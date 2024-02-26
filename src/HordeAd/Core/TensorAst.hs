{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for AST terms. Most of these instances
-- vectorize any terms starting with the build constructor.
-- The AST term instances can be used as building blocks for 'ADVal'
-- instances defined in "TensorADVal" but may also be used standalone.
module HordeAd.Core.TensorAst
  (
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector as Data.NonStrict.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           System.IO.Unsafe (unsafePerformIO)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.AstEnv
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstInline
import           HordeAd.Core.AstInterpret
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.AstVectorize
import           HordeAd.Core.Delta
import           HordeAd.Core.DualNumber
import           HordeAd.Core.HVector
import           HordeAd.Core.HVectorOps
import           HordeAd.Core.TensorADVal (unADValHVector)
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Util.ShapedList (singletonShaped)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

-- * Reverse and forward derivative stages instances

instance DerivativeStages (AstRanked FullSpan) where
  forwardPassByInterpretation
    :: (GoodScalar r, KnownNat n)
    => (HVector (AstRanked FullSpan) -> AstRanked FullSpan r n)
    -> AstEnv (ADVal (AstRanked PrimalSpan))
    -> HVector (AstRanked PrimalSpan)
    -> [AstDynamicVarName]
    -> HVector (AstRanked FullSpan)
    -> ADVal (AstRanked PrimalSpan) r n
  {-# INLINE forwardPassByInterpretation #-}
  forwardPassByInterpretation g envInit hVectorPrimal vars hVector =
    let deltaInputs = generateDeltaInputs hVectorPrimal
        varInputs = makeADInputs hVectorPrimal deltaInputs
        ast = g hVector
        env = foldr extendEnvD envInit $ zip vars $ V.toList varInputs
    in interpretAst env ast

  revArtifactFromForwardPass
    :: forall r n. (GoodScalar r, KnownNat n)
    => TensorToken (AstRanked FullSpan) -> Bool
    -> (HVector (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> HVector (AstRanked FullSpan)
        -> ADVal (AstRanked PrimalSpan) r n)
    -> VoidHVector
    -> ( AstArtifactRev (AstRanked PrimalSpan) r n
       , Dual (AstRanked PrimalSpan) r n )
  {-# INLINE revArtifactFromForwardPass #-}
  revArtifactFromForwardPass _ hasDt forwardPass parameters0 =
    let -- Bangs and the compound function to fix the numbering of variables
        -- for pretty-printing and prevent sharing the impure values/effects
        -- in tests that reset the impure counters.
        !(!varsPrimal, hVectorPrimal, vars, hVector) =
          funToAstRev parameters0 in
    let -- Evaluate completely after terms constructed, to free memory
        -- before gradientFromDelta allocates new memory and new FFI is started.
        !(D l primalBody delta) = forwardPass hVectorPrimal vars hVector
        sh = shapeAst primalBody
        domsB = V.singleton $ voidFromSh @r sh
    in fun1DToAst domsB $ \ !varsDt !astsDt -> assert (V.length astsDt == 1) $
      let mdt = if hasDt then Just $ rfromD $ astsDt V.! 0 else Nothing
          !(!astBindings, !gradient) =
            reverseDervative parameters0 primalBody mdt delta
          unGradient = dunlet l astBindings (AstMkHVector gradient)
          unPrimal = runlet l [] primalBody
      in ( ((varsDt, varsPrimal), unGradient, unPrimal, shapeToList sh)
         , delta )
           -- storing sh computed from primalBody often saves the unletAst6
           -- execution; we could store the whole primalBody, as we do in calls
           -- to reverseDervative, but we can potentially free it earlier this
           -- way (as soon as sh is forced or determined to be unneeded)

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varsDt, vars), gradient, primal, sh) parameters mdt =
    let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe (rreplicate0N (listShapeToShape sh) 1) mdt
        dts = V.singleton $ DynamicRanked dt
        envDt = extendEnvHVector varsDt dts env
        gradientHVector = interpretAstHVector envDt gradient
        primalTensor = interpretAstPrimal env primal
    in (gradientHVector, primalTensor)

  fwdArtifactFromForwardPass
    :: forall r n. (GoodScalar r, KnownNat n)
    => TensorToken (AstRanked FullSpan)
    -> (HVector (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> HVector (AstRanked FullSpan)
        -> ADVal (AstRanked PrimalSpan) r n)
    -> VoidHVector
    -> ( AstArtifactFwd (AstRanked PrimalSpan) r n
       , Dual (AstRanked PrimalSpan) r n )
  {-# INLINE fwdArtifactFromForwardPass #-}
  fwdArtifactFromForwardPass _ forwardPass parameters0 =
    let !(!varsPrimalDs, hVectorDs, varsPrimal, hVectorPrimal, vars, hVector) =
          funToAstFwd parameters0 in
    let !(D l primalBody delta) = forwardPass hVectorPrimal vars hVector in
    let !(!astBindings, !derivative) =
          forwardDerivative (V.length parameters0) delta hVectorDs
        unDerivative = runlet l astBindings derivative
        unPrimal = runlet l [] primalBody
    in ( ((varsPrimalDs, varsPrimal), unDerivative, unPrimal)
       , delta )

  {-# INLINE fwdEvalArtifact #-}
  fwdEvalArtifact ((varDs, vars), derivative, primal) parameters ds =
    if hVectorsMatch parameters ds then
      let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
          envDs = foldr extendEnvD env $ zip varDs $ V.toList ds
          derivativeTensor = interpretAstPrimal envDs derivative
          primalTensor = interpretAstPrimal @(Flip OR.Array) env primal
      in (derivativeTensor, primalTensor)
   else error "fwdEvalArtifact: forward derivative input and sensitivity arguments should have same shapes"

instance DerivativeStages (AstShaped FullSpan) where
  forwardPassByInterpretation
    :: (GoodScalar r, Sh.Shape sh)
    => (HVector (AstRanked FullSpan) -> AstShaped FullSpan r sh)
    -> AstEnv (ADVal (AstRanked PrimalSpan))
    -> HVector (AstRanked PrimalSpan)
    -> [AstDynamicVarName]
    -> HVector (AstRanked FullSpan)
    -> ADVal (AstShaped PrimalSpan) r sh
  {-# INLINE forwardPassByInterpretation #-}
  forwardPassByInterpretation g envInit hVectorPrimal vars hVector =
    let deltaInputs = generateDeltaInputs hVectorPrimal
        varInputs = makeADInputs hVectorPrimal deltaInputs
        ast = g hVector
        env = foldr extendEnvD envInit $ zip vars $ V.toList varInputs
    in interpretAstS env ast

  revArtifactFromForwardPass
    :: forall r sh. (GoodScalar r, Sh.Shape sh)
    => TensorToken (AstShaped FullSpan) -> Bool
    -> (HVector (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> HVector (AstRanked FullSpan)
        -> ADVal (AstShaped PrimalSpan) r sh)
    -> VoidHVector
    -> ( AstArtifactRev (AstShaped PrimalSpan) r sh
       , Dual (AstShaped PrimalSpan) r sh )
  {-# INLINE revArtifactFromForwardPass #-}
  revArtifactFromForwardPass _ hasDt forwardPass parameters0 =
    let !(!varsPrimal, hVectorPrimal, vars, hVector) =
          funToAstRev parameters0 in
    let !(D l primalBody delta) = forwardPass hVectorPrimal vars hVector
        domsB = V.singleton $ voidFromShS @r @sh
    in fun1DToAst domsB $ \ !varsDt !astsDt -> assert (V.length astsDt == 1) $
      let mdt = if hasDt then Just $ sfromD $ astsDt V.! 0 else Nothing
          !(!astBindings, !gradient) =
            reverseDervative parameters0 primalBody mdt delta
          unGradient = dunlet l astBindings (AstMkHVector gradient)
          unPrimal = sunlet l [] primalBody
      in ( ((varsDt, varsPrimal), unGradient, unPrimal, Sh.shapeT @sh)
         , delta )

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varsDt, vars), gradient, primal, _) parameters mdt =
    let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe 1 mdt
        dts = V.singleton $ DynamicShaped dt
        envDt = extendEnvHVector varsDt dts env
        gradientHVector = interpretAstHVector envDt gradient
        primalTensor = interpretAstPrimalS env primal
    in (gradientHVector, primalTensor)

  fwdArtifactFromForwardPass
    :: forall r sh. (GoodScalar r, Sh.Shape sh)
    => TensorToken (AstShaped FullSpan)
    -> (HVector (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> HVector (AstRanked FullSpan)
        -> ADVal (AstShaped PrimalSpan) r sh)
    -> VoidHVector
    -> ( AstArtifactFwd (AstShaped PrimalSpan) r sh
       , Dual (AstShaped PrimalSpan) r sh )
  {-# INLINE fwdArtifactFromForwardPass #-}
  fwdArtifactFromForwardPass _ forwardPass parameters0 =
    let !(!varsPrimalDs, hVectorDs, varsPrimal, hVectorPrimal, vars, hVector) =
          funToAstFwd parameters0 in
    let !(D l primalBody delta) = forwardPass hVectorPrimal vars hVector  in
    let !(!astBindings, !derivative) =
          forwardDerivative (V.length parameters0) delta hVectorDs
        unDerivative = sunlet l astBindings derivative
        unPrimal = sunlet l [] primalBody
    in ( ((varsPrimalDs, varsPrimal), unDerivative, unPrimal)
       , delta )

  {-# INLINE fwdEvalArtifact #-}
  fwdEvalArtifact ((varDs, vars), derivative, primal) parameters ds =
    if hVectorsMatch parameters ds then
      let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
          envDs = foldr extendEnvD env $ zip varDs $ V.toList ds
          derivativeTensor = interpretAstPrimalS envDs derivative
          primalTensor = interpretAstPrimalS @(Flip OR.Array) env primal
      in (derivativeTensor, primalTensor)
   else error "fwdEvalArtifact: forward derivative input and sensitivity arguments should have same shapes"

instance DerivativeStages (HVectorPseudoTensor (AstRanked FullSpan)) where
  forwardPassByInterpretation
    :: (HVector (AstRanked FullSpan)
        -> HVectorPseudoTensor (AstRanked FullSpan) r y)
    -> AstEnv (ADVal (AstRanked PrimalSpan))
    -> HVector (AstRanked PrimalSpan)
    -> [AstDynamicVarName]
    -> HVector (AstRanked FullSpan)
    -> ADVal (HVectorPseudoTensor (AstRanked PrimalSpan)) r y
  {-# INLINE forwardPassByInterpretation #-}
  forwardPassByInterpretation g envInit hVectorPrimal vars hVector =
    let deltaInputs = generateDeltaInputs hVectorPrimal
        varInputs = makeADInputs hVectorPrimal deltaInputs
        HVectorPseudoTensor ast = g hVector
        env = foldr extendEnvD envInit $ zip vars $ V.toList varInputs
        (ll, as, as') = unADValHVector $ interpretAstHVector env ast
    in dDnotShared (flattenADShare $ V.toList ll)
                   (HVectorPseudoTensor $ dmkHVector as)
                   (HVectorPseudoTensor $ HToH as')

  revArtifactFromForwardPass
    :: (GoodScalar r, HasSingletonDict y)
    => TensorToken (HVectorPseudoTensor (AstRanked FullSpan)) -> Bool
    -> (HVector (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> HVector (AstRanked FullSpan)
        -> ADVal (HVectorPseudoTensor (AstRanked PrimalSpan)) r y)
    -> VoidHVector
    -> ( AstArtifactRev (HVectorPseudoTensor (AstRanked PrimalSpan)) r y
       , Dual (HVectorPseudoTensor (AstRanked PrimalSpan)) r y )
  {-# INLINE revArtifactFromForwardPass #-}
  revArtifactFromForwardPass _ hasDt forwardPass parameters0 =
    let !(!varsPrimal, hVectorPrimal, vars, hVector) =
          funToAstRev parameters0 in  -- varDtId replace by many variables
    let !(D l (HVectorPseudoTensor primalBody) delta) =
          forwardPass hVectorPrimal vars hVector
        domsB = shapeAstHVector primalBody
    in fun1DToAst domsB $ \ !varsDt !astsDt ->
      let mdt = if hasDt
                then Just $ HVectorPseudoTensor $ AstMkHVector astsDt
                else Nothing
          !(!astBindings, !gradient) =
            reverseDervative
              parameters0 (HVectorPseudoTensor primalBody) mdt delta
          unGradient = dunlet l astBindings (AstMkHVector gradient)
          unPrimal = dunlet @(AstRanked PrimalSpan) l [] primalBody
      in ( ( (varsDt, varsPrimal), unGradient, HVectorPseudoTensor unPrimal
           , undefined )
         , delta )

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varsDt, vars), gradient, primal, _sh) parameters mdt =
    let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
        domsB = voidFromVars varsDt
        dt1 = mapHVectorShaped (const 1) $ V.map dynamicFromVoid domsB
        dts = maybe dt1 unHVectorPseudoTensor mdt
        envDt = extendEnvHVector varsDt dts env
        gradientHVector = interpretAstHVector envDt gradient
        primalTensor = interpretAstHVector env $ unHVectorPseudoTensor primal
    in (gradientHVector, HVectorPseudoTensor primalTensor)

  fwdArtifactFromForwardPass
    :: (GoodScalar r, HasSingletonDict y)
    => TensorToken (HVectorPseudoTensor (AstRanked FullSpan))
    -> (HVector (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> HVector (AstRanked FullSpan)
        -> ADVal (HVectorPseudoTensor (AstRanked PrimalSpan)) r y)
    -> VoidHVector
    -> ( AstArtifactFwd (HVectorPseudoTensor (AstRanked PrimalSpan)) r y
       , Dual (HVectorPseudoTensor (AstRanked PrimalSpan)) r y )
  {-# INLINE fwdArtifactFromForwardPass #-}
  fwdArtifactFromForwardPass _ forwardPass parameters0 =
    let !(!varsPrimalDs, hVectorDs, varsPrimal, hVectorPrimal, vars, hVector) =
          funToAstFwd parameters0 in
    let !(D l (HVectorPseudoTensor primalBody) delta) =
          forwardPass hVectorPrimal vars hVector in
    let !(!astBindings, !(HVectorPseudoTensor derivative)) =
          forwardDerivative (V.length parameters0) delta hVectorDs
        unDerivative = HVectorPseudoTensor $ dunlet l astBindings derivative
        unPrimal = HVectorPseudoTensor
                   $ dunlet @(AstRanked PrimalSpan) l [] primalBody
    in ( ((varsPrimalDs, varsPrimal), unDerivative, unPrimal)
       , delta )

  {-# INLINE fwdEvalArtifact #-}
  fwdEvalArtifact ((varDs, vars), derivative, primal) parameters ds =
    if hVectorsMatch parameters ds then
      let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
          envDs = foldr extendEnvD env $ zip varDs $ V.toList ds
          derivativeTensor =
            interpretAstHVector envDs $ unHVectorPseudoTensor derivative
          primalTensor = interpretAstHVector env $ unHVectorPseudoTensor primal
      in ( HVectorPseudoTensor derivativeTensor
         , HVectorPseudoTensor primalTensor )
   else error "fwdEvalArtifact: forward derivative input and sensitivity arguments should have same shapes"

-- * Unlawful boolean instances of ranked AST; they are lawful modulo evaluation

type instance SimpleBoolOf (AstRanked s) = AstBool

instance AstSpan s => EqF (AstRanked s) where
  v ==. u = (emptyADShare, AstRel EqOp (astSpanPrimal v) (astSpanPrimal u))
  v /=. u = (emptyADShare, AstRel NeqOp (astSpanPrimal v) (astSpanPrimal u))

instance AstSpan s => OrdF (AstRanked s) where
  AstConst u <. AstConst v = (emptyADShare, AstBoolConst $ u < v)
    -- common in indexing
  v <. u = (emptyADShare, AstRel LsOp (astSpanPrimal v) (astSpanPrimal u))
  AstConst u <=. AstConst v = (emptyADShare, AstBoolConst $ u <= v)
    -- common in indexing
  v <=. u = (emptyADShare, AstRel LeqOp (astSpanPrimal v) (astSpanPrimal u))
  AstConst u >. AstConst v = (emptyADShare, AstBoolConst $ u > v)
    -- common in indexing
  v >. u = (emptyADShare, AstRel GtOp (astSpanPrimal v) (astSpanPrimal u))
  AstConst u >=. AstConst v = (emptyADShare, AstBoolConst $ u >= v)
    -- common in indexing
  v >=. u = (emptyADShare, AstRel GeqOp (astSpanPrimal v) (astSpanPrimal u))

instance IfF (AstRanked s) where
  ifF (_, b) = astCond b


-- * Unlawful boolean instances of shaped AST; they are lawful modulo evaluation

type instance SimpleBoolOf (AstShaped s) = AstBool

instance AstSpan s => EqF (AstShaped s) where
  v ==. u = (emptyADShare, AstRelS EqOp (astSpanPrimalS v) (astSpanPrimalS u))
  v /=. u = (emptyADShare, AstRelS NeqOp (astSpanPrimalS v) (astSpanPrimalS u))

instance AstSpan s => OrdF (AstShaped s) where
  AstConstS u <. AstConstS v = (emptyADShare, AstBoolConst $ u < v)
    -- common in indexing
  v <. u = (emptyADShare, AstRelS LsOp (astSpanPrimalS v) (astSpanPrimalS u))
  AstConstS u <=. AstConstS v = (emptyADShare, AstBoolConst $ u <= v)
    -- common in indexing
  v <=. u = (emptyADShare, AstRelS LeqOp (astSpanPrimalS v) (astSpanPrimalS u))
  AstConstS u >. AstConstS v = (emptyADShare, AstBoolConst $ u > v)
    -- common in indexing
  v >. u = (emptyADShare, AstRelS GtOp (astSpanPrimalS v) (astSpanPrimalS u))
  AstConstS u >=. AstConstS v = (emptyADShare, AstBoolConst $ u >= v)
    -- common in indexing
  v >=. u = (emptyADShare, AstRelS GeqOp (astSpanPrimalS v) (astSpanPrimalS u))

instance IfF (AstShaped s) where
  ifF (_, b) = astCondS b


-- * Ranked tensor AST instances

instance AstSpan s => RankedTensor (AstRanked s) where
  rlet = astLetFun

  rshape = shapeAst
  rminIndex = fromPrimal . AstMinIndex . astSpanPrimal
  rmaxIndex = fromPrimal . AstMaxIndex . astSpanPrimal
  rfloor = fromPrimal . AstFloor . astSpanPrimal

  riota = fromPrimal AstIota
  rindex = AstIndex
  rsum = astSum
  rscatter sh t f = astScatter sh t (funToAstIndex f)  -- introduces new vars

  rfromList = AstFromList
  rfromVector = AstFromVector
  runravelToList :: forall r n. (GoodScalar r, KnownNat n)
                 => AstRanked s r (1 + n) -> [AstRanked s r n]
  runravelToList t =
    let f :: Int -> AstRanked s r n
        f i = AstIndex t (singletonIndex $ fromIntegral i)
    in map f [0 .. rlength t - 1]
  rreplicate = AstReplicate
  rappend = AstAppend
  rslice = AstSlice
  rreverse = AstReverse
  rtranspose = astTranspose
  rreshape = astReshape
  rbuild1 = astBuild1Vectorize
  rgather sh t f = AstGather sh t (funToAstIndex f)  -- introduces new vars
  rcast = AstCast
  rfromIntegral = fromPrimal . AstFromIntegral . astSpanPrimal
  rconst = fromPrimal . AstConst
  rletHVectorIn = astLetHVectorInFun
  rletHFunIn = astLetHFunInFun
  rfromS = astRFromS

  rletWrap l u | Just Refl <- sameAstSpan @s @PrimalSpan =
    if nullADShare l then u else AstLetADShare l u
  rletWrap _ _ = error "rletWrap: wrong span"
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  rletUnwrap u = case u of
    AstLetADShare l t -> (l, t)
    AstConstant (AstLetADShare l t) -> (l, AstConstant t)
    _ -> (emptyADShare, u)
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  runlet =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> unletAst6
      _ -> error "runlet: used not at PrimalSpan"
  rregister = astRegisterFun
  rsharePrimal =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> astRegisterADShare
      _ -> error "rsharePrimal: used not at PrimalSpan"

  rconstant = fromPrimal
  rprimalPart = astSpanPrimal
  rdualPart = astSpanDual
  rD = astSpanD
  rScale s t = astDualPart $ AstConstant s * AstD (rzero (rshape s)) t

instance (GoodScalar r, KnownNat n, RankedTensor (AstRanked s))
         => AdaptableHVector (AstRanked s) (AstRanked s r n) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstRanked s) (AstRanked s Double n) #-}
  toHVector = undefined
  fromHVector _aInit params = fromHVectorR @r @n params

instance DualNumberValue (AstRanked PrimalSpan r n) where
  type DValue (AstRanked PrimalSpan r n) = Flip OR.Array r n
  fromDValue t = fromPrimal $ AstConst $ runFlip t

instance TermValue (AstRanked FullSpan r n) where
  type Value (AstRanked FullSpan r n) = Flip OR.Array r n
  fromValue t = fromPrimal $ AstConst $ runFlip t

astLetHVectorInFun
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => AstHVector s -> (HVector (AstRanked s) -> AstRanked s r n)
  -> AstRanked s r n
{-# INLINE astLetHVectorInFun #-}
astLetHVectorInFun a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorIn vars a (f asts)

astLetHFunInFun
  :: AstHFun -> (AstHFun -> AstRanked s r n)
  -> AstRanked s r n
{-# INLINE astLetHFunInFun #-}
astLetHFunInFun a f =
  let shss = domainShapesAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunIn var a (f ast)

astSpanPrimal :: forall s r n. (KnownNat n, GoodScalar r, AstSpan s)
              => AstRanked s r n -> AstRanked PrimalSpan r n
astSpanPrimal t | Just Refl <- sameAstSpan @s @PrimalSpan = t
astSpanPrimal _ | Just Refl <- sameAstSpan @s @DualSpan =
  error "astSpanPrimal: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimal t | Just Refl <- sameAstSpan @s @FullSpan = astPrimalPart t
astSpanPrimal _ = error "a spuriuos case for pattern match coverage"

astSpanDual :: forall s r n. (KnownNat n, GoodScalar r, AstSpan s)
            => AstRanked s r n -> AstRanked DualSpan r n
astSpanDual t | Just Refl <- sameAstSpan @s @PrimalSpan =
  AstDualPart $ AstConstant t  -- this is nil; likely to happen
astSpanDual t | Just Refl <- sameAstSpan @s @DualSpan = t
astSpanDual t | Just Refl <- sameAstSpan @s @FullSpan = astDualPart t
astSpanDual _ = error "a spuriuos case for pattern match coverage"

astSpanD :: forall s r n. AstSpan s
         => AstRanked PrimalSpan r n -> AstRanked DualSpan r n
         -> AstRanked s r n
astSpanD u _ | Just Refl <- sameAstSpan @s @PrimalSpan = u
astSpanD _ u' | Just Refl <- sameAstSpan @s @DualSpan = u'
astSpanD u u' | Just Refl <- sameAstSpan @s @FullSpan = AstD u u'
astSpanD _ _ = error "a spuriuos case for pattern match coverage"

astLetFun :: (KnownNat n, KnownNat m, GoodScalar r, GoodScalar r2, AstSpan s)
          => AstRanked s r n -> (AstRanked s r n -> AstRanked s r2 m)
          -> AstRanked s r2 m
astLetFun a f | astIsSmall True a = f a
astLetFun a f =
  let sh = shapeAst a
      (var, ast) = funToAstR sh f
  in astLet var a ast  -- safe, because subsitution ruled out above

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize :: (KnownNat n, GoodScalar r, AstSpan s)
                   => Int -> (AstInt -> AstRanked s r n)
                   -> AstRanked s r (1 + n)
astBuild1Vectorize k f = build1Vectorize k $ funToAstI f


-- * Shaped tensor AST instances

instance AstSpan s => ShapedTensor (AstShaped s) where
  slet = astLetFunS

  sminIndex = fromPrimalS . AstMinIndexS . astSpanPrimalS
  smaxIndex = fromPrimalS . AstMaxIndexS . astSpanPrimalS
  sfloor = fromPrimalS . AstFloorS . astSpanPrimalS

  siota = fromPrimalS AstIotaS
  sindex = AstIndexS
  ssum = astSumS
  sscatter t f = astScatterS t (funToAstIndexS f)  -- introduces new vars

  sfromList = AstFromListS
  sfromVector = AstFromVectorS
  sunravelToList :: forall r n sh. (GoodScalar r, KnownNat n, Sh.Shape sh)
                 => AstShaped s r (n ': sh) -> [AstShaped s r sh]
  sunravelToList t =
    let f :: Int -> AstShaped s r sh
        f i = AstIndexS t (singletonShaped $ fromIntegral i)
    in map f [0 .. slength t - 1]
  sreplicate = AstReplicateS
  sappend = AstAppendS
  sslice (_ :: Proxy i) Proxy = AstSliceS @i
  sreverse = AstReverseS
  stranspose (_ :: Proxy perm) = astTransposeS @perm
  sreshape = astReshapeS
  sbuild1 = astBuild1VectorizeS
  sgather t f = AstGatherS t (funToAstIndexS f)  -- introduces new vars
  scast = AstCastS
  sfromIntegral = fromPrimalS . AstFromIntegralS . astSpanPrimalS
  sconst = fromPrimalS . AstConstS
  sletHVectorIn = astLetHVectorInFunS
  sletHFunIn = astLetHFunInFunS
  sfromR = astSFromR

  sletWrap l u | Just Refl <- sameAstSpan @s @PrimalSpan =
    if nullADShare l then u else AstLetADShareS l u
  sletWrap _ _ = error "sletWrap: wrong span"
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  sletUnwrap u = case u of
    AstLetADShareS l t -> (l, t)
    AstConstantS (AstLetADShareS l t) -> (l, AstConstantS t)
    _ -> (emptyADShare, u)
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  sunlet =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> unletAst6S
      _ -> error "sunlet: used not at PrimalSpan"
  sregister = astRegisterFunS
  ssharePrimal =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> astRegisterADShareS
      _ -> error "ssharePrimal: used not at PrimalSpan"

  sconstant = fromPrimalS
  sprimalPart = astSpanPrimalS
  sdualPart = astSpanDualS
  sD = astSpanDS
  sScale s t = astDualPartS $ AstConstantS s * AstDS 0 t

instance (GoodScalar r, Sh.Shape sh, ShapedTensor (AstShaped s))
         => AdaptableHVector (AstRanked s) (AstShaped s r sh) where
  toHVector = undefined
  fromHVector _aInit params = fromHVectorS @r @sh params

instance DualNumberValue (AstShaped PrimalSpan r sh) where
  type DValue (AstShaped PrimalSpan r sh) = Flip OS.Array r sh
  fromDValue t = fromPrimalS $ AstConstS $ runFlip t

instance TermValue (AstShaped FullSpan r sh) where
  type Value (AstShaped FullSpan r sh) = Flip OS.Array r sh
  fromValue t = fromPrimalS $ AstConstS $ runFlip t

astLetHVectorInFunS
  :: forall sh s r. (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstHVector s -> (HVector (AstRanked s) -> AstShaped s r sh)
  -> AstShaped s r sh
{-# INLINE astLetHVectorInFunS #-}
astLetHVectorInFunS a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorInS vars a (f asts)

astLetHFunInFunS
  :: AstHFun -> (AstHFun -> AstShaped s r sh)
  -> AstShaped s r sh
{-# INLINE astLetHFunInFunS #-}
astLetHFunInFunS a f =
  let shss = domainShapesAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunInS var a (f ast)

astSpanPrimalS :: forall s r sh. (Sh.Shape sh, GoodScalar r, AstSpan s)
               => AstShaped s r sh -> AstShaped PrimalSpan r sh
astSpanPrimalS t | Just Refl <- sameAstSpan @s @PrimalSpan = t
astSpanPrimalS _ | Just Refl <- sameAstSpan @s @DualSpan =
  error "astSpanPrimalS: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimalS t | Just Refl <- sameAstSpan @s @FullSpan = astPrimalPartS t
astSpanPrimalS _ = error "a spuriuos case for pattern match coverage"

astSpanDualS :: forall s r sh. (Sh.Shape sh, GoodScalar r, AstSpan s)
             => AstShaped s r sh -> AstShaped DualSpan r sh
astSpanDualS t | Just Refl <- sameAstSpan @s @PrimalSpan =
  AstDualPartS $ AstConstantS t  -- this is nil; likely to happen
astSpanDualS t | Just Refl <- sameAstSpan @s @DualSpan = t
astSpanDualS t | Just Refl <- sameAstSpan @s @FullSpan = astDualPartS t
astSpanDualS _ = error "a spuriuos case for pattern match coverage"

astSpanDS :: forall s r sh. AstSpan s
          => AstShaped PrimalSpan r sh -> AstShaped DualSpan r sh
          -> AstShaped s r sh
astSpanDS u _ | Just Refl <- sameAstSpan @s @PrimalSpan = u
astSpanDS _ u' | Just Refl <- sameAstSpan @s @DualSpan = u'
astSpanDS u u' | Just Refl <- sameAstSpan @s @FullSpan = AstDS u u'
astSpanDS _ _ = error "a spuriuos case for pattern match coverage"

astLetFunS :: ( Sh.Shape sh, Sh.Shape sh2, GoodScalar r, GoodScalar r2
              , AstSpan s )
          => AstShaped s r sh -> (AstShaped s r sh -> AstShaped s r2 sh2)
          -> AstShaped s r2 sh2
astLetFunS a f | astIsSmallS True a = f a
astLetFunS a f =
  let (var, ast) = funToAstS f
  in astLetS var a ast  -- safe, because subsitution ruled out above

astBuild1VectorizeS :: (KnownNat n, Sh.Shape sh, GoodScalar r, AstSpan s)
                    => (IntSh (AstShaped PrimalSpan) n -> AstShaped s r sh)
                    -> AstShaped s r (n ': sh)
astBuild1VectorizeS f =
  build1VectorizeS $ funToAstI (f . ShapedList.shapedNat)


-- * HVectorTensor instance

instance forall s. AstSpan s => HVectorTensor (AstRanked s) (AstShaped s) where
  dshape = shapeAstHVector
  dmkHVector = AstMkHVector
  dunHVector hVectorOf =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: ShapeInt n) ->
              DynamicRanked @r @n
              $ rletHVectorIn @(AstRanked s) hVectorOf (rfromD . (V.! i))
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh
            $ sletHVectorIn @(AstShaped s) hVectorOf (sfromD . (V.! i))
    in V.imap f $ shapeAstHVector hVectorOf
  dlambda shss f = AstLambda
                   $ fun1LToAst shss $ \ !vvars !ll -> (vvars, unHFun f ll)
  dHApply = astHApply
  dletHVectorInHVector = astLetHVectorInHVectorFun
  dletHFunInHVector = astLetHFunInHVectorFun
  rletInHVector = astLetInHVectorFun
  sletInHVector = astLetInHVectorFunS
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  dunlet =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> unletAstHVector6
      _ -> error "dunlet: used not at PrimalSpan"
  -- These and many similar bangs are necessary to ensure variable IDs
  -- are generated in the expected order, resulting in nesting of lets
  -- occuring in the correct order and so no scoping errors.
  dsharePrimal !r !l | Just Refl <- sameAstSpan @s @PrimalSpan =
    fun1DToAst (shapeAstHVector r) $ \ !vars !asts -> case vars of
      [] -> (l, V.empty)
      !var : _ ->  -- vars are fresh, so var uniquely represent vars
        ( insertADShare (dynamicVarNameToAstVarId var)
                        (AstBindingsHVector vars r)
                        l
        , asts )
  dsharePrimal _ _ = error "dsharePrimal: wrong span"
  dregister !r !l =
    fun1DToAst (shapeAstHVector r) $ \ !vars !asts -> case vars of
      [] -> (l, V.empty)
      !var : _ ->  -- vars are fresh, so var uniquely represent vars
        ((dynamicVarNameToAstVarId var, AstBindingsHVector vars r) : l, asts)
  dbuild1 = astBuildHVector1Vectorize
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (AstRanked s)
       -> AstHVector s
  rrev f parameters0 =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new @parmeters@, which is much better than computing anew.
    let !(!((!_varsDt, !vars), !gradient, !_primal, _sh), _delta) =
          revProduceArtifact TensorToken False (f @(AstRanked FullSpan))
                             EM.empty parameters0
    in \parameters -> assert (voidHVectorMatches parameters0 parameters) $
      let env = extendEnvHVector @(AstRanked s) vars parameters EM.empty
      in interpretAstHVector env gradient
        -- this interpretation both substitutes parameters for the variables and
        -- reinterprets @PrimalSpan@ terms in @s@ terms;
        -- we could shortcut when @s@ is @PrimalSpan@ and @parameters@
        -- are the same variables, but it's a very special case;
        -- a faster implementation would be via AstHApply, but this tests
        -- a slightly different code path, so let's keep it
  drevDt :: VoidHVector
         -> HFun
         -> AstHFun
  drevDt shs f =
    let g :: HVector (AstRanked FullSpan)
          -> HVectorPseudoTensor (AstRanked FullSpan) Float '()
        g !hv = HVectorPseudoTensor $ unHFun f [hv]
        (((varsDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken True g EM.empty shs
     in AstLambda ([varsDt, vars], gradient)
  dfwd :: VoidHVector
       -> HFun
       -> AstHFun
  dfwd shs f =
    let g :: HVector (AstRanked FullSpan)
          -> HVectorPseudoTensor (AstRanked FullSpan) Float '()
        g !hv = HVectorPseudoTensor $ unHFun f [hv]
        (((varsDt, vars), derivative, _primal), _delta) =
          fwdProduceArtifact TensorToken g EM.empty shs
     in AstLambda ([varsDt, vars], unHVectorPseudoTensor derivative)
  dmapAccumRDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> AstHFun
    -> AstHFun
    -> AstHFun
    -> HVector (AstRanked s)
    -> HVector (AstRanked s)
    -> AstHVector s
  dmapAccumRDer !k !accShs !bShs !eShs f df rf acc0 es =
    assert (voidHVectorMatches (replicate1VoidHVector k eShs) es
            && voidHVectorMatches accShs acc0) $
    AstMapAccumRDer k accShs bShs eShs f df rf acc0 es
  dmapAccumLDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> AstHFun
    -> AstHFun
    -> AstHFun
    -> HVector (AstRanked s)
    -> HVector (AstRanked s)
    -> AstHVector s
  dmapAccumLDer !k !accShs !bShs !eShs f df rf acc0 es =
    assert (voidHVectorMatches (replicate1VoidHVector k eShs) es
            && voidHVectorMatches accShs acc0) $
    AstMapAccumLDer k accShs bShs eShs f df rf acc0 es

instance AdaptableHVector (AstRanked s) (AstHVector s) where
  toHVector = undefined
  fromHVector aInit params =
    let (portion, rest) = V.splitAt (V.length $ shapeAstHVector aInit) params
    in Just (AstMkHVector portion, rest)

instance DualNumberValue (AstHVector PrimalSpan) where
  type DValue (AstHVector PrimalSpan) = HVector (Flip OR.Array)
  fromDValue t = AstMkHVector $ V.map fromDValue t

-- HVector causes overlap and violation of injectivity,
-- hence Data.NonStrict.Vector. Injectivity is crucial to limit the number
-- of type applications the library user has to supply.
instance TermValue (AstHVector FullSpan) where
  type Value (AstHVector FullSpan) =
    Data.NonStrict.Vector.Vector (DynamicTensor (Flip OR.Array))
  fromValue t = AstMkHVector $ V.convert $ V.map fromValue t

instance TermValue (HVectorPseudoTensor (AstRanked FullSpan) r y) where
  type Value (HVectorPseudoTensor (AstRanked FullSpan) r y) =
    HVectorPseudoTensor (Flip OR.Array) r y
  fromValue (HVectorPseudoTensor t) =
    HVectorPseudoTensor $ AstMkHVector $ V.convert $ V.map fromValue t

astLetHVectorInHVectorFun
  :: AstSpan s
  => AstHVector s -> (HVector (AstRanked s) -> AstHVector s)
  -> AstHVector s
{-# INLINE astLetHVectorInHVectorFun #-}
astLetHVectorInHVectorFun a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorInHVector vars a (f asts)

astLetHFunInHVectorFun
  :: AstHFun -> (AstHFun -> AstHVector s)
  -> AstHVector s
{-# INLINE astLetHFunInHVectorFun #-}
astLetHFunInHVectorFun a f =
  let shss = domainShapesAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunInHVector var a (f ast)

astLetInHVectorFun :: (KnownNat n, GoodScalar r, AstSpan s)
                   => AstRanked s r n -> (AstRanked s r n -> AstHVector s)
                   -> AstHVector s
{-# NOINLINE astLetInHVectorFun #-}
astLetInHVectorFun a f | astIsSmall True a = f a
astLetInHVectorFun a f = unsafePerformIO $ do  -- the id causes trouble
  let sh = shapeAst a
  (!var, _, !ast) <- funToAstIOR sh id
  return $! astLetInHVector var a (f ast)
              -- safe because subsitution ruled out above

astLetInHVectorFunS :: (Sh.Shape sh, GoodScalar r, AstSpan s)
                    => AstShaped s r sh -> (AstShaped s r sh -> AstHVector s)
                    -> AstHVector s
{-# NOINLINE astLetInHVectorFunS #-}
astLetInHVectorFunS a f | astIsSmallS True a = f a
astLetInHVectorFunS a f = unsafePerformIO $ do  -- the id causes trouble
  (!var, _, !ast) <- funToAstIOS id
  return $! astLetInHVectorS var a (f ast)
              -- safe because subsitution ruled out above

astBuildHVector1Vectorize
  :: AstSpan s
  => SNat k -> (AstInt -> AstHVector s) -> AstHVector s
astBuildHVector1Vectorize k f = build1VectorizeHVector k $ funToAstI f

-- This specialization is not possible where gradientFromDeltaR is defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDeltaR
  :: KnownNat y
  => VoidHVector -> AstRanked PrimalSpan Double y
  -> Maybe (AstRanked PrimalSpan Double y)
  -> DeltaR (AstRanked PrimalSpan) Double y
  -> ( AstBindingsD (AstRanked PrimalSpan)
     , HVector (AstRanked PrimalSpan) ) #-}
{-# SPECIALIZE gradientFromDeltaS
  :: Sh.Shape y
  => VoidHVector -> Maybe (AstShaped PrimalSpan Double y)
  -> DeltaS (AstShaped PrimalSpan) Double y
  -> ( AstBindingsD (AstRanked PrimalSpan)
     , HVector (AstRanked PrimalSpan) ) #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState (AstRanked PrimalSpan) -> EvalState (AstRanked PrimalSpan) #-}


-- * The auxiliary AstNoVectorize and AstNoSimplify instances, for tests

type instance SimpleBoolOf (AstNoVectorize s) = AstBool

deriving instance IfF (AstNoVectorize s)
deriving instance AstSpan s => EqF (AstNoVectorize s)
deriving instance AstSpan s => OrdF (AstNoVectorize s)
deriving instance Eq (AstNoVectorize s r n)
deriving instance Ord (AstNoVectorize s r n)
deriving instance Num (AstRanked s r n) => Num (AstNoVectorize s r n)
deriving instance (Real (AstRanked s r n))
                   => Real (AstNoVectorize s r n)
deriving instance Enum (AstRanked s r n) => Enum (AstNoVectorize s r n)
deriving instance (Integral (AstRanked s r n))
                  => Integral (AstNoVectorize s r n)
deriving instance Fractional (AstRanked s r n)
                  => Fractional (AstNoVectorize s r n)
deriving instance Floating (AstRanked s r n)
                  => Floating (AstNoVectorize s r n)
deriving instance (RealFrac (AstRanked s r n))
                  => RealFrac (AstNoVectorize s r n)
deriving instance (RealFloat (AstRanked s r n))
                  => RealFloat (AstNoVectorize s r n)

type instance SimpleBoolOf (AstNoVectorizeS s) = AstBool

deriving instance IfF (AstNoVectorizeS s)
deriving instance AstSpan s => EqF (AstNoVectorizeS s)
deriving instance AstSpan s => OrdF (AstNoVectorizeS s)
deriving instance Eq ((AstNoVectorizeS s) r sh)
deriving instance Ord ((AstNoVectorizeS s) r sh)
deriving instance Num (AstShaped s r sh) => Num (AstNoVectorizeS s r sh)
deriving instance (Real (AstShaped s r sh))
                   => Real (AstNoVectorizeS s r sh)
deriving instance Enum (AstShaped s r sh) => Enum (AstNoVectorizeS s r sh)
deriving instance (Integral (AstShaped s r sh))
                  => Integral (AstNoVectorizeS s r sh)
deriving instance Fractional (AstShaped s r sh)
                  => Fractional (AstNoVectorizeS s r sh)
deriving instance Floating (AstShaped s r sh)
                  => Floating (AstNoVectorizeS s r sh)
deriving instance (RealFrac (AstShaped s r sh))
                  => RealFrac (AstNoVectorizeS s r sh)
deriving instance (RealFloat (AstShaped s r sh))
                  => RealFloat (AstNoVectorizeS s r sh)

type instance SimpleBoolOf (AstNoSimplify s) = AstBool

deriving instance IfF (AstNoSimplify s)
deriving instance AstSpan s => EqF (AstNoSimplify s)
deriving instance AstSpan s => OrdF (AstNoSimplify s)
deriving instance Eq (AstNoSimplify s r n)
deriving instance Ord (AstNoSimplify s r n)
deriving instance Num (AstRanked s r n) => Num (AstNoSimplify s r n)
deriving instance (Real (AstRanked s r n))
                  => Real (AstNoSimplify s r n)
deriving instance Enum (AstRanked s r n) => Enum (AstNoSimplify s r n)
deriving instance (Integral (AstRanked s r n))
                  => Integral (AstNoSimplify s r n)
deriving instance Fractional (AstRanked s r n)
                  => Fractional (AstNoSimplify s r n)
deriving instance Floating (AstRanked s r n)
                  => Floating (AstNoSimplify s r n)
deriving instance (RealFrac (AstRanked s r n))
                  => RealFrac (AstNoSimplify s r n)
deriving instance (RealFloat (AstRanked s r n))
                  => RealFloat (AstNoSimplify s r n)

type instance SimpleBoolOf (AstNoSimplifyS s) = AstBool

deriving instance IfF (AstNoSimplifyS s)
deriving instance AstSpan s => EqF (AstNoSimplifyS s)
deriving instance AstSpan s => OrdF (AstNoSimplifyS s)
deriving instance Eq (AstNoSimplifyS s r sh)
deriving instance Ord (AstNoSimplifyS s r sh)
deriving instance Num (AstShaped s r sh) => Num (AstNoSimplifyS s r sh)
deriving instance (Real (AstShaped s r sh))
                  => Real (AstNoSimplifyS s r sh)
deriving instance Enum (AstShaped s r sh) => Enum (AstNoSimplifyS s r sh)
deriving instance (Integral (AstShaped s r sh))
                  => Integral (AstNoSimplifyS s r sh)
deriving instance Fractional (AstShaped s r sh)
                  => Fractional (AstNoSimplifyS s r sh)
deriving instance Floating (AstShaped s r sh)
                  => Floating (AstNoSimplifyS s r sh)
deriving instance (RealFrac (AstShaped s r sh))
                  => RealFrac (AstNoSimplifyS s r sh)
deriving instance (RealFloat (AstShaped s r sh))
                  => RealFloat (AstNoSimplifyS s r sh)

instance AstSpan s => RankedTensor (AstNoVectorize s) where
  rlet a f =
    AstNoVectorize
    $ astLetFun (unAstNoVectorize a) (unAstNoVectorize . f . AstNoVectorize)
  rshape = shapeAst . unAstNoVectorize
  rminIndex = AstNoVectorize . fromPrimal . AstMinIndex
              . astSpanPrimal . unAstNoVectorize
  rmaxIndex = AstNoVectorize . fromPrimal . AstMaxIndex
              . astSpanPrimal . unAstNoVectorize
  rfloor = AstNoVectorize . fromPrimal . AstFloor
           . astSpanPrimal . unAstNoVectorize
  riota = AstNoVectorize . fromPrimal $ AstIota
  rindex v ix = AstNoVectorize $ AstIndex (unAstNoVectorize v) ix
  rsum = AstNoVectorize . astSum . unAstNoVectorize
  rscatter sh t f = AstNoVectorize $ astScatter sh (unAstNoVectorize t)
                    $ funToAstIndex f  -- this introduces new variable names
  rfromList = AstNoVectorize . AstFromList . map unAstNoVectorize
  rfromVector = AstNoVectorize . AstFromVector . V.map unAstNoVectorize
  runravelToList :: forall r n. (GoodScalar r, KnownNat n)
                 => AstNoVectorize s r (1 + n) -> [AstNoVectorize s r n]
  runravelToList (AstNoVectorize t) =
    let f :: Int -> AstNoVectorize s r n
        f i = AstNoVectorize $ AstIndex t (singletonIndex $ fromIntegral i)
    in map f [0 .. rlength t - 1]
  rreplicate k = AstNoVectorize . AstReplicate k . unAstNoVectorize
  rappend u v =
    AstNoVectorize $ AstAppend (unAstNoVectorize u) (unAstNoVectorize v)
  rslice i n = AstNoVectorize . AstSlice i n . unAstNoVectorize
  rreverse = AstNoVectorize . AstReverse . unAstNoVectorize
  rtranspose perm = AstNoVectorize . astTranspose perm . unAstNoVectorize
  rreshape sh = AstNoVectorize . astReshape sh . unAstNoVectorize
  rbuild1 k f = AstNoVectorize $ AstBuild1 k
                $ funToAstI  -- this introduces new variable names
                $ unAstNoVectorize . f
  rgather sh t f = AstNoVectorize $ AstGather sh (unAstNoVectorize t)
                   $ funToAstIndex f  -- this introduces new variable names
  rcast = AstNoVectorize . AstCast . unAstNoVectorize
  rfromIntegral = AstNoVectorize . fromPrimal . AstFromIntegral
                  . astSpanPrimal . unAstNoVectorize
  rconst = AstNoVectorize . fromPrimal . AstConst
  rletHVectorIn a f =
    AstNoVectorize
    $ astLetHVectorInFun a (unAstNoVectorize . f . noVectorizeHVector)
  rletHFunIn a f = AstNoVectorize $ rletHFunIn a (unAstNoVectorize . f)
  rfromS = AstNoVectorize . rfromS @(AstRanked s) . unAstNoVectorizeS

  rconstant = AstNoVectorize . fromPrimal
  rprimalPart = astSpanPrimal . unAstNoVectorize
  rdualPart = astSpanDual . unAstNoVectorize
  rD u u' = AstNoVectorize $ astSpanD u u'
  rScale s t = astDualPart $ AstConstant s * AstD (rzero (rshape s)) t

instance AstSpan s => ShapedTensor (AstNoVectorizeS s) where
  slet a f =
    AstNoVectorizeS
    $ astLetFunS (unAstNoVectorizeS a) (unAstNoVectorizeS . f . AstNoVectorizeS)
  sminIndex = AstNoVectorizeS . fromPrimalS . AstMinIndexS
              . astSpanPrimalS . unAstNoVectorizeS
  smaxIndex = AstNoVectorizeS . fromPrimalS . AstMaxIndexS
              . astSpanPrimalS . unAstNoVectorizeS
  sfloor = AstNoVectorizeS . fromPrimalS . AstFloorS
           . astSpanPrimalS . unAstNoVectorizeS
  siota = AstNoVectorizeS . fromPrimalS $ AstIotaS
  sindex v ix = AstNoVectorizeS $ AstIndexS (unAstNoVectorizeS v) ix
  ssum = AstNoVectorizeS . astSumS . unAstNoVectorizeS
  sscatter t f = AstNoVectorizeS $ astScatterS (unAstNoVectorizeS t)
                 $ funToAstIndexS f  -- this introduces new variable names
  sfromList = AstNoVectorizeS . AstFromListS . map unAstNoVectorizeS
  sfromVector = AstNoVectorizeS . AstFromVectorS . V.map unAstNoVectorizeS
  sunravelToList :: forall r n sh. (GoodScalar r, KnownNat n, Sh.Shape sh)
                 => AstNoVectorizeS s r (n ': sh) -> [AstNoVectorizeS s r sh]
  sunravelToList (AstNoVectorizeS t) =
    let f :: Int -> AstNoVectorizeS s r sh
        f i = AstNoVectorizeS $ AstIndexS t (singletonShaped $ fromIntegral i)
    in map f [0 .. slength t - 1]
  sreplicate = AstNoVectorizeS . AstReplicateS . unAstNoVectorizeS
  sappend u v =
    AstNoVectorizeS $ AstAppendS (unAstNoVectorizeS u) (unAstNoVectorizeS v)
  sslice (_ :: Proxy i) Proxy =
    AstNoVectorizeS . AstSliceS @i . unAstNoVectorizeS
  sreverse = AstNoVectorizeS . AstReverseS . unAstNoVectorizeS
  stranspose (_ :: Proxy perm) =
    AstNoVectorizeS . astTransposeS @perm . unAstNoVectorizeS
  sreshape = AstNoVectorizeS . astReshapeS . unAstNoVectorizeS
  sbuild1 f = AstNoVectorizeS $ AstBuild1S
                $ funToAstI  -- this introduces new variable names
                $ unAstNoVectorizeS . f . ShapedList.shapedNat
  sgather t f = AstNoVectorizeS $ AstGatherS (unAstNoVectorizeS t)
                $ funToAstIndexS f  -- this introduces new variable names
  scast = AstNoVectorizeS . AstCastS . unAstNoVectorizeS
  sfromIntegral = AstNoVectorizeS . fromPrimalS . AstFromIntegralS
                  . astSpanPrimalS . unAstNoVectorizeS
  sconst = AstNoVectorizeS . fromPrimalS . AstConstS
  sletHVectorIn a f =
    AstNoVectorizeS
    $ astLetHVectorInFunS a (unAstNoVectorizeS . f . noVectorizeHVector)
  sletHFunIn a f = AstNoVectorizeS $ sletHFunIn a (unAstNoVectorizeS . f)
  sfromR = AstNoVectorizeS . sfromR @(AstShaped s) . unAstNoVectorize

  sconstant = AstNoVectorizeS . fromPrimalS
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  sprimalPart = astSpanPrimalS . unAstNoVectorizeS
  sdualPart = astSpanDualS . unAstNoVectorizeS
  sD u u' = AstNoVectorizeS $ astSpanDS u u'
  sScale s t = astDualPartS $ AstConstantS s * AstDS 0 t

instance AstSpan s => HVectorTensor (AstNoVectorize s) (AstNoVectorizeS s) where
  dshape = dshape @(AstRanked s)
  dmkHVector hVector = dmkHVector @(AstRanked s) (unNoVectorizeHVector hVector)
  dlambda = dlambda @(AstRanked s)
  dHApply t ll = dHApply @(AstRanked s) t (map unNoVectorizeHVector ll)
  dunHVector doms = noVectorizeHVector $ dunHVector @(AstRanked s) doms
  dletHVectorInHVector a f =
    astLetHVectorInHVectorFun a (f . noVectorizeHVector)
  dletHFunInHVector = dletHFunInHVector @(AstRanked s)
  rletInHVector u f =
    rletInHVector @(AstRanked s) (unAstNoVectorize u) (f . AstNoVectorize)
  sletInHVector u f =
    sletInHVector @(AstRanked s) (unAstNoVectorizeS u) (f . AstNoVectorizeS)
  dsharePrimal = error "dsharePrimal for AstNoVectorize"
  dregister = error "dregister for AstNoVectorize"
  dbuild1 k f = AstBuildHVector1 k $ funToAstI f
  rrev f parameters0 hVector =
    rrev @(AstRanked s) f parameters0 (unNoVectorizeHVector hVector)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumR k accShs bShs eShs f acc0 es =
    dmapAccumR @(AstRanked s)
               k accShs bShs eShs f (unNoVectorizeHVector acc0)
                                    (unNoVectorizeHVector es)
  dmapAccumRDer k accShs bShs eShs f df rf acc0 es =
    dmapAccumRDer @(AstRanked s)
                  k accShs bShs eShs f df rf (unNoVectorizeHVector acc0)
                                             (unNoVectorizeHVector es)
  dmapAccumL k accShs bShs eShs f acc0 es =
    dmapAccumL @(AstRanked s)
               k accShs bShs eShs f (unNoVectorizeHVector acc0)
                                    (unNoVectorizeHVector es)
  dmapAccumLDer k accShs bShs eShs f df rf acc0 es =
    dmapAccumLDer @(AstRanked s)
                  k accShs bShs eShs f df rf (unNoVectorizeHVector acc0)
                                             (unNoVectorizeHVector es)

unNoVectorizeHVector :: HVector (AstNoVectorize s) -> HVector (AstRanked s)
unNoVectorizeHVector =
  let f (DynamicRanked (AstNoVectorize t)) = DynamicRanked t
      f (DynamicShaped (AstNoVectorizeS t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noVectorizeHVector :: HVector (AstRanked s) -> HVector (AstNoVectorize s)
noVectorizeHVector =
  let f (DynamicRanked t) = DynamicRanked $ AstNoVectorize t
      f (DynamicShaped t) = DynamicShaped $ AstNoVectorizeS t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

instance AstSpan s => RankedTensor (AstNoSimplify s) where
  rlet a f =
    AstNoSimplify
    $ astLetFunUnSimp (unAstNoSimplify a) (unAstNoSimplify . f . AstNoSimplify)
  rshape = shapeAst . unAstNoSimplify
  rminIndex = AstNoSimplify . fromPrimal . AstMinIndex
              . astSpanPrimal . unAstNoSimplify
  rmaxIndex = AstNoSimplify . fromPrimal . AstMaxIndex
              . astSpanPrimal . unAstNoSimplify
  rfloor = AstNoSimplify . fromPrimal . AstFloor
           . astSpanPrimal . unAstNoSimplify
  riota = AstNoSimplify . fromPrimal $ AstIota
  rindex v ix = AstNoSimplify $ AstIndex (unAstNoSimplify v) ix
  rsum = AstNoSimplify . AstSum . unAstNoSimplify
  rscatter sh t f = AstNoSimplify $ AstScatter sh (unAstNoSimplify t)
                    $ funToAstIndex f  -- this introduces new variable names
  rfromList = AstNoSimplify . AstFromList . map unAstNoSimplify
  rfromVector = AstNoSimplify . AstFromVector . V.map unAstNoSimplify
  runravelToList :: forall r n. (GoodScalar r, KnownNat n)
                 => AstNoSimplify s r (1 + n) -> [AstNoSimplify s r n]
  runravelToList (AstNoSimplify t) =
    let f :: Int -> AstNoSimplify s r n
        f i = AstNoSimplify $ AstIndex t (singletonIndex $ fromIntegral i)
    in map f [0 .. rlength t - 1]
  rreplicate k = AstNoSimplify . AstReplicate k . unAstNoSimplify
  rappend u v =
    AstNoSimplify $ AstAppend (unAstNoSimplify u) (unAstNoSimplify v)
  rslice i n = AstNoSimplify . AstSlice i n . unAstNoSimplify
  rreverse = AstNoSimplify . AstReverse . unAstNoSimplify
  rtranspose perm = AstNoSimplify . AstTranspose perm . unAstNoSimplify
  rreshape sh = AstNoSimplify . AstReshape sh . unAstNoSimplify
  rbuild1 k f = AstNoSimplify $ astBuild1Vectorize k (unAstNoSimplify . f)
  rgather sh t f = AstNoSimplify $ AstGather sh (unAstNoSimplify t)
                   $ funToAstIndex f  -- this introduces new variable names
  rcast = AstNoSimplify . AstCast . unAstNoSimplify
  rfromIntegral = AstNoSimplify . fromPrimal . AstFromIntegral
                  . astSpanPrimal . unAstNoSimplify
  rconst = AstNoSimplify . fromPrimal . AstConst
  rletHVectorIn a f =
    AstNoSimplify
    $ astLetHVectorInFun a (unAstNoSimplify . f . noSimplifyHVector)
  rletHFunIn a f = AstNoSimplify $ rletHFunIn a (unAstNoSimplify . f)
  rfromS = AstNoSimplify . rfromS @(AstRanked s) . unAstNoSimplifyS

  rconstant = AstNoSimplify . fromPrimal
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  rprimalPart = astSpanPrimal . unAstNoSimplify
  rdualPart = astSpanDual . unAstNoSimplify
  rD u u' = AstNoSimplify $ astSpanD u u'
  rScale s t = astDualPart $ AstConstant s * AstD (rzero (rshape s)) t

astLetFunUnSimp :: (KnownNat n, KnownNat m, GoodScalar r, AstSpan s)
                => AstRanked s r n -> (AstRanked s r n -> AstRanked s r2 m)
                -> AstRanked s r2 m
astLetFunUnSimp a f =
  let sh = shapeAst a
      (var, ast) = funToAstR sh f
  in AstLet var a ast

astLetFunUnSimpS
  :: (Sh.Shape sh, Sh.Shape sh2, GoodScalar r, AstSpan s)
  => AstShaped s r sh -> (AstShaped s r sh -> AstShaped s r2 sh2)
  -> AstShaped s r2 sh2
astLetFunUnSimpS a f =
  let (var, ast) = funToAstS f
  in AstLetS var a ast

instance AstSpan s => ShapedTensor (AstNoSimplifyS s) where
  slet a f =
    AstNoSimplifyS
    $ astLetFunUnSimpS (unAstNoSimplifyS a)
                       (unAstNoSimplifyS . f . AstNoSimplifyS)
  sminIndex = AstNoSimplifyS . fromPrimalS . AstMinIndexS
              . astSpanPrimalS . unAstNoSimplifyS
  smaxIndex = AstNoSimplifyS . fromPrimalS . AstMaxIndexS
              . astSpanPrimalS . unAstNoSimplifyS
  sfloor = AstNoSimplifyS . fromPrimalS . AstFloorS
           . astSpanPrimalS . unAstNoSimplifyS
  siota = AstNoSimplifyS . fromPrimalS $ AstIotaS
  sindex v ix = AstNoSimplifyS $ AstIndexS (unAstNoSimplifyS v) ix
  ssum = AstNoSimplifyS . AstSumS . unAstNoSimplifyS
  sscatter t f = AstNoSimplifyS $ AstScatterS (unAstNoSimplifyS t)
                 $ funToAstIndexS f  -- this introduces new variable names
  sfromList = AstNoSimplifyS . AstFromListS . map unAstNoSimplifyS
  sfromVector = AstNoSimplifyS . AstFromVectorS . V.map unAstNoSimplifyS
  sunravelToList :: forall r n sh. (GoodScalar r, KnownNat n, Sh.Shape sh)
                 => AstNoSimplifyS s r (n ': sh) -> [AstNoSimplifyS s r sh]
  sunravelToList (AstNoSimplifyS t) =
    let f :: Int -> AstNoSimplifyS s r sh
        f i = AstNoSimplifyS $ AstIndexS t (singletonShaped $ fromIntegral i)
    in map f [0 .. slength t - 1]
  sreplicate = AstNoSimplifyS . AstReplicateS . unAstNoSimplifyS
  sappend u v =
    AstNoSimplifyS $ AstAppendS (unAstNoSimplifyS u) (unAstNoSimplifyS v)
  sslice (_ :: Proxy i) Proxy = AstNoSimplifyS . AstSliceS @i . unAstNoSimplifyS
  sreverse = AstNoSimplifyS . AstReverseS . unAstNoSimplifyS
  stranspose (_ :: Proxy perm) =
    AstNoSimplifyS . AstTransposeS @perm . unAstNoSimplifyS
  sreshape = AstNoSimplifyS . AstReshapeS . unAstNoSimplifyS
  sbuild1 f = AstNoSimplifyS $ astBuild1VectorizeS (unAstNoSimplifyS . f)
  sgather t f = AstNoSimplifyS $ AstGatherS (unAstNoSimplifyS t)
                $ funToAstIndexS f  -- this introduces new variable names
  scast = AstNoSimplifyS . AstCastS . unAstNoSimplifyS
  sfromIntegral = AstNoSimplifyS . fromPrimalS . AstFromIntegralS
                  . astSpanPrimalS . unAstNoSimplifyS
  sconst = AstNoSimplifyS . fromPrimalS . AstConstS
  sletHVectorIn a f =
    AstNoSimplifyS
    $ astLetHVectorInFunS a (unAstNoSimplifyS . f . noSimplifyHVector)
  sletHFunIn a f = AstNoSimplifyS $ sletHFunIn a (unAstNoSimplifyS . f)
  sfromR = AstNoSimplifyS . sfromR @(AstShaped s) . unAstNoSimplify

  sconstant = AstNoSimplifyS . fromPrimalS
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  sprimalPart = astSpanPrimalS . unAstNoSimplifyS
  sdualPart = astSpanDualS . unAstNoSimplifyS
  sD u u' = AstNoSimplifyS $ astSpanDS u u'
  sScale s t = astDualPartS $ AstConstantS s * AstDS 0 t

instance AstSpan s => HVectorTensor (AstNoSimplify s) (AstNoSimplifyS s) where
  dshape = dshape @(AstRanked s)
  dmkHVector hVector = dmkHVector @(AstRanked s) (unNoSimplifyHVector hVector)
  dlambda = dlambda @(AstRanked s)
  dHApply t ll = dHApply @(AstRanked s) t (map unNoSimplifyHVector ll)
  dunHVector doms = noSimplifyHVector $ dunHVector @(AstRanked s) doms
  dletHVectorInHVector a f = astLetHVectorInHVectorFun a (f . noSimplifyHVector)
  dletHFunInHVector = dletHFunInHVector @(AstRanked s)
  rletInHVector u f =
    rletInHVector @(AstRanked s) (unAstNoSimplify u) (f . AstNoSimplify)
  sletInHVector u f =
    sletInHVector @(AstRanked s) (unAstNoSimplifyS u) (f . AstNoSimplifyS)
  dsharePrimal = error "dsharePrimal for AstNoVectorize"
  dregister = error "dregister for AstNoSimplify"
  dbuild1 = astBuildHVector1Vectorize
  rrev f parameters0 hVector =
    rrev @(AstRanked s) f parameters0 (unNoSimplifyHVector hVector)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumR k accShs bShs eShs f acc0 es =
    dmapAccumR @(AstRanked s)
               k accShs bShs eShs f (unNoSimplifyHVector acc0)
                                    (unNoSimplifyHVector es)
  dmapAccumRDer k accShs bShs eShs f df rf acc0 es =
    dmapAccumRDer @(AstRanked s)
                  k accShs bShs eShs f df rf (unNoSimplifyHVector acc0)
                                             (unNoSimplifyHVector es)
  dmapAccumL k accShs bShs eShs f acc0 es =
    dmapAccumL @(AstRanked s)
               k accShs bShs eShs f (unNoSimplifyHVector acc0)
                                    (unNoSimplifyHVector es)
  dmapAccumLDer k accShs bShs eShs f df rf acc0 es =
    dmapAccumLDer @(AstRanked s)
                  k accShs bShs eShs f df rf (unNoSimplifyHVector acc0)
                                             (unNoSimplifyHVector es)

unNoSimplifyHVector :: HVector (AstNoSimplify s) -> HVector (AstRanked s)
unNoSimplifyHVector =
  let f (DynamicRanked (AstNoSimplify t)) = DynamicRanked t
      f (DynamicShaped (AstNoSimplifyS t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noSimplifyHVector :: HVector (AstRanked s) -> HVector (AstNoSimplify s)
noSimplifyHVector =
  let f (DynamicRanked t) = DynamicRanked $ AstNoSimplify t
      f (DynamicShaped t) = DynamicShaped $ AstNoSimplifyS t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f
