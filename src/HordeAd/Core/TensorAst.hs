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
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal, type (+))
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
          unGradient = dunlet l astBindings (AstHVector gradient)
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
        envDt = extendEnvPars varsDt dts env
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
          unGradient = dunlet l astBindings (AstHVector gradient)
          unPrimal = sunlet l [] primalBody
      in ( ((varsDt, varsPrimal), unGradient, unPrimal, Sh.shapeT @sh)
         , delta )

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varsDt, vars), gradient, primal, _) parameters mdt =
    let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe 1 mdt
        dts = V.singleton $ DynamicShaped dt
        envDt = extendEnvPars varsDt dts env
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
                then Just $ HVectorPseudoTensor $ AstHVector astsDt
                else Nothing
          !(!astBindings, !gradient) =
            reverseDervative
              parameters0 (HVectorPseudoTensor primalBody) mdt delta
          unGradient = dunlet l astBindings (AstHVector gradient)
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
        envDt = extendEnvPars varsDt dts env
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

instance AdaptableHVector (AstRanked s) (AstHVector s) where
  type Value (AstHVector s) = HVector (Flip OR.Array)
  toHVector = undefined
  fromHVector aInit params =
    let (portion, rest) = V.splitAt (V.length aInit) params
    in Just (AstHVector portion, rest)

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
  rfromS = astSToR

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

instance ( GoodScalar r, KnownNat n
         , RankedTensor (AstRanked s) )
         => AdaptableHVector (AstRanked s) (AstRanked s r n) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstRanked s) (AstRanked s Double n) #-}
  type Value (AstRanked s r n) = Flip OR.Array r n
  toHVector = undefined
  fromHVector _aInit params = fromHVectorR @r @n params

astLetHVectorInFun
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => VoidHVector -> AstHVector s -> (HVector (AstRanked s) -> AstRanked s r n)
  -> AstRanked s r n
{-# INLINE astLetHVectorInFun #-}
astLetHVectorInFun a0 a f =
  fun1DToAst a0 $ \ !vars !asts -> astLetHVectorIn vars a (f asts)

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
  sfromR = astRToS

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

instance ( GoodScalar r, Sh.Shape sh
         , ShapedTensor (AstShaped s) )
         => AdaptableHVector (AstRanked s) (AstShaped s r sh) where
  type Value (AstShaped s r sh) = Flip OS.Array r sh
  toHVector = undefined
  fromHVector _aInit params = fromHVectorS @r @sh params

astLetHVectorInFunS
  :: forall sh s r. (Sh.Shape sh, GoodScalar r, AstSpan s)
  => VoidHVector -> AstHVector s -> (HVector (AstRanked s) -> AstShaped s r sh)
  -> AstShaped s r sh
{-# INLINE astLetHVectorInFunS #-}
astLetHVectorInFunS a0 a f =
  fun1DToAst a0 $ \ !vars !asts -> astLetHVectorInS vars a (f asts)

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

instance AstSpan s => HVectorTensor (AstRanked s) (AstShaped s) where
  dshape = shapeAstHVector
  dmkHVector = AstHVector
  dunHVector shs hVectorOf =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListShape (Sh.shapeT @sh) $ \(_ :: ShapeInt n) ->
              DynamicRanked @r @n
              $ rletHVectorIn @(AstRanked s) shs hVectorOf (rfromD . (V.! i))
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh
            $ sletHVectorIn @(AstShaped s) shs hVectorOf (sfromD . (V.! i))
        hv = V.imap f shs
    in assert (voidHVectorMatches shs hv) hv
  dletHVectorInHVector = astLetHVectorInHVectorFun
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
  dsharePrimal !shs !r !l | Just Refl <- sameAstSpan @s @PrimalSpan =
    fun1DToAst shs $ \ !vars !asts -> case vars of
      [] -> (l, V.empty)
      !var : _ ->  -- vars are fresh, so var uniquely represent vars
        ( insertADShare (dynamicVarNameToAstVarId var)
                        (AstBindingsHVector vars r)
                        l
        , asts )
  dsharePrimal _ _ _ = error "dsharePrimal: wrong span"
  dregister !domsOD !r !l =
    fun1DToAst domsOD $ \ !vars !asts -> case vars of
      [] -> error "dregister: empty hVector"
      !var : _ ->  -- vars are fresh, so var uniquely represent vars
        ((dynamicVarNameToAstVarId var, AstBindingsHVector vars r) : l, asts)
  dbuild1 = astBuildHVector1Vectorize
  dzipWith1 f u = case V.unsnoc u of
    Nothing -> error "dzipWith1: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "dzipWith1: wrong rank of argument"
      width : _ -> dbuild1 @(AstRanked s) width (\i -> f (index1HVector u i))
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (AstRanked s)
       -> AstHVector s
  rrev f parameters0 =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new @parmeters@, which is much better than computing anew.
    let (((_varsDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken False (f @(AstRanked FullSpan))
                             EM.empty parameters0
    in \parameters -> assert (voidHVectorMatches parameters0 parameters) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
      in interpretAstHVector env gradient
        -- this interpretation both substitutes parameters for the variables and
        -- reinterprets @PrimalSpan@ terms in @s@ terms;
        -- we could shortcut when @s@ is @PrimalSpan@ and @parameters@
        -- are the same variables, but it's a very special case
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => HVector f -> f r n)
         -> VoidHVector
         -> HVector (AstRanked s)
         -> AstRanked s r n
         -> AstHVector s
  rrevDt f parameters0 =
    let (((varsDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken True (f @(AstRanked FullSpan))
                             EM.empty parameters0
    in \parameters dt -> assert (voidHVectorMatches parameters0 parameters
                                 && length varsDt == 1) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
          dts = V.singleton $ DynamicRanked dt
          envDt = extendEnvPars varsDt dts env
      in interpretAstHVector envDt gradient
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (AstRanked s)
       -> HVector (AstRanked s)
       -> AstRanked s r n
  rfwd f parameters0 =
    let (((varsDt, vars), derivative, _primal), _delta) =
          fwdProduceArtifact TensorToken (f @(AstRanked FullSpan))
                             EM.empty parameters0
    in \parameters ds -> assert (voidHVectorMatches parameters0 parameters) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
          envDt = extendEnvPars @(AstRanked s) varsDt ds env
      in interpretAst envDt derivative
  srev f parameters0 =
    let (((_varsDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken False (f @(AstShaped FullSpan))
                             EM.empty parameters0
    in \parameters -> assert (voidHVectorMatches parameters0 parameters) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
      in interpretAstHVector env gradient
  srevDt f parameters0 =
    let (((varsDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken True (f @(AstShaped FullSpan))
                             EM.empty parameters0
    in \parameters dt -> assert (voidHVectorMatches parameters0 parameters
                                 && length varsDt == 1) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
          dts = V.singleton $ DynamicShaped dt
          envDt = extendEnvPars varsDt dts env
      in interpretAstHVector envDt gradient
  sfwd f parameters0 =
    let (((varsDt, vars), derivative, _primal), _delta) =
          fwdProduceArtifact TensorToken (f @(AstShaped FullSpan))
                             EM.empty parameters0
    in \parameters ds -> assert (voidHVectorMatches parameters0 parameters) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
          envDt = extendEnvPars @(AstRanked s) varsDt ds env
      in interpretAstS envDt derivative
  rfold :: forall rn rm n m.
           (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> AstRanked s rn n
        -> AstRanked s rm (1 + m)
        -> AstRanked s rn n
  rfold f x0 as =
    let shn = rshape x0
        shm = tailShape $ rshape as
        domsF = V.fromList [voidFromSh @rn shn, voidFromSh @rm shm]
        domsToPair :: forall f. ADReady f => HVector f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: HVector (AstRanked FullSpan) -> AstRanked FullSpan rn n
        g doms = uncurry f (domsToPair doms)
    in -- This computes the (AST of) derivative of f once for each @x0@
       -- and @as@, which is better than once for each @a@. We could compute
       -- it once per @f@ if we took shapes as arguments. The @sfold@ operation
       -- can do that thanks to shapes being available from types.
       case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varsDt, [AstDynamicVarName nid, AstDynamicVarName mid])
        , gradient, _primal, _sh), _delta ) -> assert (length varsDt == 1) $
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( [AstDynamicVarName nid1, AstDynamicVarName mid1]
              , [AstDynamicVarName nid2, AstDynamicVarName mid2] )
            , derivative, _primal), _delta ) ->
            let (nvar1, mvar1) = (AstVarName nid1, AstVarName mid1)
                (nvar2, mvar2) = (AstVarName nid2, AstVarName mid2)
                (nvar, mvar) = (AstVarName nid, AstVarName mid)
            in AstFoldDer (funToAst2R shn shm f)
                          (nvar1, mvar1, nvar2, mvar2, derivative)
                          ( AstVarName $ dynamicVarNameToAstVarId (varsDt !! 0)
                          , nvar, mvar, gradient )
                          x0 as
          _ -> error "rfold: wrong variables"
      _ -> error "rfold: wrong variables"
  rfoldDer :: forall rn rm n m.
              (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> HVectorOf f)
           -> AstRanked s rn n
           -> AstRanked s rm (1 + m)
           -> AstRanked s rn n
  rfoldDer f df rf x0 as =
    let shn = rshape x0
        shm = tailShape $ rshape as
    in AstFoldDer (funToAst2R shn shm f) (funToAst4R shn shm df)
                  (funToAst3R shn shm rf) x0 as
  rfoldZip :: forall rn n. (GoodScalar rn, KnownNat n)
         => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
         -> VoidHVector
         -> AstRanked s rn n
         -> HVector (AstRanked s)
         -> AstRanked s rn n
  rfoldZip f domsOD x0 asD = case V.unsnoc asD of
    Nothing -> error "rfoldZip: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "rfoldZip: wrong rank of argument"
      width : _shm -> case someNatVal $ toInteger width of
        Just (SomeNat @k _) ->
          assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD)
                                     asD) $
          let shn = rshape x0
              domsF = V.cons (voidFromSh @rn shn) domsOD
              domsToPair :: forall f. ADReady f
                         => HVector f -> (f rn n, HVector f)
              domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
              g :: HVector (AstRanked FullSpan) -> AstRanked FullSpan rn n
              g doms = uncurry f (domsToPair doms)
          in case revProduceArtifact TensorToken True g EM.empty domsF of
            ( ( (varsDt, AstDynamicVarName nid : mdyns)
              , gradient, _primal, _sh), _delta ) ->
              assert (length varsDt == 1) $
              case fwdProduceArtifact TensorToken g EM.empty domsF of
                ( ( ( AstDynamicVarName nid1 : mdyns1
                    , AstDynamicVarName nid2 : mdyns2 )
                  , derivative, _primal), _delta ) ->
                  let nvar1 = AstVarName nid1
                      nvar2 = AstVarName nid2
                      nvar = AstVarName nid
                  in AstFoldZipDer (funToAstRH shn f domsOD)
                                   (nvar1, mdyns1, nvar2, mdyns2, derivative)
                                   ( AstVarName
                                     $ dynamicVarNameToAstVarId (varsDt !! 0)
                                   , nvar, mdyns, gradient )
                                   x0 asD
                _ -> error "rfoldZip: wrong variables"
            _ -> error "rfoldZip: wrong variables"
        _ -> error "rfoldZip: impossible someNatVal"
  rfoldZipDer :: forall rn n. (GoodScalar rn, KnownNat n)
            => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> HVector f -> f rn n -> HVector f
                -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> f rn n -> HVector f
                -> HVectorOf f)
            -> VoidHVector
            -> AstRanked s rn n
            -> HVector (AstRanked s)
            -> AstRanked s rn n
  rfoldZipDer f df rf domsOD x0 asD = case V.unsnoc asD of
    Nothing -> error "rfoldZipDer: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "rfoldZipDer: wrong rank of argument"
      width : _shm -> case someNatVal $ toInteger width of
        Just (SomeNat @k _) ->
          assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD)
                                     asD) $
          let shn = rshape x0
          in AstFoldZipDer (funToAstRH shn f domsOD)
                           (funToAstRHRH shn df domsOD)
                           (funToAstRRH shn rf domsOD) x0 asD
        _ -> error "rfoldZipDer: impossible someNatVal"
  rscan :: forall rn rm n m.
           (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> AstRanked s rn n
        -> AstRanked s rm (1 + m)
        -> AstRanked s rn (1 + n)
  rscan f x0 as =
    let shn = rshape x0
        shm = tailShape $ rshape as
        domsF = V.fromList [voidFromSh @rn shn, voidFromSh @rm shm]
        domsToPair :: forall f. ADReady f => HVector f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: HVector (AstRanked FullSpan) -> AstRanked FullSpan rn n
        g doms = uncurry f (domsToPair doms)
    in -- This computes the (AST of) derivative of f once for each @x0@
       -- and @as@, which is better than once for each @a@. We could compute
       -- it once per @f@ if we took shapes as arguments. The @sfold@ operation
       -- can do that thanks to shapes being available from types.
       case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varsDt, [AstDynamicVarName nid, AstDynamicVarName mid])
        , gradient, _primal, _sh), _delta ) -> assert (length varsDt == 1) $
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( [AstDynamicVarName nid1, AstDynamicVarName mid1]
              , [AstDynamicVarName nid2, AstDynamicVarName mid2] )
            , derivative, _primal), _delta ) ->
            let (nvar1, mvar1) = (AstVarName nid1, AstVarName mid1)
                (nvar2, mvar2) = (AstVarName nid2, AstVarName mid2)
                (nvar, mvar) = (AstVarName nid, AstVarName mid)
            in AstScanDer (funToAst2R shn shm f)
                          (nvar1, mvar1, nvar2, mvar2, derivative)
                          ( AstVarName $ dynamicVarNameToAstVarId (varsDt !! 0)
                          , nvar, mvar, gradient )
                          x0 as
          _ -> error "rscan: wrong variables"
      _ -> error "rscan: wrong variables"
  rscanDer :: forall rn rm n m.
              (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> HVectorOf f)
           -> AstRanked s rn n
           -> AstRanked s rm (1 + m)
           -> AstRanked s rn (1 + n)
  rscanDer f df rf x0 as =
    let shn = rshape x0
        shm = tailShape $ rshape as
    in AstScanDer (funToAst2R shn shm f)
                  (funToAst4R shn shm df)
                  (funToAst3R shn shm rf) x0 as
  rscanZip :: forall rn n. (GoodScalar rn, KnownNat n)
         => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
         -> VoidHVector
         -> AstRanked s rn n
         -> HVector (AstRanked s)
         -> AstRanked s rn (1 + n)
  rscanZip f domsOD x0 asD = case V.unsnoc asD of
    Nothing -> error "rscanZip: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "rscanZip: wrong rank of argument"
      width : _shm -> case someNatVal $ toInteger width of
        Just (SomeNat @k _) ->
          assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD)
                                     asD) $
          let shn = rshape x0
              domsF = V.cons (voidFromSh @rn shn) domsOD
              domsToPair :: forall f. ADReady f
                         => HVector f -> (f rn n, HVector f)
              domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
              g :: HVector (AstRanked FullSpan) -> AstRanked FullSpan rn n
              g doms = uncurry f (domsToPair doms)
          in case revProduceArtifact TensorToken True g EM.empty domsF of
            ( ( (varsDt, AstDynamicVarName nid : mdyns)
              , gradient, _primal, _sh), _delta ) ->
              assert (length varsDt == 1) $
              case fwdProduceArtifact TensorToken g EM.empty domsF of
                ( ( ( AstDynamicVarName nid1 : mdyns1
                    , AstDynamicVarName nid2 : mdyns2 )
                  , derivative, _primal), _delta ) ->
                  let nvar1 = AstVarName nid1
                      nvar2 = AstVarName nid2
                      nvar = AstVarName nid
                  in AstScanZipDer (funToAstRH shn f domsOD)
                                   (nvar1, mdyns1, nvar2, mdyns2, derivative)
                                   ( AstVarName
                                     $ dynamicVarNameToAstVarId (varsDt !! 0)
                                   , nvar, mdyns, gradient )
                                   x0 asD
                _ -> error "rscanZip: wrong variables"
            _ -> error "rscanZip: wrong variables"
        _ -> error "rscanZip: impossible someNatVal"
  rscanZipDer :: forall rn n. (GoodScalar rn, KnownNat n)
            => (forall f. ADReady f => f rn n -> HVector f -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> HVector f -> f rn n -> HVector f
                -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> f rn n -> HVector f
                -> HVectorOf f)
            -> VoidHVector
            -> AstRanked s rn n
            -> HVector (AstRanked s)
            -> AstRanked s rn (1 + n)
  rscanZipDer f df rf domsOD x0 asD = case V.unsnoc asD of
    Nothing -> error "rscanZipDer: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "rscanZipDer: wrong rank of argument"
      width : _shm -> case someNatVal $ toInteger width of
        Just (SomeNat @k _) ->
          assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD)
                                     asD) $
          let shn = rshape x0
          in AstScanZipDer (funToAstRH shn f domsOD)
                           (funToAstRHRH shn df domsOD)
                           (funToAstRRH shn rf domsOD) x0 asD
        _ -> error "rscanZipDer: impossible someNatVal"
  sfold :: forall rn rm sh shm k.
           (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> AstShaped s rn sh
        -> AstShaped s rm (k ': shm)
        -> AstShaped s rn sh
  sfold f x0 as =
    let domsF = V.fromList [voidFromShS @rn @sh, voidFromShS @rm @shm]
        domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        g :: HVector (AstRanked FullSpan) -> AstShaped FullSpan rn sh
        g doms = uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varsDt, [AstDynamicVarName nid, AstDynamicVarName mid])
        , gradient, _primal, _sh), _delta ) -> assert (length varsDt == 1) $
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( [AstDynamicVarName nid1, AstDynamicVarName mid1]
              , [AstDynamicVarName nid2, AstDynamicVarName mid2] )
            , derivative, _primal), _delta ) ->
            let (nvar1, mvar1) = (AstVarName nid1, AstVarName mid1)
                (nvar2, mvar2) = (AstVarName nid2, AstVarName mid2)
                (nvar, mvar) = (AstVarName nid, AstVarName mid)
            in AstFoldDerS (funToAst2S f)
                           (nvar1, mvar1, nvar2, mvar2, derivative)
                           ( AstVarName $ dynamicVarNameToAstVarId (varsDt !! 0)
                           , nvar, mvar, gradient )
                           x0 as
          _ -> error "sfold: wrong variables"
      _ -> error "sfold: wrong variables"
  sfoldDer :: forall rn rm sh shm k. (GoodScalar rm, Sh.Shape shm, KnownNat k)
           => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rm shm -> f rn sh -> f rm shm
               -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rn sh -> f rm shm -> HVectorOf (RankedOf f))
           -> AstShaped s rn sh
           -> AstShaped s rm (k ': shm)
           -> AstShaped s rn sh
  sfoldDer f df rf x0 as =
    AstFoldDerS (funToAst2S f) (funToAst4S df) (funToAst3S rf) x0 as
  sfoldZip :: forall rn sh. (GoodScalar rn, Sh.Shape sh)
         => (forall f. ADReadyS f
             => f rn sh -> HVector (RankedOf f) -> f rn sh)
         -> VoidHVector
         -> AstShaped s rn sh
         -> HVector (AstRanked s)
         -> AstShaped s rn sh
  sfoldZip f domsOD x0 asD = case V.unsnoc asD of
    Nothing -> error "sfoldZip: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "sfoldZip: wrong rank of argument"
      width : _shm -> case someNatVal $ toInteger width of
        Just (SomeNat @k _) ->
          assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD)
                                     asD) $
          let domsF = V.cons (voidFromShS @rn @sh) domsOD
              domsToPair :: forall f. ADReadyS f
                         => HVector (RankedOf f)
                         -> (f rn sh, HVector (RankedOf f))
              domsToPair doms = (sfromD $ doms V.! 0, V.tail doms)
              g :: HVector (AstRanked FullSpan) -> AstShaped FullSpan rn sh
              g doms = uncurry f (domsToPair doms)
          in case revProduceArtifact TensorToken True g EM.empty domsF of
            ( ( (varsDt, AstDynamicVarName nid : mdyns)
              , gradient, _primal, _sh), _delta ) ->
              assert (length varsDt == 1) $
              case fwdProduceArtifact TensorToken g EM.empty domsF of
                ( ( ( AstDynamicVarName nid1 : mdyns1
                    , AstDynamicVarName nid2 : mdyns2 )
                  , derivative, _primal), _delta ) ->
                  let nvar1 = AstVarName nid1
                      nvar2 = AstVarName nid2
                      nvar = AstVarName nid
                  in AstFoldZipDerS (funToAstSH @_ @_ @sh f domsOD)
                                    (nvar1, mdyns1, nvar2, mdyns2, derivative)
                                    ( AstVarName
                                      $ dynamicVarNameToAstVarId (varsDt !! 0)
                                    , nvar, mdyns, gradient )
                                    x0 asD
                _ -> error "sfoldZip: wrong variables"
            _ -> error "sfoldZip: wrong variables"
        _ -> error "sfoldZip: impossible someNatVal"
  sfoldZipDer :: forall rn sh. Sh.Shape sh
            => (forall f. ADReadyS f
                => f rn sh -> HVector (RankedOf f) -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> HVector (RankedOf f) -> f rn sh
                -> HVector (RankedOf f)
                -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> f rn sh -> HVector (RankedOf f)
                -> HVectorOf (RankedOf f))
            -> VoidHVector
            -> AstShaped s rn sh
            -> HVector (AstRanked s)
            -> AstShaped s rn sh
  sfoldZipDer f df rf domsOD x0 asD = case V.unsnoc asD of
    Nothing -> error "sfoldZipDer: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "sfoldZipDer: wrong rank of argument"
      width : _shm -> case someNatVal $ toInteger width of
        Just (SomeNat @k _) ->
          assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD)
                                     asD) $
          AstFoldZipDerS (funToAstSH @_ @_ @sh f domsOD)
                         (funToAstSHSH @_ @_ @sh df domsOD)
                         (funToAstSSH @_ @_ @sh rf domsOD) x0 asD
        _ -> error "sfoldZipDer: impossible someNatVal"
  sscan :: forall rn rm sh shm k.
           (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> AstShaped s rn sh
        -> AstShaped s rm (k ': shm)
        -> AstShaped s rn (1 + k ': sh)
  sscan f x0 as =
    let domsF = V.fromList [voidFromShS @rn @sh, voidFromShS @rm @shm]
        domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        g :: HVector (AstRanked FullSpan) -> AstShaped FullSpan rn sh
        g doms = uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varsDt, [AstDynamicVarName nid, AstDynamicVarName mid])
        , gradient, _primal, _sh), _delta ) -> assert (length varsDt == 1) $
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( [AstDynamicVarName nid1, AstDynamicVarName mid1]
              , [AstDynamicVarName nid2, AstDynamicVarName mid2] )
            , derivative, _primal), _delta ) ->
            let (nvar1, mvar1) = (AstVarName nid1, AstVarName mid1)
                (nvar2, mvar2) = (AstVarName nid2, AstVarName mid2)
                (nvar, mvar) = (AstVarName nid, AstVarName mid)
            in AstScanDerS (funToAst2S @_ @_ @sh f)
                           (nvar1, mvar1, nvar2, mvar2, derivative)
                           ( AstVarName $ dynamicVarNameToAstVarId (varsDt !! 0)
                           , nvar, mvar, gradient )
                           x0 as
          _ -> error "sscan: wrong variables"
      _ -> error "sscan: wrong variables"
  sscanDer :: forall rn rm sh shm k.
              (GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
           => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rm shm -> f rn sh -> f rm shm
               -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rn sh -> f rm shm -> HVectorOf (RankedOf f))
           -> AstShaped s rn sh
           -> AstShaped s rm (k ': shm)
           -> AstShaped s rn (1 + k ': sh)
  sscanDer f df rf x0 as =
    AstScanDerS (funToAst2S @_ @_ @sh f)
                (funToAst4S @_ @_ @sh df)
                (funToAst3S @_ @_ @sh rf) x0 as
  sscanZip :: forall k rn sh. (GoodScalar rn, Sh.Shape sh, KnownNat k)
         => (forall f. ADReadyS f
             => f rn sh -> HVector (RankedOf f) -> f rn sh)
         -> VoidHVector
         -> AstShaped s rn sh
         -> HVector (AstRanked s)
         -> AstShaped s rn (1 + k ': sh)
  sscanZip f domsOD x0 asD =
    assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD) asD) $
    let domsF = V.cons (voidFromShS @rn @sh) domsOD
        domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f)
                   -> (f rn sh, HVector (RankedOf f))
        domsToPair doms = (sfromD $ doms V.! 0, V.tail doms)
        g :: HVector (AstRanked FullSpan) -> AstShaped FullSpan rn sh
        g doms = uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varsDt, AstDynamicVarName nid : mdyns)
        , gradient, _primal, _sh), _delta ) -> assert (length varsDt == 1) $
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( AstDynamicVarName nid1 : mdyns1
              , AstDynamicVarName nid2 : mdyns2 )
            , derivative, _primal), _delta ) ->
            let nvar1 = AstVarName nid1
                nvar2 = AstVarName nid2
                nvar = AstVarName nid
            in AstScanZipDerS (funToAstSH @_ @_ @sh f domsOD)
                              (nvar1, mdyns1, nvar2, mdyns2, derivative)
                              ( AstVarName
                                $ dynamicVarNameToAstVarId (varsDt !! 0)
                              , nvar, mdyns, gradient )
                              x0 asD
          _ -> error "sscanZip: wrong variables"
      _ -> error "sscanZip: wrong variables"
  sscanZipDer :: forall k rn sh. (Sh.Shape sh, KnownNat k)
            => (forall f. ADReadyS f
                => f rn sh -> HVector (RankedOf f) -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> HVector (RankedOf f) -> f rn sh
                -> HVector (RankedOf f)
                -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> f rn sh -> HVector (RankedOf f)
                -> HVectorOf (RankedOf f))
            -> VoidHVector
            -> AstShaped s rn sh
            -> HVector (AstRanked s)
            -> AstShaped s rn (1 + k ': sh)
  sscanZipDer f df rf domsOD x0 asD =
    assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD) asD) $
    AstScanZipDerS (funToAstSH @_ @_ @sh f domsOD)
                   (funToAstSHSH @_ @_ @sh df domsOD)
                   (funToAstSSH @_ @_ @sh rf domsOD) x0 asD
  dmapAccumR
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> HVector (AstRanked s)
    -> HVector (AstRanked s)
    -> AstHVector s
  dmapAccumR k accShs bShs eShs f acc0 es =
    assert (voidHVectorMatches (replicate1VoidHVector k eShs) es
            && voidHVectorMatches accShs acc0) $
    let accLen = V.length accShs
        hvToPair :: forall f. HVector f -> (HVector f, HVector f)
        hvToPair hv = (V.take accLen hv, V.drop accLen hv)
        accEShs = accShs V.++ eShs
        g :: HVector (AstRanked FullSpan)
          -> HVectorPseudoTensor (AstRanked FullSpan) Float '()
        g hv = HVectorPseudoTensor $ uncurry f (hvToPair hv)
        (((varsDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken True g EM.empty accEShs
        (((varsDt2, vars2), derivative, _primal2), _delta2) =
          fwdProduceArtifact TensorToken g EM.empty accEShs
     in AstMapAccumRDer k accShs bShs eShs
                        (funToAstHH f accShs eShs)
                        ( take accLen varsDt2, drop accLen varsDt2
                        , take accLen vars2, drop accLen vars2
                        , unHVectorPseudoTensor derivative )
                        ( take accLen varsDt, drop accLen varsDt
                        , take accLen vars, drop accLen vars
                        , gradient )
                        acc0 es
  dmapAccumRDer
    :: SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVectorOf f)
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f)
    -> (forall f. ADReady f
        => HVector f -> HVector f -> HVector f -> HVector f -> HVectorOf f)
    -> HVector (AstRanked s)
    -> HVector (AstRanked s)
    -> AstHVector s
  dmapAccumRDer k accShs bShs eShs f df rf acc0 es =
    assert (voidHVectorMatches (replicate1VoidHVector k eShs) es
            && voidHVectorMatches accShs acc0) $
    AstMapAccumRDer k accShs bShs eShs
                    (funToAstHH f accShs eShs)
                    (funToAstHHHH df accShs eShs)
                    (funToAstHHHG rf accShs bShs eShs)
                    acc0 es
  rmapAccumR
    :: forall rn n. (GoodScalar rn, KnownNat n)
    => VoidHVector
    -> (forall f. ADReady f
        => f rn n -> HVector f -> HVectorOf f)
    -> VoidHVector
    -> AstRanked s rn n
    -> HVector (AstRanked s)
    -> AstHVector s
  rmapAccumR domB f domsOD x0 asD =
    let width = case V.unsnoc asD of
          Nothing -> error "rmapAccumRDer: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "rmapAccumRDer: wrong rank of argument"
            width2 : _shm -> width2
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD)
                                   asD) $
        let shn = rshape x0
            domsF = V.cons (voidFromSh @rn shn) domsOD
            domsToPair :: forall f. ADReady f
                       => HVector f -> (f rn n, HVector f)
            domsToPair doms = (rfromD $ doms V.! 0, V.tail doms)
            g :: HVector (AstRanked FullSpan)
              -> HVectorPseudoTensor (AstRanked FullSpan) Float '()
            g doms = HVectorPseudoTensor $ uncurry f (domsToPair doms)
        in case revProduceArtifact TensorToken True g EM.empty domsF of
          ( ( (AstDynamicVarName nid3 : mdyns3, AstDynamicVarName nid : mdyns)
            , gradient, _primal, _sh), _delta ) ->
            case fwdProduceArtifact TensorToken g EM.empty domsF of
              ( ( ( AstDynamicVarName nid1 : mdyns1
                  , AstDynamicVarName nid2 : mdyns2 )
                , derivative, _primal), _delta ) ->
                let nvar1 = AstVarName nid1
                    nvar2 = AstVarName nid2
                    varDt3 = AstVarName nid3
                    nvar = AstVarName nid
                in AstMapAccumRDerR domB
                                    (funToAstRH shn f domsOD)
                                    ( nvar1, mdyns1, nvar2, mdyns2
                                    , unHVectorPseudoTensor derivative )
                                    (varDt3, mdyns3, nvar, mdyns, gradient)
                                    x0 asD
              _ -> error "rmapAccumR: wrong variables"
          _ -> error "rmapAccumR: wrong variables"
      _ -> error "rmapAccumR: impossible someNatVal"
  rmapAccumRDer
    :: forall rn n. (GoodScalar rn, KnownNat n)
    => VoidHVector
    -> (forall f. ADReady f
        => f rn n
        -> HVector f
        -> HVectorOf f)
    -> (forall f. ADReady f
        => f rn n
        -> HVector f
        -> f rn n
        -> HVector f
        -> HVectorOf f)
    -> (forall f. ADReady f
        => f rn n
        -> HVector f
        -> f rn n
        -> HVector f
        -> HVectorOf f)
    -> VoidHVector
    -> AstRanked s rn n
    -> HVector (AstRanked s)
    -> AstHVector s
  rmapAccumRDer domB f df rf domsOD x0 asD =
    let width = case V.unsnoc asD of
          Nothing -> error "rmapAccumRDer: can't determine argument width"
          Just (_, d) -> case shapeDynamic d of
            [] -> error "rmapAccumRDer: wrong rank of argument"
            width2 : _shm -> width2
    in case someNatVal $ toInteger width of
      Just (SomeNat @k _) ->
        assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD)
                                   asD) $
        let shn = rshape x0
        in AstMapAccumRDerR domB
                            (funToAstRH shn f domsOD)
                            (funToAstRHRH shn df domsOD)
                            (funToAstRHRG shn rf domB domsOD) x0 asD
      _ -> error "rmapAccumRDer: impossible someNatVal"
  smapAccumR
    :: forall k rn sh. (GoodScalar rn, Sh.Shape sh, KnownNat k)
    => Proxy k
    -> VoidHVector
    -> (forall f. ADReadyS f
        => f rn sh -> HVector (RankedOf f) -> HVectorOf (RankedOf f))
    -> VoidHVector
    -> AstShaped s rn sh
    -> HVector (AstRanked s)
    -> AstHVector s
  smapAccumR _proxy_k domB f domsOD x0 asD =
    assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD) asD) $
    let domsF = V.cons (voidFromShS @rn @sh) domsOD
        domsToPair :: forall f. ADReadyS f
                   => HVector (RankedOf f)
                   -> (f rn sh, HVector (RankedOf f))
        domsToPair doms = (sfromD $ doms V.! 0, V.tail doms)
        g :: HVector (AstRanked FullSpan)
          -> HVectorPseudoTensor (AstRanked FullSpan) Float '()
        g doms = HVectorPseudoTensor $ uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (AstDynamicVarName nid3 : mdyns3, AstDynamicVarName nid : mdyns)
        , gradient, _primal, _sh), _delta ) ->
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( AstDynamicVarName nid1 : mdyns1
              , AstDynamicVarName nid2 : mdyns2 )
            , derivative, _primal), _delta ) ->
            let nvar1 = AstVarName nid1
                nvar2 = AstVarName nid2
                varDt3 = AstVarName nid3
                nvar = AstVarName nid
            in AstMapAccumRDerS @k domB
                                (funToAstSH @_ @_ @sh f domsOD)
                                ( nvar1, mdyns1, nvar2, mdyns2
                                , unHVectorPseudoTensor derivative )
                                (varDt3, mdyns3, nvar, mdyns, gradient)
                                x0 asD
          _ -> error "smapAccumR: wrong variables"
      _ -> error "smapAccumR: wrong variables"
  smapAccumRDer
    :: forall k rn sh. (GoodScalar rn, Sh.Shape sh, KnownNat k)
    => Proxy k
    -> VoidHVector
    -> (forall f. ADReadyS f
        => f rn sh
        -> HVector (RankedOf f)
        -> HVectorOf (RankedOf f))
    -> (forall f. ADReadyS f
        => f rn sh
        -> HVector (RankedOf f)
        -> f rn sh
        -> HVector (RankedOf f)
        -> HVectorOf (RankedOf f))
    -> (forall f. ADReadyS f
        => f rn sh
        -> HVector (RankedOf f)
        -> f rn sh
        -> HVector (RankedOf f)
        -> HVectorOf (RankedOf f))
    -> VoidHVector
    -> AstShaped s rn sh
    -> HVector (AstRanked s)
    -> AstHVector s
  smapAccumRDer _proxy_k domB f df rf domsOD x0 asD =
    assert (voidHVectorMatches (replicate1VoidHVector (SNat @k) domsOD) asD) $
    AstMapAccumRDerS @k domB
                     (funToAstSH @_ @_ @sh f domsOD)
                     (funToAstSHSH @_ @_ @sh df domsOD)
                     (funToAstSHSG @_ @_ @sh rf domB domsOD) x0 asD

astLetHVectorInHVectorFun
  :: AstSpan s
  => VoidHVector -> AstHVector s -> (HVector (AstRanked s) -> AstHVector s)
  -> AstHVector s
{-# INLINE astLetHVectorInHVectorFun #-}
astLetHVectorInHVectorFun a0 a f =
  fun1DToAst a0 $ \ !vars !asts -> astLetHVectorInHVector vars a (f asts)

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
  => Int -> (AstInt -> AstHVector s) -> AstHVector s
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
  rletHVectorIn a0 a f =
    AstNoVectorize $ astLetHVectorInFun
                       a0 a (unAstNoVectorize . f . noVectorizeHVector)
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
  sletHVectorIn a0 a f =
    AstNoVectorizeS $ astLetHVectorInFunS
                        a0 a (unAstNoVectorizeS . f . noVectorizeHVector)
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
  dunHVector parameters0 doms =
    noVectorizeHVector $ dunHVector @(AstRanked s) parameters0 doms
  dletHVectorInHVector a0 a f =
    astLetHVectorInHVectorFun a0 a (f . noVectorizeHVector)
  rletInHVector u f =
    rletInHVector @(AstRanked s) (unAstNoVectorize u) (f . AstNoVectorize)
  sletInHVector u f =
    sletInHVector @(AstRanked s) (unAstNoVectorizeS u) (f . AstNoVectorizeS)
  dsharePrimal = error "dsharePrimal for AstNoVectorize"
  dregister = error "dregister for AstNoVectorize"
  dbuild1 k f = AstBuildHVector1 k $ funToAstI f
  dzipWith1 f u = case V.unsnoc u of
    Nothing -> error "dzipWith1: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "dzipWith1: wrong rank of argument"
      width : _ ->
        dbuild1 @(AstNoVectorize s) width (\i -> f (index1HVector u i))
  rrev f parameters0 hVector =
    rrev @(AstRanked s) f parameters0 (unNoVectorizeHVector hVector)
  rrevDt f parameters0 hVector dt =
    rrevDt @(AstRanked s) f parameters0
           (unNoVectorizeHVector hVector) (unAstNoVectorize dt)
  rfwd f parameters0 hVector ds =
    AstNoVectorize
    $ rfwd @(AstRanked s) f parameters0
           (unNoVectorizeHVector hVector) (unNoVectorizeHVector ds)
  srev f parameters0 hVector =
    srev @(AstRanked s) f parameters0 (unNoVectorizeHVector hVector)
  srevDt f parameters0 hVector dt =
    srevDt @(AstRanked s) f parameters0
           (unNoVectorizeHVector hVector) (unAstNoVectorizeS dt)
  sfwd f parameters0 hVector ds =
    AstNoVectorizeS
    $ sfwd @(AstRanked s) f parameters0
           (unNoVectorizeHVector hVector) (unNoVectorizeHVector ds)
  rfold f x0 as =
    AstNoVectorize
    $ rfold @(AstRanked s) f (unAstNoVectorize x0) (unAstNoVectorize as)
  rfoldDer f df rf x0 as =
    AstNoVectorize
    $ rfoldDer @(AstRanked s)
               f df rf (unAstNoVectorize x0) (unAstNoVectorize as)
  rfoldZip f domsOD x0 as =
    AstNoVectorize
    $ rfoldZip @(AstRanked s) f domsOD (unAstNoVectorize x0)
                                       (unNoVectorizeHVector as)
  rfoldZipDer f df rf domsOD x0 as =
    AstNoVectorize
    $ rfoldZipDer @(AstRanked s)
                  f df rf domsOD (unAstNoVectorize x0) (unNoVectorizeHVector as)
  rscan f x0 as =
    AstNoVectorize
    $ rscan @(AstRanked s) f (unAstNoVectorize x0) (unAstNoVectorize as)
  rscanDer f df rf x0 as =
    AstNoVectorize
    $ rscanDer @(AstRanked s)
               f df rf (unAstNoVectorize x0) (unAstNoVectorize as)
  rscanZip f domsOD x0 as =
    AstNoVectorize
    $ rscanZip @(AstRanked s) f domsOD (unAstNoVectorize x0)
                                       (unNoVectorizeHVector as)
  rscanZipDer f df rf domsOD x0 as =
    AstNoVectorize
    $ rscanZipDer @(AstRanked s)
                  f df rf domsOD (unAstNoVectorize x0) (unNoVectorizeHVector as)
  sfold f x0 as =
    AstNoVectorizeS
    $ sfold @(AstRanked s) f (unAstNoVectorizeS x0) (unAstNoVectorizeS as)
  sfoldDer f df rf x0 as =
    AstNoVectorizeS
    $ sfoldDer @(AstRanked s)
               f df rf (unAstNoVectorizeS x0) (unAstNoVectorizeS as)
  sfoldZip f domsOD x0 as =
    AstNoVectorizeS
    $ sfoldZip @(AstRanked s) f domsOD (unAstNoVectorizeS x0)
                                       (unNoVectorizeHVector as)
  sfoldZipDer f df rf domsOD x0 as =
    AstNoVectorizeS
    $ sfoldZipDer @(AstRanked s)
                  f df rf domsOD (unAstNoVectorizeS x0)
                                 (unNoVectorizeHVector as)
  sscan f x0 as =
    AstNoVectorizeS
    $ sscan @(AstRanked s) f (unAstNoVectorizeS x0) (unAstNoVectorizeS as)
  sscanDer f df rf x0 as =
    AstNoVectorizeS
    $ sscanDer @(AstRanked s)
               f df rf (unAstNoVectorizeS x0) (unAstNoVectorizeS as)
  sscanZip f domsOD x0 as =
    AstNoVectorizeS
    $ sscanZip @(AstRanked s) f domsOD (unAstNoVectorizeS x0)
                                       (unNoVectorizeHVector as)
  sscanZipDer f df rf domsOD x0 as =
    AstNoVectorizeS
    $ sscanZipDer @(AstRanked s)
                  f df rf domsOD (unAstNoVectorizeS x0)
                                 (unNoVectorizeHVector as)
  dmapAccumR k accShs bShs eShs f acc0 es =
    dmapAccumR @(AstRanked s)
               k accShs bShs eShs f (unNoVectorizeHVector acc0)
                                    (unNoVectorizeHVector es)
  dmapAccumRDer k accShs bShs eShs f df rf acc0 es =
    dmapAccumRDer @(AstRanked s)
                  k accShs bShs eShs f df rf (unNoVectorizeHVector acc0)
                                             (unNoVectorizeHVector es)
  rmapAccumR domB f domsOD x0 as =
    rmapAccumR @(AstRanked s) domB f domsOD (unAstNoVectorize x0)
                                            (unNoVectorizeHVector as)
  rmapAccumRDer domB f df rf domsOD x0 as =
    rmapAccumRDer @(AstRanked s)
                  domB f df rf domsOD (unAstNoVectorize x0)
                                      (unNoVectorizeHVector as)
  smapAccumR proxy_k domB f domsOD x0 as =
    smapAccumR @(AstRanked s) proxy_k domB f domsOD (unAstNoVectorizeS x0)
                                                    (unNoVectorizeHVector as)
  smapAccumRDer proxy_k domB f df rf domsOD x0 as =
    smapAccumRDer @(AstRanked s)
                  proxy_k domB f df rf domsOD (unAstNoVectorizeS x0)
                                              (unNoVectorizeHVector as)

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
  rletHVectorIn a0 a f =
    AstNoSimplify $ astLetHVectorInFun
                      a0 a (unAstNoSimplify . f . noSimplifyHVector)
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
  sletHVectorIn a0 a f =
    AstNoSimplifyS $ astLetHVectorInFunS
                       a0 a (unAstNoSimplifyS . f . noSimplifyHVector)
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
  dunHVector parameters0 doms =
    noSimplifyHVector $ dunHVector @(AstRanked s) parameters0 doms
  dletHVectorInHVector a0 a f =
    astLetHVectorInHVectorFun a0 a (f . noSimplifyHVector)
  rletInHVector u f =
    rletInHVector @(AstRanked s) (unAstNoSimplify u) (f . AstNoSimplify)
  sletInHVector u f =
    sletInHVector @(AstRanked s) (unAstNoSimplifyS u) (f . AstNoSimplifyS)
  dsharePrimal = error "dsharePrimal for AstNoVectorize"
  dregister = error "dregister for AstNoSimplify"
  dbuild1 = astBuildHVector1Vectorize
  dzipWith1 f u = case V.unsnoc u of
    Nothing -> error "dzipWith1: can't determine argument width"
    Just (_, d) -> case shapeDynamic d of
      [] -> error "dzipWith1: wrong rank of argument"
      width : _ ->
        dbuild1 @(AstNoSimplify s) width (\i -> f (index1HVector u i))
  rrev f parameters0 hVector =
    rrev @(AstRanked s) f parameters0 (unNoSimplifyHVector hVector)
  rrevDt f parameters0 hVector dt =
    rrevDt @(AstRanked s) f parameters0
           (unNoSimplifyHVector hVector) (unAstNoSimplify dt)
  rfwd f parameters0 hVector ds =
    AstNoSimplify $ rfwd @(AstRanked s) f parameters0
                         (unNoSimplifyHVector hVector) (unNoSimplifyHVector ds)
  srev f parameters0 hVector =
    srev @(AstRanked s) f parameters0 (unNoSimplifyHVector hVector)
  srevDt f parameters0 hVector dt =
    srevDt @(AstRanked s) f parameters0
           (unNoSimplifyHVector hVector) (unAstNoSimplifyS dt)
  sfwd f parameters0 hVector ds =
    AstNoSimplifyS $ sfwd @(AstRanked s) f parameters0
                          (unNoSimplifyHVector hVector) (unNoSimplifyHVector ds)
  rfold f x0 as =
    AstNoSimplify
    $ rfold @(AstRanked s) f (unAstNoSimplify x0) (unAstNoSimplify as)
  rfoldDer f df rf x0 as =
    AstNoSimplify
    $ rfoldDer @(AstRanked s) f df rf (unAstNoSimplify x0) (unAstNoSimplify as)
  rfoldZip f domsOD x0 as =
    AstNoSimplify
    $ rfoldZip @(AstRanked s) f domsOD (unAstNoSimplify x0)
                                       (unNoSimplifyHVector as)
  rfoldZipDer f df rf domsOD x0 as =
    AstNoSimplify
    $ rfoldZipDer @(AstRanked s)
                  f df rf domsOD (unAstNoSimplify x0) (unNoSimplifyHVector as)
  rscan f x0 as =
    AstNoSimplify
    $ rscan @(AstRanked s) f (unAstNoSimplify x0) (unAstNoSimplify as)
  rscanDer f df rf x0 as =
    AstNoSimplify
    $ rscanDer @(AstRanked s) f df rf (unAstNoSimplify x0) (unAstNoSimplify as)
  rscanZip f domsOD x0 as =
    AstNoSimplify
    $ rscanZip @(AstRanked s) f domsOD (unAstNoSimplify x0)
                                       (unNoSimplifyHVector as)
  rscanZipDer f df rf domsOD x0 as =
    AstNoSimplify
    $ rscanZipDer @(AstRanked s)
                  f df rf domsOD (unAstNoSimplify x0) (unNoSimplifyHVector as)
  sfold f x0 as =
    AstNoSimplifyS
    $ sfold @(AstRanked s) f (unAstNoSimplifyS x0) (unAstNoSimplifyS as)
  sfoldDer f df rf x0 as =
    AstNoSimplifyS
    $ sfoldDer @(AstRanked s)
               f df rf (unAstNoSimplifyS x0) (unAstNoSimplifyS as)
  sfoldZip f domsOD x0 as =
    AstNoSimplifyS
    $ sfoldZip @(AstRanked s) f domsOD (unAstNoSimplifyS x0)
                                       (unNoSimplifyHVector as)
  sfoldZipDer f df rf domsOD x0 as =
    AstNoSimplifyS
    $ sfoldZipDer @(AstRanked s)
                  f df rf domsOD (unAstNoSimplifyS x0) (unNoSimplifyHVector as)
  sscan f x0 as =
    AstNoSimplifyS
    $ sscan @(AstRanked s) f (unAstNoSimplifyS x0) (unAstNoSimplifyS as)
  sscanDer f df rf x0 as =
    AstNoSimplifyS
    $ sscanDer @(AstRanked s)
               f df rf (unAstNoSimplifyS x0) (unAstNoSimplifyS as)
  sscanZip f domsOD x0 as =
    AstNoSimplifyS
    $ sscanZip @(AstRanked s) f domsOD (unAstNoSimplifyS x0)
                                       (unNoSimplifyHVector as)
  sscanZipDer f df rf domsOD x0 as =
    AstNoSimplifyS
    $ sscanZipDer @(AstRanked s)
                  f df rf domsOD (unAstNoSimplifyS x0) (unNoSimplifyHVector as)
  dmapAccumR k accShs bShs eShs f acc0 es =
    dmapAccumR @(AstRanked s)
               k accShs bShs eShs f (unNoSimplifyHVector acc0)
                                    (unNoSimplifyHVector es)
  dmapAccumRDer k accShs bShs eShs f df rf acc0 es =
    dmapAccumRDer @(AstRanked s)
                  k accShs bShs eShs f df rf (unNoSimplifyHVector acc0)
                                             (unNoSimplifyHVector es)
  rmapAccumR domB f domsOD x0 as =
    rmapAccumR @(AstRanked s) domB f domsOD (unAstNoSimplify x0)
                                            (unNoSimplifyHVector as)
  rmapAccumRDer domB f df rf domsOD x0 as =
    rmapAccumRDer @(AstRanked s)
                  domB f df rf domsOD (unAstNoSimplify x0)
                                      (unNoSimplifyHVector as)
  smapAccumR proxy_k domB f domsOD x0 as =
    smapAccumR @(AstRanked s) proxy_k domB f domsOD (unAstNoSimplifyS x0)
                                                    (unNoSimplifyHVector as)
  smapAccumRDer proxy_k domB f df rf domsOD x0 as =
    smapAccumRDer @(AstRanked s)
                  proxy_k domB f df rf domsOD (unAstNoSimplifyS x0)
                                              (unNoSimplifyHVector as)

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
