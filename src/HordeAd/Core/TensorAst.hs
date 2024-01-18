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
import           GHC.TypeLits (KnownNat, Nat, type (+))
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
import           HordeAd.Core.DualClass
import           HordeAd.Core.DualNumber
import           HordeAd.Core.TensorADVal ()
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Util.ShapedList (singletonShaped)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex

-- * IsPrimal instances

instance (GoodScalar r, KnownNat n) => IsPrimal (AstRanked PrimalSpan) r n where
  dZeroOfShape tsh = ZeroR (rshape tsh)
  dScale _ (ZeroR sh) = ZeroR sh
  dScale v u' = ScaleR v u'
  dAdd ZeroR{} w = w
  dAdd v ZeroR{} = v
  dAdd v w = AddR v w
  intOfShape tsh c =
    rconst $ OR.constant (shapeToList $ rshape tsh) (fromIntegral c)
  recordSharingPrimal = astRegisterADShare
  recordSharing d = case d of
    ZeroR{} -> d
    InputR{} -> d
    SToR{} -> d
    LetR{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaR d

instance (GoodScalar r, Sh.Shape sh)
         => IsPrimal (AstShaped PrimalSpan) r sh where
  dZeroOfShape _tsh = ZeroS
  dScale _ ZeroS = ZeroS
  dScale v u' = ScaleS v u'
  dAdd ZeroS w = w
  dAdd v ZeroS = v
  dAdd v w = AddS v w
  intOfShape _tsh c =  -- this is not needed for OS, but OR needs it
    sconst $ fromIntegral c
  recordSharingPrimal = astRegisterADShareS
  recordSharing d = case d of
    ZeroS -> d
    InputS{} -> d
    RToS{} -> d
    LetS{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaS d


-- * Reverse and forward derivative stages instances

instance DerivativeStages (AstRanked FullSpan) where
  forwardPassByInterpretation
    :: (GoodScalar r, KnownNat n)
    => (Domains (AstRanked FullSpan) -> AstRanked FullSpan r n)
    -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
    -> Domains (AstRanked PrimalSpan)
    -> [AstDynamicVarName]
    -> Domains (AstRanked FullSpan)
    -> ADVal (AstRanked PrimalSpan) r n
  {-# INLINE forwardPassByInterpretation #-}
  forwardPassByInterpretation g envInit domainsPrimal vars domains =
    let deltaInputs = generateDeltaInputs domainsPrimal
        varInputs = makeADInputs domainsPrimal deltaInputs
        ast = g domains
        env = foldr extendEnvD envInit $ zip vars $ V.toList varInputs
    in interpretAst env ast

  revArtifactFromForwardPass
    :: forall r n. (GoodScalar r, KnownNat n)
    => TensorToken (AstRanked FullSpan) -> Bool
    -> (Domains (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> Domains (AstRanked FullSpan)
        -> ADVal (AstRanked PrimalSpan) r n)
    -> DomainsOD
    -> ( AstArtifactRev (AstRanked PrimalSpan) r n
       , Dual (AstRanked PrimalSpan) r n )
  {-# INLINE revArtifactFromForwardPass #-}
  revArtifactFromForwardPass _ hasDt forwardPass parameters0 =
    let -- Bangs and the compound function to fix the numbering of variables
        -- for pretty-printing and prevent sharing the impure values/effects
        -- in tests that reset the impure counters.
        !(!varDtId, varsPrimal, domainsPrimal, vars, domains) =
          funToAstRev parameters0 in
    let -- Evaluate completely after terms constructed, to free memory
        -- before gradientFromDelta allocates new memory and new FFI is started.
        !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
    let varDt = AstVarName varDtId
        sh = shapeAst primalBody
        astDt = AstVar sh varDt
        mdt = if hasDt then Just astDt else Nothing
        !(!astBindings, !gradient) =
          reverseDervative parameters0 primalBody mdt delta
        unGradient = unletGradient @Nat @(AstRanked PrimalSpan)
                                 l astBindings gradient
        unPrimal = unletValue l [] primalBody
    in ( ((varDt, varsPrimal), unGradient, unPrimal, shapeToList sh)
       , delta )
         -- storing sh computed from primalBody often saves the unletAst6
         -- execution; we could store the whole primalBody, as we do in calls
         -- to reverseDervative, but we can potentially free it earlier this way
         -- (as soon as sh is forced or determined to be unneeded)

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varDt, vars), gradient, primal, sh) parameters mdt =
    let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe (rreplicate0N (listShapeToShape sh) 1) mdt
        envDt = extendEnvR varDt dt env
        gradientDomain = interpretAstDomains envDt gradient
        primalTensor = interpretAstPrimal env primal
    in (gradientDomain, primalTensor)

  fwdArtifactFromForwardPass
    :: forall r n. (GoodScalar r, KnownNat n)
    => TensorToken (AstRanked FullSpan)
    -> (Domains (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> Domains (AstRanked FullSpan)
        -> ADVal (AstRanked PrimalSpan) r n)
    -> DomainsOD
    -> ( AstArtifactFwd (AstRanked PrimalSpan) r n
       , Dual (AstRanked PrimalSpan) r n )
  {-# INLINE fwdArtifactFromForwardPass #-}
  fwdArtifactFromForwardPass _ forwardPass parameters0 =
    let !(!varsPrimalDs, domainsDs, varsPrimal, domainsPrimal, vars, domains) =
          funToAstFwd parameters0 in
    let !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
    let !(!astBindings, !derivative) =
          forwardDerivative (V.length parameters0) delta domainsDs
        unDerivative = unletValue l astBindings derivative
        unPrimal = unletValue l [] primalBody
    in ( ((varsPrimalDs, varsPrimal), unDerivative, unPrimal)
       , delta )

  {-# INLINE fwdEvalArtifact #-}
  fwdEvalArtifact ((varDs, vars), derivative, primal) parameters ds =
    if domainsMatch parameters ds then
      let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
          envDs = foldr extendEnvD env $ zip varDs $ V.toList ds
          derivativeTensor = interpretAstPrimal envDs derivative
          primalTensor = interpretAstPrimal @(Flip OR.Array) env primal
      in (derivativeTensor, primalTensor)
   else error "fwdEvalArtifact: forward derivative input and sensitivity arguments should have same shapes"

instance UnletGradient (AstRanked PrimalSpan) where
  unletGradient
    :: ADShare -> AstBindings -> Domains (AstRanked PrimalSpan)
    -> AstDomains PrimalSpan
  unletGradient l astBindings gradient =
    unletAstDomains6 astBindings l
                     (dmkDomains @(AstRanked PrimalSpan) gradient)
  unletValue
    :: (GoodScalar r, KnownNat n)
    => ADShare -> AstBindings -> AstRanked PrimalSpan r n
    -> AstRanked PrimalSpan r n
  unletValue l astBindings primalBody =
    unletAst6 astBindings l primalBody

instance DerivativeStages (AstShaped FullSpan) where
  forwardPassByInterpretation
    :: (GoodScalar r, Sh.Shape sh)
    => (Domains (AstRanked FullSpan) -> AstShaped FullSpan r sh)
    -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
    -> Domains (AstRanked PrimalSpan)
    -> [AstDynamicVarName]
    -> Domains (AstRanked FullSpan)
    -> ADVal (AstShaped PrimalSpan) r sh
  {-# INLINE forwardPassByInterpretation #-}
  forwardPassByInterpretation g envInit domainsPrimal vars domains =
    let deltaInputs = generateDeltaInputs domainsPrimal
        varInputs = makeADInputs domainsPrimal deltaInputs
        ast = g domains
        env = foldr extendEnvD envInit $ zip vars $ V.toList varInputs
    in interpretAstS env ast

  revArtifactFromForwardPass
    :: forall r sh. (GoodScalar r, Sh.Shape sh)
    => TensorToken (AstShaped FullSpan) -> Bool
    -> (Domains (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> Domains (AstRanked FullSpan)
        -> ADVal (AstShaped PrimalSpan) r sh)
    -> DomainsOD
    -> ( AstArtifactRev (AstShaped PrimalSpan) r sh
       , Dual (AstShaped PrimalSpan) r sh )
  {-# INLINE revArtifactFromForwardPass #-}
  revArtifactFromForwardPass _ hasDt forwardPass parameters0 =
    let !(!varDtId, varsPrimal, domainsPrimal, vars, domains) =
          funToAstRev parameters0 in
    let !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
    let varDt = AstVarName varDtId
        astDt = AstVarS varDt
        mdt = if hasDt then Just astDt else Nothing
        !(!astBindings, !gradient) =
          reverseDervative parameters0 primalBody mdt delta
        unGradient = unletGradient @[Nat] @(AstShaped PrimalSpan)
                                 l astBindings gradient
        unPrimal = unletValue l [] primalBody
    in ( ((varDt, varsPrimal), unGradient, unPrimal, Sh.shapeT @sh)
       , delta )

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varDt, vars), gradient, primal, _) parameters mdt =
    let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe 1 mdt
        envDt = extendEnvS varDt dt env
        gradientDomain = interpretAstDomains envDt gradient
        primalTensor = interpretAstPrimalS env primal
    in (gradientDomain, primalTensor)

  fwdArtifactFromForwardPass
    :: forall r sh. (GoodScalar r, Sh.Shape sh)
    => TensorToken (AstShaped FullSpan)
    -> (Domains (AstRanked PrimalSpan)
        -> [AstDynamicVarName]
        -> Domains (AstRanked FullSpan)
        -> ADVal (AstShaped PrimalSpan) r sh)
    -> DomainsOD
    -> ( AstArtifactFwd (AstShaped PrimalSpan) r sh
       , Dual (AstShaped PrimalSpan) r sh )
  {-# INLINE fwdArtifactFromForwardPass #-}
  fwdArtifactFromForwardPass _ forwardPass parameters0 =
    let !(!varsPrimalDs, domainsDs, varsPrimal, domainsPrimal, vars, domains) =
          funToAstFwd parameters0 in
    let !(D l primalBody delta) = forwardPass domainsPrimal vars domains  in
    let !(!astBindings, !derivative) =
          forwardDerivative (V.length parameters0) delta domainsDs
        unDerivative = unletValue l astBindings derivative
        unPrimal = unletValue l [] primalBody
    in ( ((varsPrimalDs, varsPrimal), unDerivative, unPrimal)
       , delta )

  {-# INLINE fwdEvalArtifact #-}
  fwdEvalArtifact ((varDs, vars), derivative, primal) parameters ds =
    if domainsMatch parameters ds then
      let env = foldr extendEnvD EM.empty $ zip vars $ V.toList parameters
          envDs = foldr extendEnvD env $ zip varDs $ V.toList ds
          derivativeTensor = interpretAstPrimalS envDs derivative
          primalTensor = interpretAstPrimalS @(Flip OR.Array) env primal
      in (derivativeTensor, primalTensor)
   else error "fwdEvalArtifact: forward derivative input and sensitivity arguments should have same shapes"

instance UnletGradient (AstShaped PrimalSpan) where
  unletGradient
    :: ADShare -> AstBindings -> Domains (AstRanked PrimalSpan)
    -> AstDomains PrimalSpan
  unletGradient l astBindings gradient =
    unletAstDomains6 astBindings l
                     (dmkDomains @(AstRanked PrimalSpan) gradient)
  unletValue
    :: (GoodScalar r,  Sh.Shape sh)
    => ADShare -> AstBindings -> AstShaped PrimalSpan r sh
    -> AstShaped PrimalSpan r sh
  unletValue l astBindings primalBody =
   unletAst6S astBindings l primalBody


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

instance AstSpan s
         => RankedTensor (AstRanked s) where
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
  rletDomainsIn = astLetDomainsInFun
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
  rregister = astRegisterFun

  rconstant = fromPrimal
  rprimalPart = astSpanPrimal
  rdualPart = astSpanDual
  rD = astSpanD
  rScale s t = astDualPart $ AstConstant s * AstD (rzero (rshape s)) t

instance ( GoodScalar r, KnownNat n
         , RankedTensor (AstRanked s) )
         => AdaptableDomains (AstRanked s) (AstRanked s r n) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableDomains (AstRanked s) (AstRanked s Double n) #-}
  type Value (AstRanked s r n) = Flip OR.Array r n
  toDomains = undefined
  fromDomains _aInit params = fromDomainsR @r @n params

astLetDomainsInFun
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => DomainsOD -> AstDomains s -> (Domains (AstRanked s) -> AstRanked s r n)
  -> AstRanked s r n
{-# INLINE astLetDomainsInFun #-}
astLetDomainsInFun a0 a f =
  fun1DToAst a0 $ \vars asts -> astLetDomainsIn vars a (f asts)

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

instance AstSpan s
         => ShapedTensor (AstShaped s) where
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
  sletDomainsIn = astLetDomainsInFunS
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
  sregister = astRegisterFunS

  sconstant = fromPrimalS
  sprimalPart = astSpanPrimalS
  sdualPart = astSpanDualS
  sD = astSpanDS
  sScale s t = astDualPartS $ AstConstantS s * AstDS 0 t

instance ( GoodScalar r, Sh.Shape sh
         , ShapedTensor (AstShaped s) )
         => AdaptableDomains (AstRanked s) (AstShaped s r sh) where
  type Value (AstShaped s r sh) = Flip OS.Array r sh
  toDomains = undefined
  fromDomains _aInit params = fromDomainsS @r @sh params

astLetDomainsInFunS
  :: forall sh s r. (Sh.Shape sh, GoodScalar r, AstSpan s)
  => DomainsOD -> AstDomains s -> (Domains (AstRanked s) -> AstShaped s r sh)
  -> AstShaped s r sh
{-# INLINE astLetDomainsInFunS #-}
astLetDomainsInFunS a0 a f =
  fun1DToAst a0 $ \vars asts -> astLetDomainsInS vars a (f asts)

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


-- * DomainsTensor instance

instance AstSpan s => DomainsTensor (AstRanked s) (AstShaped s) where
  dmkDomains = AstDomains
  dunDomains domsOD domainsOf =
    let f :: Int -> DynamicTensor (Flip OR.Array) -> AstDynamic s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListShape (Sh.shapeT @sh) $ \(_ :: ShapeInt n) ->
              DynamicRanked @r @n
              $ rletDomainsIn @(AstRanked s) domsOD domainsOf (rfromD . (V.! i))
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh
            $ sletDomainsIn @(AstShaped s) domsOD domainsOf (sfromD . (V.! i))
          _ -> error "dunDomains: unexpected OD value"
    in V.imap f domsOD
  dletDomainsInDomains = astLetDomainsInDomainsFun
  rletInDomains = astLetInDomainsFun
  sletInDomains = astLetInDomainsFunS
  dregister domsOD r l =
    fun1DToAst domsOD $ \vars asts -> (AstBindingsDomains vars r : l, asts)
  dbuild1 = astBuildDomains1Vectorize
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains f -> f r n)
       -> DomainsOD
       -> Domains (AstRanked s)
       -> AstDomains s
  rrev f parameters0 =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new @parmeters@, which is much better than computing anew.
    let (((_varDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken False (f @(AstRanked FullSpan))
                             EM.empty parameters0
    in \parameters -> assert (domainsMatch parameters0 parameters) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
      in interpretAstDomains env gradient
        -- this interpretation both substitutes parameters for the variables and
        -- reinterprets @PrimalSpan@ terms in @s@ terms;
        -- we could shortcut when @s@ is @PrimalSpan@ and @parameters@
        -- are the same variables, but it's a very special case
  rrevDt :: (GoodScalar r, KnownNat n)
         => (forall f. ADReady f => Domains f -> f r n)
         -> DomainsOD
         -> Domains (AstRanked s)
         -> AstRanked s r n
         -> AstDomains s
  rrevDt f parameters0 =
    let (((varDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken True (f @(AstRanked FullSpan))
                             EM.empty parameters0
    in \parameters dt -> assert (domainsMatch parameters0 parameters) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
          envDt = extendEnvR varDt dt env
      in interpretAstDomains envDt gradient
  rfwd :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains f -> f r n)
       -> DomainsOD
       -> Domains (AstRanked s)
       -> Domains (AstRanked s)
       -> AstRanked s r n
  rfwd f parameters0 =
    let (((varsDt, vars), derivative, _primal), _delta) =
          fwdProduceArtifact TensorToken (f @(AstRanked FullSpan))
                             EM.empty parameters0
    in \parameters ds -> assert (domainsMatch parameters0 parameters) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
          envDt = extendEnvPars @(AstRanked s) varsDt ds env
      in interpretAst envDt derivative
  srev f parameters0 =
    let (((_varDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken False (f @(AstShaped FullSpan))
                             EM.empty parameters0
    in \parameters -> assert (domainsMatch parameters0 parameters) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
      in interpretAstDomains env gradient
  srevDt f parameters0 =
    let (((varDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact TensorToken True (f @(AstShaped FullSpan))
                             EM.empty parameters0
    in \parameters dt -> assert (domainsMatch parameters0 parameters) $
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
          envDt = extendEnvS varDt dt env
      in interpretAstDomains envDt gradient
  sfwd f parameters0 =
    let (((varsDt, vars), derivative, _primal), _delta) =
          fwdProduceArtifact TensorToken (f @(AstShaped FullSpan))
                             EM.empty parameters0
    in \parameters ds -> assert (domainsMatch parameters0 parameters) $
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
        domsF = V.fromList [odFromSh @rn shn, odFromSh @rm shm]
        domsToPair :: forall f. ADReady f => Domains f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: Domains (AstRanked FullSpan) -> AstRanked FullSpan rn n
        g doms = uncurry f (domsToPair doms)
    in -- This computes the (AST of) derivative of f once for each @x0@
       -- and @as@, which is better than once for each @a@. We could compute
       -- it once per @f@ if we took shapes as arguments. The @sfold@ operation
       -- can do that thanks to shapes being available from types.
       case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varDt, [AstDynamicVarName nid, AstDynamicVarName mid])
        , gradient, _primal, _sh), _delta ) ->
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( [AstDynamicVarName nid1, AstDynamicVarName mid1]
              , [AstDynamicVarName nid2, AstDynamicVarName mid2] )
            , derivative, _primal), _delta ) ->
            let (nvar1, mvar1) = (AstVarName nid1, AstVarName mid1)
                (nvar2, mvar2) = (AstVarName nid2, AstVarName mid2)
                (nvar, mvar) = (AstVarName nid, AstVarName mid)
            in AstFoldDer (fun2ToAstR shn shm f)
                          (nvar1, mvar1, nvar2, mvar2, derivative)
                          (varDt, nvar, mvar, gradient)
                          x0 as
          _ -> error "rfold: wrong variables"
      _ -> error "rfold: wrong variables"
  rfoldDer :: forall rn rm n m.
              (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
           -> AstRanked s rn n
           -> AstRanked s rm (1 + m)
           -> AstRanked s rn n
  rfoldDer f df rf x0 as =
    let shn = rshape x0
        shm = tailShape $ rshape as
    in AstFoldDer (fun2ToAstR shn shm f) (fun4ToAstR shn shm df)
                  (fun3ToAstR shn shm rf) x0 as
  rfoldZip :: forall rn n. (GoodScalar rn, KnownNat n)
         => (forall f. ADReady f => f rn n -> DomainsOf f -> f rn n)
         -> DomainsOD
         -> AstRanked s rn n
         -> Domains (AstRanked s)
         -> AstRanked s rn n
  rfoldZip f domsOD x0 as =
    assert (domainsMatch domsOD (index1Domains as 0)) $
    let shn = rshape x0
        domsF = V.cons (odFromSh @rn shn) domsOD
        domsToPair :: forall f. ADReady f => Domains f -> (f rn n, DomainsOf f)
        domsToPair doms = (rfromD $ doms V.! 0, dmkDomains $ V.tail doms)
        g :: Domains (AstRanked FullSpan) -> AstRanked FullSpan rn n
        g doms = uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varDt, AstDynamicVarName nid : mdyns)
        , gradient, _primal, _sh), _delta ) ->
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( AstDynamicVarName nid1 : mdyns1
              , AstDynamicVarName nid2 : mdyns2 )
            , derivative, _primal), _delta ) ->
            let nvar1 = AstVarName nid1
                nvar2 = AstVarName nid2
                nvar = AstVarName nid
            in AstFoldZipDer (fun2DToAstR shn f domsOD)
                             (nvar1, mdyns1, nvar2, mdyns2, derivative)
                             (varDt, nvar, mdyns, gradient)
                             x0 as
          _ -> error "rfoldD: wrong variables"
      _ -> error "rfoldD: wrong variables"
  rfoldZipDer :: forall rn n. (GoodScalar rn, KnownNat n)
            => (forall f. ADReady f => f rn n -> DomainsOf f -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> DomainsOf f -> f rn n -> DomainsOf f
                -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> f rn n -> DomainsOf f
                -> DomainsOf f)
            -> DomainsOD
            -> AstRanked s rn n
            -> Domains (AstRanked s)
            -> AstRanked s rn n
  rfoldZipDer f df rf domsOD x0 as =
    assert (domainsMatch domsOD (index1Domains as 0)) $
    let shn = rshape x0
    in AstFoldZipDer (fun2DToAstR shn f domsOD)
                     (fun4DToAstR shn df domsOD)
                     (fun3DToAstR shn rf domsOD) x0 as
  rscan :: forall rn rm n m.
           (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
        => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
        -> AstRanked s rn n
        -> AstRanked s rm (1 + m)
        -> AstRanked s rn (1 + n)
  rscan f x0 as =
    let shn = rshape x0
        shm = tailShape $ rshape as
        domsF = V.fromList [odFromSh @rn shn, odFromSh @rm shm]
        domsToPair :: forall f. ADReady f => Domains f -> (f rn n, f rm m)
        domsToPair doms = (rfromD $ doms V.! 0, rfromD $ doms V.! 1)
        g :: Domains (AstRanked FullSpan) -> AstRanked FullSpan rn n
        g doms = uncurry f (domsToPair doms)
    in -- This computes the (AST of) derivative of f once for each @x0@
       -- and @as@, which is better than once for each @a@. We could compute
       -- it once per @f@ if we took shapes as arguments. The @sfold@ operation
       -- can do that thanks to shapes being available from types.
       case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varDt, [AstDynamicVarName nid, AstDynamicVarName mid])
        , gradient, _primal, _sh), _delta ) ->
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( [AstDynamicVarName nid1, AstDynamicVarName mid1]
              , [AstDynamicVarName nid2, AstDynamicVarName mid2] )
            , derivative, _primal), _delta ) ->
            let (nvar1, mvar1) = (AstVarName nid1, AstVarName mid1)
                (nvar2, mvar2) = (AstVarName nid2, AstVarName mid2)
                (nvar, mvar) = (AstVarName nid, AstVarName mid)
            in AstScanDer (fun2ToAstR shn shm f)
                          (nvar1, mvar1, nvar2, mvar2, derivative)
                          (varDt, nvar, mvar, gradient)
                          x0 as
          _ -> error "rscan: wrong variables"
      _ -> error "rscan: wrong variables"
  rscanDer :: forall rn rm n m.
              (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
           => (forall f. ADReady f => f rn n -> f rm m -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rm m -> f rn n -> f rm m
                                   -> f rn n)
           -> (forall f. ADReady f => f rn n -> f rn n -> f rm m -> DomainsOf f)
           -> AstRanked s rn n
           -> AstRanked s rm (1 + m)
           -> AstRanked s rn (1 + n)
  rscanDer f df rf x0 as =
    let shn = rshape x0
        shm = tailShape $ rshape as
    in AstScanDer (fun2ToAstR shn shm f)
                  (fun4ToAstR shn shm df)
                  (fun3ToAstR shn shm rf) x0 as
  rscanZip :: forall rn n. (GoodScalar rn, KnownNat n)
         => (forall f. ADReady f => f rn n -> DomainsOf f -> f rn n)
         -> DomainsOD
         -> AstRanked s rn n
         -> Domains (AstRanked s)
         -> AstRanked s rn (1 + n)
  rscanZip f domsOD x0 as =
    assert (domainsMatch domsOD (index1Domains as 0)) $
    let shn = rshape x0
        domsF = V.cons (odFromSh @rn shn) domsOD
        domsToPair :: forall f. ADReady f => Domains f -> (f rn n, DomainsOf f)
        domsToPair doms = (rfromD $ doms V.! 0, dmkDomains $ V.tail doms)
        g :: Domains (AstRanked FullSpan) -> AstRanked FullSpan rn n
        g doms = uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varDt, AstDynamicVarName nid : mdyns)
        , gradient, _primal, _sh), _delta ) ->
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( AstDynamicVarName nid1 : mdyns1
              , AstDynamicVarName nid2 : mdyns2 )
            , derivative, _primal), _delta ) ->
            let nvar1 = AstVarName nid1
                nvar2 = AstVarName nid2
                nvar = AstVarName nid
            in AstScanZipDer (fun2DToAstR shn f domsOD)
                             (nvar1, mdyns1, nvar2, mdyns2, derivative)
                             (varDt, nvar, mdyns, gradient)
                             x0 as
          _ -> error "rscanD: wrong variables"
      _ -> error "rscanD: wrong variables"
  rscanZipDer :: forall rn n. (GoodScalar rn, KnownNat n)
            => (forall f. ADReady f => f rn n -> DomainsOf f -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> DomainsOf f -> f rn n -> DomainsOf f
                -> f rn n)
            -> (forall f. ADReady f
                => f rn n -> f rn n -> DomainsOf f
                -> DomainsOf f)
            -> DomainsOD
            -> AstRanked s rn n
            -> Domains (AstRanked s)
            -> AstRanked s rn (1 + n)
  rscanZipDer f df rf domsOD x0 as =
    assert (domainsMatch domsOD (index1Domains as 0)) $
    let shn = rshape x0
    in AstScanZipDer (fun2DToAstR shn f domsOD)
                     (fun4DToAstR shn df domsOD)
                     (fun3DToAstR shn rf domsOD) x0 as
  sfold :: forall rn rm sh shm k.
           (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> AstShaped s rn sh
        -> AstShaped s rm (k ': shm)
        -> AstShaped s rn sh
  sfold f x0 as =
    let domsF = V.fromList [odFromShS @rn @sh, odFromShS @rm @shm]
        domsToPair :: forall f. ADReadyS f
                   => Domains (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        g :: Domains (AstRanked FullSpan) -> AstShaped FullSpan rn sh
        g doms = uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varDt, [AstDynamicVarName nid, AstDynamicVarName mid])
        , gradient, _primal, _sh), _delta ) ->
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( [AstDynamicVarName nid1, AstDynamicVarName mid1]
              , [AstDynamicVarName nid2, AstDynamicVarName mid2] )
            , derivative, _primal), _delta ) ->
            let (nvar1, mvar1) = (AstVarName nid1, AstVarName mid1)
                (nvar2, mvar2) = (AstVarName nid2, AstVarName mid2)
                (nvar, mvar) = (AstVarName nid, AstVarName mid)
            in AstFoldDerS (fun2ToAstS f)
                           (nvar1, mvar1, nvar2, mvar2, derivative)
                           (varDt, nvar, mvar, gradient)
                           x0 as
          _ -> error "sfold: wrong variables"
      _ -> error "sfold: wrong variables"
  sfoldDer :: forall rn rm sh shm k. (GoodScalar rm, Sh.Shape shm, KnownNat k)
           => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rm shm -> f rn sh -> f rm shm
               -> f rn sh)
           -> (forall f. ADReadyS f
               => f rn sh -> f rn sh -> f rm shm -> DomainsOf (RankedOf f))
           -> AstShaped s rn sh
           -> AstShaped s rm (k ': shm)
           -> AstShaped s rn sh
  sfoldDer f df rf x0 as =
    AstFoldDerS (fun2ToAstS f) (fun4ToAstS df) (fun3ToAstS rf) x0 as
  sfoldZip :: forall rn sh. (GoodScalar rn, Sh.Shape sh)
         => (forall f. ADReadyS f
             => f rn sh -> DomainsOf (RankedOf f) -> f rn sh)
         -> DomainsOD
         -> AstShaped s rn sh
         -> Domains (AstRanked s)
         -> AstShaped s rn sh
  sfoldZip f domsOD x0 as =
    assert (domainsMatch domsOD (index1Domains as 0)) $
    let domsF = V.cons (odFromShS @rn @sh) domsOD
        domsToPair :: forall f. ADReadyS f
                      => Domains (RankedOf f)
                      -> (f rn sh, DomainsOf (RankedOf f))
        domsToPair doms = (sfromD $ doms V.! 0, dmkDomains $ V.tail doms)
        g :: Domains (AstRanked FullSpan) -> AstShaped FullSpan rn sh
        g doms = uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varDt, AstDynamicVarName nid : mdyns)
        , gradient, _primal, _sh), _delta ) ->
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( AstDynamicVarName nid1 : mdyns1
              , AstDynamicVarName nid2 : mdyns2 )
            , derivative, _primal), _delta ) ->
            let nvar1 = AstVarName nid1
                nvar2 = AstVarName nid2
                nvar = AstVarName nid
            in AstFoldZipDerS (fun2DToAstS @_ @_ @sh f domsOD)
                              (nvar1, mdyns1, nvar2, mdyns2, derivative)
                              (varDt, nvar, mdyns, gradient)
                              x0 as
          _ -> error "sfoldD: wrong variables"
      _ -> error "sfoldD: wrong variables"
  sfoldZipDer :: forall rn sh. Sh.Shape sh
            => (forall f. ADReadyS f
                => f rn sh -> DomainsOf (RankedOf f) -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> DomainsOf (RankedOf f) -> f rn sh
                -> DomainsOf (RankedOf f)
                -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> f rn sh -> DomainsOf (RankedOf f)
                -> DomainsOf (RankedOf f))
            -> DomainsOD
            -> AstShaped s rn sh
            -> Domains (AstRanked s)
            -> AstShaped s rn sh
  sfoldZipDer f df rf domsOD x0 as =
    assert (domainsMatch domsOD (index1Domains as 0)) $
    AstFoldZipDerS (fun2DToAstS @_ @_ @sh f domsOD)
                   (fun4DToAstS @_ @_ @sh df domsOD)
                   (fun3DToAstS @_ @_ @sh rf domsOD) x0 as
  sscan :: forall rn rm sh shm k.
           (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm, KnownNat k)
        => (forall f. ADReadyS f => f rn sh -> f rm shm -> f rn sh)
        -> AstShaped s rn sh
        -> AstShaped s rm (k ': shm)
        -> AstShaped s rn (1 + k ': sh)
  sscan f x0 as =
    let domsF = V.fromList [odFromShS @rn @sh, odFromShS @rm @shm]
        domsToPair :: forall f. ADReadyS f
                   => Domains (RankedOf f) -> (f rn sh, f rm shm)
        domsToPair doms = (sfromD $ doms V.! 0, sfromD $ doms V.! 1)
        g :: Domains (AstRanked FullSpan) -> AstShaped FullSpan rn sh
        g doms = uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varDt, [AstDynamicVarName nid, AstDynamicVarName mid])
        , gradient, _primal, _sh), _delta ) ->
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( [AstDynamicVarName nid1, AstDynamicVarName mid1]
              , [AstDynamicVarName nid2, AstDynamicVarName mid2] )
            , derivative, _primal), _delta ) ->
            let (nvar1, mvar1) = (AstVarName nid1, AstVarName mid1)
                (nvar2, mvar2) = (AstVarName nid2, AstVarName mid2)
                (nvar, mvar) = (AstVarName nid, AstVarName mid)
            in AstScanDerS (fun2ToAstS @_ @_ @sh f)
                           (nvar1, mvar1, nvar2, mvar2, derivative)
                           (varDt, nvar, mvar, gradient)
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
               => f rn sh -> f rn sh -> f rm shm -> DomainsOf (RankedOf f))
           -> AstShaped s rn sh
           -> AstShaped s rm (k ': shm)
           -> AstShaped s rn (1 + k ': sh)
  sscanDer f df rf x0 as =
    AstScanDerS (fun2ToAstS @_ @_ @sh f)
                (fun4ToAstS @_ @_ @sh df)
                (fun3ToAstS @_ @_ @sh rf) x0 as
  sscanZip :: forall k rn sh. (GoodScalar rn, Sh.Shape sh, KnownNat k)
         => (forall f. ADReadyS f
             => f rn sh -> DomainsOf (RankedOf f) -> f rn sh)
         -> DomainsOD
         -> AstShaped s rn sh
         -> Domains (AstRanked s)
         -> AstShaped s rn (1 + k ': sh)
  sscanZip f domsOD x0 as =
    assert (domainsMatch domsOD (index1Domains as 0)) $
    let domsF = V.cons (odFromShS @rn @sh) domsOD
        domsToPair :: forall f. ADReadyS f
                      => Domains (RankedOf f)
                      -> (f rn sh, DomainsOf (RankedOf f))
        domsToPair doms = (sfromD $ doms V.! 0, dmkDomains $ V.tail doms)
        g :: Domains (AstRanked FullSpan) -> AstShaped FullSpan rn sh
        g doms = uncurry f (domsToPair doms)
    in case revProduceArtifact TensorToken True g EM.empty domsF of
      ( ( (varDt, AstDynamicVarName nid : mdyns)
        , gradient, _primal, _sh), _delta ) ->
        case fwdProduceArtifact TensorToken g EM.empty domsF of
          ( ( ( AstDynamicVarName nid1 : mdyns1
              , AstDynamicVarName nid2 : mdyns2 )
            , derivative, _primal), _delta ) ->
            let nvar1 = AstVarName nid1
                nvar2 = AstVarName nid2
                nvar = AstVarName nid
            in AstScanZipDerS (fun2DToAstS @_ @_ @sh f domsOD)
                              (nvar1, mdyns1, nvar2, mdyns2, derivative)
                              (varDt, nvar, mdyns, gradient)
                              x0 as
          _ -> error "sscanD: wrong variables"
      _ -> error "sscanD: wrong variables"
  sscanZipDer :: forall k rn sh. (Sh.Shape sh, KnownNat k)
            => (forall f. ADReadyS f
                => f rn sh -> DomainsOf (RankedOf f) -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> DomainsOf (RankedOf f) -> f rn sh
                -> DomainsOf (RankedOf f)
                -> f rn sh)
            -> (forall f. ADReadyS f
                => f rn sh -> f rn sh -> DomainsOf (RankedOf f)
                -> DomainsOf (RankedOf f))
            -> DomainsOD
            -> AstShaped s rn sh
            -> Domains (AstRanked s)
            -> AstShaped s rn (1 + k ': sh)
  sscanZipDer f df rf domsOD x0 as =
    assert (domainsMatch domsOD (index1Domains as 0)) $
    AstScanZipDerS (fun2DToAstS @_ @_ @sh f domsOD)
                   (fun4DToAstS @_ @_ @sh df domsOD)
                   (fun3DToAstS @_ @_ @sh rf domsOD) x0 as

astLetDomainsInDomainsFun
  :: AstSpan s
  => DomainsOD -> AstDomains s -> (Domains (AstRanked s) -> AstDomains s)
  -> AstDomains s
{-# INLINE astLetDomainsInDomainsFun #-}
astLetDomainsInDomainsFun a0 a f =
  fun1DToAst a0 $ \vars asts -> astLetDomainsInDomains vars a (f asts)

astLetInDomainsFun :: (KnownNat n, GoodScalar r, AstSpan s)
                   => AstRanked s r n -> (AstRanked s r n -> AstDomains s)
                   -> AstDomains s
{-# NOINLINE astLetInDomainsFun #-}
astLetInDomainsFun a f | astIsSmall True a = f a
astLetInDomainsFun a f = unsafePerformIO $ do  -- the id causes trouble
  let sh = shapeAst a
  (!var, _, !ast) <- funToAstIOR sh id
  return $! astLetInDomains var a (f ast)
              -- safe because subsitution ruled out above

astLetInDomainsFunS :: (Sh.Shape sh, GoodScalar r, AstSpan s)
                    => AstShaped s r sh -> (AstShaped s r sh -> AstDomains s)
                    -> AstDomains s
{-# NOINLINE astLetInDomainsFunS #-}
astLetInDomainsFunS a f | astIsSmallS True a = f a
astLetInDomainsFunS a f = unsafePerformIO $ do  -- the id causes trouble
  (!var, _, !ast) <- funToAstIOS id
  return $! astLetInDomainsS var a (f ast)
              -- safe because subsitution ruled out above

astBuildDomains1Vectorize
  :: AstSpan s
  => Int -> (AstInt -> AstDomains s) -> AstDomains s
astBuildDomains1Vectorize k f = build1VectorizeDomains k $ funToAstI f


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

instance AstSpan s
         => RankedTensor (AstNoVectorize s) where
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
  rletDomainsIn a0 a f =
    AstNoVectorize $ astLetDomainsInFun
                       a0 a (unAstNoVectorize . f . noVectorizeDomains)
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
  sletDomainsIn a0 a f =
    AstNoVectorizeS $ astLetDomainsInFunS
                        a0 a (unAstNoVectorizeS . f . noVectorizeDomains)
  sfromR = AstNoVectorizeS . sfromR @(AstShaped s) . unAstNoVectorize

  sconstant = AstNoVectorizeS . fromPrimalS
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  sprimalPart = astSpanPrimalS . unAstNoVectorizeS
  sdualPart = astSpanDualS . unAstNoVectorizeS
  sD u u' = AstNoVectorizeS $ astSpanDS u u'
  sScale s t = astDualPartS $ AstConstantS s * AstDS 0 t

instance AstSpan s => DomainsTensor (AstNoVectorize s) (AstNoVectorizeS s) where
  dmkDomains domains = dmkDomains @(AstRanked s) (unNoVectorizeDomains domains)
  dunDomains parameters0 doms =
    noVectorizeDomains $ dunDomains @(AstRanked s) parameters0 doms
  dletDomainsInDomains a0 a f =
    astLetDomainsInDomainsFun a0 a (f . noVectorizeDomains)
  rletInDomains u f =
    rletInDomains @(AstRanked s) (unAstNoVectorize u) (f . AstNoVectorize)
  sletInDomains u f =
    sletInDomains @(AstRanked s) (unAstNoVectorizeS u) (f . AstNoVectorizeS)
  dregister = error "dregister for AstNoVectorize"
  dbuild1 k f = AstBuildDomains1 k $ funToAstI f
  rrev f parameters0 domains =
    rrev @(AstRanked s) f parameters0 (unNoVectorizeDomains domains)
  rrevDt f parameters0 domains dt =
    rrevDt @(AstRanked s) f parameters0
           (unNoVectorizeDomains domains) (unAstNoVectorize dt)
  rfwd f parameters0 domains ds =
    AstNoVectorize
    $ rfwd @(AstRanked s) f parameters0
           (unNoVectorizeDomains domains) (unNoVectorizeDomains ds)
  srev f parameters0 domains =
    srev @(AstRanked s) f parameters0 (unNoVectorizeDomains domains)
  srevDt f parameters0 domains dt =
    srevDt @(AstRanked s) f parameters0
           (unNoVectorizeDomains domains) (unAstNoVectorizeS dt)
  sfwd f parameters0 domains ds =
    AstNoVectorizeS
    $ sfwd @(AstRanked s) f parameters0
           (unNoVectorizeDomains domains) (unNoVectorizeDomains ds)
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
                                     (unNoVectorizeDomains as)
  rfoldZipDer f df rf domsOD x0 as =
    AstNoVectorize
    $ rfoldZipDer @(AstRanked s)
                f df rf domsOD (unAstNoVectorize x0) (unNoVectorizeDomains as)
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
                                     (unNoVectorizeDomains as)
  rscanZipDer f df rf domsOD x0 as =
    AstNoVectorize
    $ rscanZipDer @(AstRanked s)
                f df rf domsOD (unAstNoVectorize x0) (unNoVectorizeDomains as)
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
                                     (unNoVectorizeDomains as)
  sfoldZipDer f df rf domsOD x0 as =
    AstNoVectorizeS
    $ sfoldZipDer @(AstRanked s)
                f df rf domsOD (unAstNoVectorizeS x0) (unNoVectorizeDomains as)
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
                                     (unNoVectorizeDomains as)
  sscanZipDer f df rf domsOD x0 as =
    AstNoVectorizeS
    $ sscanZipDer @(AstRanked s)
                f df rf domsOD (unAstNoVectorizeS x0) (unNoVectorizeDomains as)

unNoVectorizeDomains :: Domains (AstNoVectorize s) -> Domains (AstRanked s)
unNoVectorizeDomains =
  let f (DynamicRanked (AstNoVectorize t)) = DynamicRanked t
      f (DynamicShaped (AstNoVectorizeS t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noVectorizeDomains :: Domains (AstRanked s) -> Domains (AstNoVectorize s)
noVectorizeDomains =
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
  rletDomainsIn a0 a f =
    AstNoSimplify $ astLetDomainsInFun
                      a0 a (unAstNoSimplify . f . noSimplifyDomains)
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
  sletDomainsIn a0 a f =
    AstNoSimplifyS $ astLetDomainsInFunS
                       a0 a (unAstNoSimplifyS . f . noSimplifyDomains)
  sfromR = AstNoSimplifyS . sfromR @(AstShaped s) . unAstNoSimplify

  sconstant = AstNoSimplifyS . fromPrimalS
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  sprimalPart = astSpanPrimalS . unAstNoSimplifyS
  sdualPart = astSpanDualS . unAstNoSimplifyS
  sD u u' = AstNoSimplifyS $ astSpanDS u u'
  sScale s t = astDualPartS $ AstConstantS s * AstDS 0 t

instance AstSpan s => DomainsTensor (AstNoSimplify s) (AstNoSimplifyS s) where
  dmkDomains domains = dmkDomains @(AstRanked s) (unNoSimplifyDomains domains)
  dunDomains parameters0 doms =
    noSimplifyDomains $ dunDomains @(AstRanked s) parameters0 doms
  dletDomainsInDomains a0 a f =
    astLetDomainsInDomainsFun a0 a (f . noSimplifyDomains)
  rletInDomains u f =
    rletInDomains @(AstRanked s) (unAstNoSimplify u) (f . AstNoSimplify)
  sletInDomains u f =
    sletInDomains @(AstRanked s) (unAstNoSimplifyS u) (f . AstNoSimplifyS)
  dregister = error "dregister for AstNoSimplify"
  dbuild1 = astBuildDomains1Vectorize
  rrev f parameters0 domains =
    rrev @(AstRanked s) f parameters0 (unNoSimplifyDomains domains)
  rrevDt f parameters0 domains dt =
    rrevDt @(AstRanked s) f parameters0
           (unNoSimplifyDomains domains) (unAstNoSimplify dt)
  rfwd f parameters0 domains ds =
    AstNoSimplify $ rfwd @(AstRanked s) f parameters0
                         (unNoSimplifyDomains domains) (unNoSimplifyDomains ds)
  srev f parameters0 domains =
    srev @(AstRanked s) f parameters0 (unNoSimplifyDomains domains)
  srevDt f parameters0 domains dt =
    srevDt @(AstRanked s) f parameters0
           (unNoSimplifyDomains domains) (unAstNoSimplifyS dt)
  sfwd f parameters0 domains ds =
    AstNoSimplifyS $ sfwd @(AstRanked s) f parameters0
                          (unNoSimplifyDomains domains) (unNoSimplifyDomains ds)
  rfold f x0 as =
    AstNoSimplify
    $ rfold @(AstRanked s) f (unAstNoSimplify x0) (unAstNoSimplify as)
  rfoldDer f df rf x0 as =
    AstNoSimplify
    $ rfoldDer @(AstRanked s) f df rf (unAstNoSimplify x0) (unAstNoSimplify as)
  rfoldZip f domsOD x0 as =
    AstNoSimplify
    $ rfoldZip @(AstRanked s) f domsOD (unAstNoSimplify x0)
                                     (unNoSimplifyDomains as)
  rfoldZipDer f df rf domsOD x0 as =
    AstNoSimplify
    $ rfoldZipDer @(AstRanked s)
                f df rf domsOD (unAstNoSimplify x0) (unNoSimplifyDomains as)
  rscan f x0 as =
    AstNoSimplify
    $ rscan @(AstRanked s) f (unAstNoSimplify x0) (unAstNoSimplify as)
  rscanDer f df rf x0 as =
    AstNoSimplify
    $ rscanDer @(AstRanked s) f df rf (unAstNoSimplify x0) (unAstNoSimplify as)
  rscanZip f domsOD x0 as =
    AstNoSimplify
    $ rscanZip @(AstRanked s) f domsOD (unAstNoSimplify x0)
                                     (unNoSimplifyDomains as)
  rscanZipDer f df rf domsOD x0 as =
    AstNoSimplify
    $ rscanZipDer @(AstRanked s)
                f df rf domsOD (unAstNoSimplify x0) (unNoSimplifyDomains as)
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
                                     (unNoSimplifyDomains as)
  sfoldZipDer f df rf domsOD x0 as =
    AstNoSimplifyS
    $ sfoldZipDer @(AstRanked s)
                f df rf domsOD (unAstNoSimplifyS x0) (unNoSimplifyDomains as)
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
                                     (unNoSimplifyDomains as)
  sscanZipDer f df rf domsOD x0 as =
    AstNoSimplifyS
    $ sscanZipDer @(AstRanked s)
                f df rf domsOD (unAstNoSimplifyS x0) (unNoSimplifyDomains as)

unNoSimplifyDomains :: Domains (AstNoSimplify s) -> Domains (AstRanked s)
unNoSimplifyDomains =
  let f (DynamicRanked (AstNoSimplify t)) = DynamicRanked t
      f (DynamicShaped (AstNoSimplifyS t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noSimplifyDomains :: Domains (AstRanked s) -> Domains (AstNoSimplify s)
noSimplifyDomains =
  let f (DynamicRanked t) = DynamicRanked $ AstNoSimplify t
      f (DynamicShaped t) = DynamicShaped $ AstNoSimplifyS t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f
