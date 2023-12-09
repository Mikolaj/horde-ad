{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
-- | Tensor class instances for AST terms. Most of these instances
-- vectorize any terms starting with the build constructor.
-- The AST term instances can be used as building blocks for 'ADVal'
-- instances defined in "TensorADVal" but may also be used standalone.
module HordeAd.Core.TensorAst
  (
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Int (Int64)
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, sameNat, type (+))
import           Type.Reflection (typeRep)

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
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape)
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
    DToR{} -> d
    SToR{} -> d
    LetR{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaR d

instance (GoodScalar r, OS.Shape sh)
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
    DToS{} -> d
    RToS{} -> d
    LetS{} -> d  -- should not happen, but older/lower id is safer anyway
    _ -> wrapDeltaS d


-- * Reverse and forward derivative stages instances

-- TODO: it's not clear if the instance should be of Clown OD.Array or of
-- DomainsOD, for which we already have unletAstDomains6, etc.;
-- let's wait until we have rev as a function of Tensor class in case
-- that affects rev and/or Delta
--instance DerivativeStages @() (Clown OD.Array) where
--  revEvalArtifact = undefined
--  revProduceArtifact = undefined

instance DerivativeStages (AstRanked FullSpan) where
  forwardPassByInterpretation
    :: (GoodScalar r, KnownNat n)
    => (Domains (AstDynamic FullSpan) -> AstRanked FullSpan r n)
    -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
    -> Domains (AstDynamic PrimalSpan)
    -> [AstDynamicVarName (AstRanked FullSpan)]
    -> Domains (AstDynamic FullSpan)
    -> ADVal (AstRanked PrimalSpan) r n
  {-# INLINE forwardPassByInterpretation #-}
  forwardPassByInterpretation g envInit domainsPrimal vars domains =
    let deltaInputs = generateDeltaInputsAst domainsPrimal
        varInputs = makeADInputs domainsPrimal deltaInputs
        ast = g domains
        env = foldr extendEnvDR envInit $ zip vars $ V.toList varInputs
    in interpretAst env ast

  revArtifactFromForwardPass
    :: forall r n. (GoodScalar r, KnownNat n)
    => Bool
    -> (Domains (AstDynamic PrimalSpan)
        -> [AstDynamicVarName (AstRanked FullSpan)]
        -> Domains (AstDynamic FullSpan)
        -> ADVal (AstRanked PrimalSpan) r n)
    -> DomainsOD
    -> ( AstArtifactRev (AstRanked PrimalSpan) r n
       , Dual (AstRanked PrimalSpan) r n )
  {-# INLINE revArtifactFromForwardPass #-}
  revArtifactFromForwardPass hasDt forwardPass parameters0 =
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
          reverseDervative (V.length parameters0) primalBody mdt delta
    in ( ( (varDt, varsPrimal)
         , unletAstDomains6 astBindings l
                            (dmkDomains @(AstRanked PrimalSpan) gradient)
         , unletAst6 [] l primalBody
         , shapeToList sh )
       , delta )
         -- storing sh computed from primalBody often saves the unletAst6
         -- execution; we could store the whole primalBody, as we do in calls
         -- to reverseDervative, but we can potentially free it earlier this way
         -- (as soon as sh is forced or determined to be unneeded)

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varDt, vars), gradient, primal, sh) parameters mdt =
    let env = foldr extendEnvDR EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe (rreplicate0N (listShapeToShape sh) 1) mdt
        envDt = extendEnvR varDt dt env
        gradientDomain = interpretAstDomains envDt gradient
        primalTensor = interpretAstPrimal env primal
    in (gradientDomain, primalTensor)

  fwdArtifactFromForwardPass
    :: forall r n. (GoodScalar r, KnownNat n)
    => (Domains (AstDynamic PrimalSpan)
        -> [AstDynamicVarName (AstRanked FullSpan)]
        -> Domains (AstDynamic FullSpan)
        -> ADVal (AstRanked PrimalSpan) r n)
    -> DomainsOD
    -> ( AstArtifactFwd (AstRanked PrimalSpan) r n
       , Dual (AstRanked PrimalSpan) r n )
  {-# INLINE fwdArtifactFromForwardPass #-}
  fwdArtifactFromForwardPass forwardPass parameters0 =
    let !(!varsPrimalDs, domainsDs, varsPrimal, domainsPrimal, vars, domains) =
          funToAstFwd parameters0 in
    let !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
    let !(!astBindings, !derivative) =
          forwardDerivative (V.length parameters0) delta domainsDs
    in ( ( (varsPrimalDs, varsPrimal)
         , unletAst6 astBindings l derivative
         , unletAst6 []l primalBody )
       , delta )

  {-# INLINE fwdEvalArtifact #-}
  fwdEvalArtifact ((varDs, vars), derivative, primal) parameters ds =
    if sameShapesDomainsOD parameters ds then
      let env = foldr extendEnvDR EM.empty $ zip vars $ V.toList parameters
          envDs = foldr extendEnvDR env $ zip varDs $ V.toList ds
          derivativeTensor = interpretAstPrimal envDs derivative
          primalTensor = interpretAstPrimal @(Flip OR.Array) env primal
      in (derivativeTensor, primalTensor)
   else error "forward derivative input and sensitivity arguments should have same shapes"

instance DerivativeStages (AstShaped FullSpan) where
  forwardPassByInterpretation
    :: (GoodScalar r, OS.Shape sh)
    => (Domains (AstDynamic FullSpan) -> AstShaped FullSpan r sh)
    -> AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
    -> Domains (AstDynamic PrimalSpan)
    -> [AstDynamicVarName (AstShaped FullSpan)]
    -> Domains (AstDynamic FullSpan)
    -> ADVal (AstShaped PrimalSpan) r sh
  {-# INLINE forwardPassByInterpretation #-}
  forwardPassByInterpretation g envInit domainsPrimal vars domains =
    let deltaInputs = generateDeltaInputsAst domainsPrimal
        varInputs = makeADInputs domainsPrimal deltaInputs
        ast = g domains
        env = foldr extendEnvDS envInit $ zip vars $ V.toList varInputs
    in interpretAstS env ast

  revArtifactFromForwardPass
    :: forall r sh. (GoodScalar r, OS.Shape sh)
    => Bool
    -> (Domains (AstDynamic PrimalSpan)
        -> [AstDynamicVarName (AstShaped FullSpan)]
        -> Domains (AstDynamic FullSpan)
        -> ADVal (AstShaped PrimalSpan) r sh)
    -> DomainsOD
    -> ( AstArtifactRev (AstShaped PrimalSpan) r sh
       , Dual (AstShaped PrimalSpan) r sh )
  {-# INLINE revArtifactFromForwardPass #-}
  revArtifactFromForwardPass hasDt forwardPass parameters0 =
    let !(!varDtId, varsPrimal, domainsPrimal, vars, domains) =
          funToAstRevS parameters0 in
    let !(D l primalBody delta) = forwardPass domainsPrimal vars domains in
    let varDt = AstVarName varDtId
        astDt = AstVarS varDt
        mdt = if hasDt then Just astDt else Nothing
        !(!astBindings, !gradient) =
          reverseDervative (V.length parameters0) primalBody mdt delta
    in ( ( (varDt, varsPrimal)
         , unletAstDomains6 astBindings l
                            (dmkDomains @(AstRanked PrimalSpan) gradient)
         , unletAst6S [] l primalBody
         , OS.shapeT @sh )
       , delta )

  {-# INLINE revEvalArtifact #-}
  revEvalArtifact ((varDt, vars), gradient, primal, _) parameters mdt =
    let env = foldr extendEnvDS EM.empty $ zip vars $ V.toList parameters
        dt = fromMaybe 1 mdt
        envDt = extendEnvS varDt dt env
        gradientDomain = interpretAstDomains envDt gradient
        primalTensor = interpretAstPrimalS env primal
    in (gradientDomain, primalTensor)

  fwdArtifactFromForwardPass
    :: forall r sh. (GoodScalar r, OS.Shape sh)
    => (Domains (AstDynamic PrimalSpan)
        -> [AstDynamicVarName (AstShaped FullSpan)]
        -> Domains (AstDynamic FullSpan)
        -> ADVal (AstShaped PrimalSpan) r sh)
    -> DomainsOD
    -> ( AstArtifactFwd (AstShaped PrimalSpan) r sh
       , Dual (AstShaped PrimalSpan) r sh )
  {-# INLINE fwdArtifactFromForwardPass #-}
  fwdArtifactFromForwardPass forwardPass parameters0 =
    let !(!varsPrimalDs, domainsDs, varsPrimal, domainsPrimal, vars, domains) =
          funToAstFwdS parameters0 in
    let !(D l primalBody delta) = forwardPass domainsPrimal vars domains  in
    let !(!astBindings, !derivative) =
          forwardDerivative (V.length parameters0) delta domainsDs
    in ( ( (varsPrimalDs, varsPrimal)
         , unletAst6S astBindings l derivative
         , unletAst6S [] l primalBody )
       , delta )

  {-# INLINE fwdEvalArtifact #-}
  fwdEvalArtifact ((varDs, vars), derivative, primal) parameters ds =
    let env = foldr extendEnvDS EM.empty $ zip vars $ V.toList parameters
        envDs = foldr extendEnvDS env $ zip varDs $ V.toList ds
        derivativeTensor = interpretAstPrimalS envDs derivative
        primalTensor = interpretAstPrimalS @(Flip OR.Array) env primal
    in (derivativeTensor, primalTensor)


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
  runravelToList :: forall r n. KnownNat n
                 => AstRanked s r (1 + n) -> [AstRanked s r n]
  runravelToList t =
    let f :: Int64 -> AstRanked s r n
        f i = AstIndex t (singletonIndex $ fromIntegral i)
    in map f [0 .. valueOf @n - 1]
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
  rletWrap l u = if nullADShare l then u
                 else fromPrimal $ AstLetADShare l (astSpanPrimal u)
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  rletUnwrap u = case u of
    AstLetADShare l t -> (l, t)
    AstConstant (AstLetADShare l t) -> (l, AstConstant t)
    _ -> (emptyADShare, u)
  raddDynamic :: forall n r. (GoodScalar r, KnownNat n)
              => AstRanked s r n -> DynamicExists (AstDynamic s)
              -> DynamicExists (AstDynamic s)
  raddDynamic r (DynamicExists @r2 d) = DynamicExists @r $
    case d of
      AstRToD AstIota -> AstRToD r
      AstRToD @n2 v ->
        case ( sameNat (Proxy @n) (Proxy @n2)
             , testEquality (typeRep @r) (typeRep @r2) ) of
          (Just Refl, Just Refl) -> AstRToD @n2 @r (r + v)
          _ -> error "raddDynamic: type mismatch"
      AstSToD AstIotaS -> AstRToD r
      AstSToD @sh2 v ->
        case ( matchingRank @sh2 @n
             , testEquality (typeRep @r) (typeRep @r2) ) of
          (Just Refl, Just Refl) -> AstSToD @sh2 @r (astRToS r + v)
          _ -> error "raddDynamic: type mismatch"
  rregister = astRegisterFun

  rconstant = fromPrimal
  rprimalPart = astSpanPrimal
  rdualPart = astSpanDual
  rD = astSpanD
  rScale s t = astDualPart $ AstConstant s * AstD (rzero (rshape s)) t

instance ( GoodScalar r, KnownNat n
         , RankedTensor (AstRanked s)
         , ConvertTensor (AstRanked s) (AstShaped s) )
         => AdaptableDomains (AstDynamic s) (AstRanked s r n) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableDomains (AstDynamic s) (AstRanked s Double n) #-}
  type Value (AstRanked s r n) = Flip OR.Array r n
  toDomains = undefined
  fromDomains aInit params = case V.uncons params of
    Just (DynamicExists @r2 a, rest) ->
      if isTensorDummyAst a then Just (rzero (rshape aInit), rest) else
        case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> let !t = tfromD @(AstRanked s) @(AstShaped s) @r a
                       in Just (t, rest)
          _ -> error $ "fromDomains: type mismatch: "
                       ++ show (typeRep @r) ++ " " ++ show (typeRep @r2)
    Nothing -> Nothing

isTensorDummyAst :: AstDynamic s r -> Bool
isTensorDummyAst t = case t of
  AstRToD AstIota -> True
  AstSToD AstIotaS -> True
  _ -> False

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
  sunravelToList :: forall r n sh. (KnownNat n, OS.Shape sh)
                 => AstShaped s r (n ': sh) -> [AstShaped s r sh]
  sunravelToList t =
    let f :: Int64 -> AstShaped s r sh
        f i = AstIndexS t (singletonShaped $ fromIntegral i)
    in map f [0 .. valueOf @n - 1]
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
  sletWrap l u = if nullADShare l then u
                 else fromPrimalS $ AstLetADShareS l (astSpanPrimalS u)
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  sletUnwrap u = case u of
    AstLetADShareS l t -> (l, t)
    AstConstantS (AstLetADShareS l t) -> (l, AstConstantS t)
    _ -> (emptyADShare, u)
  saddDynamic :: forall sh r. (GoodScalar r, OS.Shape sh)
              => AstShaped s r sh -> DynamicExists (AstDynamic s)
              -> DynamicExists (AstDynamic s)
  saddDynamic r (DynamicExists @r2 d) = DynamicExists @r $
    case d of
      AstSToD AstIotaS -> AstSToD r
      AstSToD @sh2 v ->
        case ( sameShape @sh @sh2
             , testEquality (typeRep @r) (typeRep @r2) ) of
          (Just Refl, Just Refl) -> AstSToD @sh2 @r (r + v)
          _ -> error "saddDynamic: type mismatch"
      AstRToD AstIota -> AstSToD r
      AstRToD @n2 v ->
        case ( matchingRank @sh @n2
             , testEquality (typeRep @r) (typeRep @r2) ) of
          (Just Refl, Just Refl) -> AstRToD @n2 @r (astSToR r + v)
          _ -> error "saddDynamic: type mismatch"
  sregister = astRegisterFunS

  sconstant = fromPrimalS
  sprimalPart = astSpanPrimalS
  sdualPart = astSpanDualS
  sD = astSpanDS
  sScale s t = astDualPartS $ AstConstantS s * AstDS 0 t

instance ( GoodScalar r, OS.Shape sh
         , ShapedTensor (AstShaped s)
         , ConvertTensor (AstRanked s) (AstShaped s) )
         => AdaptableDomains (AstDynamic s) (AstShaped s r sh) where
  type Value (AstShaped s r sh) = Flip OS.Array r sh
  toDomains = undefined
  fromDomains _aInit params = case V.uncons params of
    Just (DynamicExists @r2 a, rest) ->
      if isTensorDummyAst a then Just (0, rest) else
        case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> let !t = sfromD @(AstRanked s) @(AstShaped s) @r a
                       in Just (t, rest)
          _ -> error "fromDomains: type mismatch"
    Nothing -> Nothing

astSpanPrimalS :: forall s r sh. (OS.Shape sh, GoodScalar r, AstSpan s)
               => AstShaped s r sh -> AstShaped PrimalSpan r sh
astSpanPrimalS t | Just Refl <- sameAstSpan @s @PrimalSpan = t
astSpanPrimalS _ | Just Refl <- sameAstSpan @s @DualSpan =
  error "astSpanPrimalS: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimalS t | Just Refl <- sameAstSpan @s @FullSpan = astPrimalPartS t
astSpanPrimalS _ = error "a spuriuos case for pattern match coverage"

astSpanDualS :: forall s r sh. (OS.Shape sh, GoodScalar r, AstSpan s)
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

astLetFunS :: ( OS.Shape sh, OS.Shape sh2, GoodScalar r, GoodScalar r2
              , AstSpan s )
          => AstShaped s r sh -> (AstShaped s r sh -> AstShaped s r2 sh2)
          -> AstShaped s r2 sh2
astLetFunS a f | astIsSmallS True a = f a
astLetFunS a f =
  let (var, ast) = funToAstS f
  in astLetS var a ast  -- safe, because subsitution ruled out above

astBuild1VectorizeS :: (KnownNat n, OS.Shape sh, GoodScalar r, AstSpan s)
                    => (IntSh (AstShaped PrimalSpan) n -> AstShaped s r sh)
                    -> AstShaped s r (n ': sh)
astBuild1VectorizeS f =
  build1VectorizeS $ funToAstI (f . ShapedList.shapedNat)


-- * ConvertTensor and DomainsTensor instances

instance AstSpan s => ConvertTensor (AstRanked s) (AstShaped s) where
  tfromD = astFromDynamic
  tfromS = astSToR
  dfromR = AstRToD
  dfromS = AstSToD
  sfromR = astRToS
  sfromD = astFromDynamicS
  ddummy = AstRToD $ fromPrimal AstIota
  dshape (AstRToD v) = shapeToList $ shapeAst v
  dshape (AstSToD @sh _) = OS.shapeT @sh

instance AstSpan s => DomainsTensor (AstRanked s) (AstShaped s) where
  dmkDomains = AstDomains
  rletDomainsOf = astLetDomainsFun
  rletToDomainsOf = astDomainsLetFun
  sletDomainsOf = astLetDomainsFunS
  sletToDomainsOf = astDomainsLetFunS
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => Domains (DynamicOf f) -> f r n)
       -> DomainsOD
       -> Domains (AstDynamic s)
       -> AstDomains s
-- TODO: perhaps do this in the AstNoVectorize instance:
--   rrev f parameters0 domains = AstRev (funToAstDomains f parameters0) domains
  rrev f parameters0 =
    let (((_varDt, vars), gradient, _primal, _sh), _delta) =
          revProduceArtifact False (f @(AstRanked FullSpan))
                             EM.empty parameters0
    in \parameters ->
      let env = extendEnvPars @(AstRanked s) vars parameters EM.empty
      in interpretAstDomains env gradient
        -- this interpretation both substitutes parameters for the variables and
        -- reinterpretes @PrimalSpan@ terms in @s@ terms;
        -- we could shortcut when @s@ is @PrimalSpan@ and @parameters@
        -- are the same variables, but it's a very special case

astLetDomainsFun
  :: forall m s r. AstSpan s
  => DomainsOD -> AstDomains s -> (Domains (AstDynamic s) -> AstRanked s r m)
  -> AstRanked s r m
astLetDomainsFun a0 a f =
  let genVar :: DynamicExists OD.Array
                -> ( AstDynamicVarName (AstShaped s)
                   , DynamicExists (AstDynamic s) )
      genVar (DynamicExists @r2 t) =
        let sh2 = OD.shapeL t
        in OS.withShapeP sh2 $ \(Proxy :: Proxy p_sh2) ->
          let (var, ast) = funToAstS @p_sh2 id
          in ( AstDynamicVarName @[Nat] @p_sh2 @r2 var
             , DynamicExists $ AstSToD ast )
      (vars, asts) = unzip $ map genVar (V.toList a0)
  in AstLetDomains vars a (f $ V.fromList asts)

astDomainsLetFun :: (KnownNat n, GoodScalar r, AstSpan s)
                 => AstRanked s r n -> (AstRanked s r n -> AstDomains s)
                 -> AstDomains s
astDomainsLetFun a f | astIsSmall True a = f a
astDomainsLetFun a f =
  let sh = shapeAst a
      (var, ast) = funToAstR sh id
  in astDomainsLet var a (f ast)  -- safe, because subsitution ruled out above

astLetDomainsFunS
  :: forall sh s r. AstSpan s
  => DomainsOD -> AstDomains s -> (Domains (AstDynamic s) -> AstShaped s r sh)
  -> AstShaped s r sh
astLetDomainsFunS a0 a f =
  let genVar :: DynamicExists OD.Array
                -> ( AstDynamicVarName (AstShaped s)
                   , DynamicExists (AstDynamic s) )
      genVar (DynamicExists @r2 t) =
        let sh2 = OD.shapeL t
        in OS.withShapeP sh2 $ \(Proxy :: Proxy p_sh2) ->
          let (var, ast) = funToAstS @p_sh2 id
          in ( AstDynamicVarName @[Nat] @p_sh2 @r2 var
             , DynamicExists $ AstSToD ast )
      (vars, asts) = unzip $ map genVar (V.toList a0)
  in AstLetDomainsS vars a (f $ V.fromList asts)

astDomainsLetFunS :: (OS.Shape sh, GoodScalar r, AstSpan s)
                  => AstShaped s r sh -> (AstShaped s r sh -> AstDomains s)
                  -> AstDomains s
astDomainsLetFunS a f | astIsSmallS True a = f a
astDomainsLetFunS a f =
  let (var, ast) = funToAstS id
  in astDomainsLetS var a (f ast)  -- safe, because subsitution ruled out above


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
  raddDynamic = undefined

  rconstant = AstNoVectorize . fromPrimal
  rprimalPart = astSpanPrimal . unAstNoVectorize
  rdualPart = astSpanDual . unAstNoVectorize
  rD u u' = AstNoVectorize $ astSpanD u u'
  rScale s t = astDualPart $ AstConstant s * AstD (rzero (rshape s)) t

instance AstSpan s
         => ShapedTensor (AstNoVectorizeS s) where

instance ConvertTensor (AstNoVectorize 'PrimalSpan)
                       (AstNoVectorizeS 'PrimalSpan) where

instance DomainsTensor (AstNoVectorize s) (AstNoVectorizeS s) where

instance AstSpan s
         => RankedTensor (AstNoSimplify s) where
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
  raddDynamic = undefined

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

instance AstSpan s
         => ShapedTensor (AstNoSimplifyS s) where

instance ConvertTensor (AstNoSimplify 'PrimalSpan)
                       (AstNoSimplifyS 'PrimalSpan) where

instance DomainsTensor (AstNoSimplify s) (AstNoSimplifyS s) where
