{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for dual numbers. Most of the definitions
-- are generic over whether the dual numbers are built from concrete arrays
-- of floats or from AST terms. However, here we do not abstract over
-- the typing of tensors and so we give separate instances
-- for ranked tensors and shaped tensors.
module HordeAd.Core.TensorADVal
  ( aDValToHVector, hVectorADValToADVal, unADValHVector, unADValDynamicTensor
  , unADValInterpretation
  , crevOnADInputs, crevOnHVector, cfwdOnHVector
  ) where

import Prelude hiding (foldl')

import Control.Exception.Assert.Sugar
import Data.Array.Internal (valueOf)
import Data.Array.RankedS qualified as OR
import Data.Function ((&))
import Data.List (foldl')
import Data.List.Index (imap)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
import Type.Reflection (typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape qualified as X
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.IsPrimal
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray, OSArray)
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..), FlipS (..))
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

-- * Non-symbolic reverse and forward derivative computation

crevOnADInputs
  :: forall x z ranked.
     ( TensorKind x, TensorKind z, ADReadyNoLet ranked
     , ShareTensor ranked, ShareTensor (PrimalOf ranked) )
  => Maybe (InterpretationTarget ranked z)
  -> (InterpretationTarget (ADVal ranked) x
      -> InterpretationTarget (ADVal ranked) z)
  -> InterpretationTarget (ADVal ranked) x
  -> (InterpretationTarget ranked x, InterpretationTarget ranked z)
-- The functions in which @revOnADInputs@ inlines are not inlined themselves
-- in client code, so the bloat is limited.
{-# INLINE crevOnADInputs #-}
crevOnADInputs mdt f inputs =
  let -- Evaluate completely after terms constructed, to free memory
      -- before evaluation allocates new memory and new FFI is started.
      !(!v, !deltaIT) = unADValInterpretation (stensorKind @z) $ f inputs
      !delta = unDeltaRY (stensorKind @z) deltaIT in
  let parameters0 = tshapeFull (stensorKind @x) inputs
      !gradient = gradientFromDelta parameters0 v mdt delta
  in (gradient, v)

-- | The third argument (@parameters@) must be shallowly duplicable
-- (that is, either duplicable (e.g., a variable or concrete) or starting with
-- a tuple constructor).
crevOnHVector
  :: forall x z ranked.
     ( TensorKind x, TensorKind z, ADReadyNoLet ranked
     , ShareTensor ranked, ShareTensor (PrimalOf ranked) )
  => Maybe (InterpretationTarget ranked z)
  -> (InterpretationTarget (ADVal ranked) x
      -> InterpretationTarget (ADVal ranked) z)
  -> InterpretationTarget ranked x
  -> (InterpretationTarget ranked x, InterpretationTarget ranked z)
crevOnHVector mdt f parameters =
  let deltaInputs = generateDeltaInputs $ tshapeFull (stensorKind @x) parameters
      inputs = makeADInputs parameters deltaInputs
  in crevOnADInputs mdt f inputs

-- | The third argument (@ds@) must be shallowly duplicable.
cfwdOnADInputs
  :: forall x z ranked.
     (TensorKind x, TensorKind z, ADReadyNoLet ranked, ShareTensor ranked)
  => InterpretationTarget (ADVal ranked) x
  -> (InterpretationTarget (ADVal ranked) x
      -> InterpretationTarget (ADVal ranked) z)
  -> InterpretationTarget ranked x
  -> (InterpretationTarget ranked z, InterpretationTarget ranked z)
{-# INLINE cfwdOnADInputs #-}
cfwdOnADInputs inputs f ds =
  let !(!v, !deltaIT) = unADValInterpretation (stensorKind @z) $ f inputs
      !delta = unDeltaRY (stensorKind @z) deltaIT in
  let !derivative = derivativeFromDelta delta ds
  in (derivative, v)

-- | The first and third argument (@ds@) must be shallowly duplicable.
cfwdOnHVector
  :: forall x z ranked.
     (TensorKind x, TensorKind z, ADReadyNoLet ranked, ShareTensor ranked)
  => InterpretationTarget ranked x
  -> (InterpretationTarget (ADVal ranked) x
      -> InterpretationTarget (ADVal ranked) z)
  -> InterpretationTarget ranked x
  -> (InterpretationTarget ranked z, InterpretationTarget ranked z)
cfwdOnHVector parameters f ds =
  let deltaInputs = generateDeltaInputs $ tshapeFull (stensorKind @x) parameters
      inputs = makeADInputs parameters deltaInputs
  in cfwdOnADInputs inputs f ds


-- * Misc instances

instance ( shaped ~ ShapedOf ranked, ADReadyNoLet ranked, ShareTensor ranked
         , ShareTensor (PrimalOf ranked) )
         => LetTensor (ADVal ranked) (ADVal shaped) where
-- TODO: is the sharing needed or can we just do:  rletHVectorIn = (&)
  rletHFunIn = (&)
  sletHFunIn = (&)
  dletHFunInHVector = (&)
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => InterpretationTarget (ADVal ranked) x
       -> (ConcreteTarget (ADVal ranked) x
           -> InterpretationTarget (ADVal ranked) z)
       -> InterpretationTarget (ADVal ranked) z
  tlet a f = case stensorKind @x of
    STKR{} -> blet a f
    STKS{} -> blet a f
    STKProduct{} -> blet a f
    STKUntyped{} ->
      let (!u, !u') = unADValHVector $ unHVectorPseudoTensor a
          !var2 = dunHVector $ unHVectorPseudoTensor $ tshare @_ @TKUntyped
                  $ HVectorPseudoTensor $ dmkHVector u
            -- dunHVector is fine, because its argument is shared
            -- (and even without that, it comes from an explicit HVector)
            -- and tshare is needed due to f possibly using the argument many times
            -- and while the Haskell computation would be performed only once,
            -- a term could get duplicated and then interpreted many times.
            -- Normally it would be the reponsibility of f to share its argument
            -- but this is a let expression, so here we ensure what is passed
            -- to f is properly shared.
      in f (aDValHVector var2 u')
  blet :: forall x z. (TensorKind x, TensorKind z)
       => InterpretationTarget (ADVal ranked) x
       -> (InterpretationTarget (ADVal ranked) x
           -> InterpretationTarget (ADVal ranked) z)
       -> InterpretationTarget (ADVal ranked) z
  blet a f = case stensorKind @x of
    STKR{} ->
      let (D u u') = a
          !var2 = tshare u
      in f (dDnotShared var2 u')
    STKS{} ->
      let (D u u') = a
          !var2 = tshare u
      in f (dDnotShared var2 u')
    STKProduct{} ->
      -- Sharing is preserved despite `a` being repeated, because
      -- each repetition concerns a disjoint portion of `a` and so the whole `a`
      -- is computed only once.
      blet (fst a) $ \ !a1 ->
        blet (snd a) $ \ !a2 -> f (a1, a2)
    STKUntyped{} ->
      let (!u, !u') = unADValHVector $ unHVectorPseudoTensor a
          !var2 = dunHVector $ unHVectorPseudoTensor $ tshare @_ @TKUntyped
                  $ HVectorPseudoTensor $ dmkHVector u
      in f (HVectorPseudoTensor $ aDValHVector var2 u')

  toShare = id
  tunshare = id
  tconstant :: STensorKindType y
            -> InterpretationTarget ranked y
            -> InterpretationTarget (ADVal ranked) y
  tconstant stk t = case stk of
    STKR{} -> rconstant t
    STKS{} -> sconstant t
    STKProduct stk1 stk2 ->
      let (t1, t2) = tunpair t
          !c1 = tconstant stk1 t1
          !c2 = tconstant stk2 t2
      in (c1, c2)
    STKUntyped ->
      let fd :: DynamicTensor ranked -> DynamicTensor (ADVal ranked)
          fd = mapDynamic rconstant sconstant
      in HVectorPseudoTensor $ V.map fd $ tunvector t

  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (ADVal ranked)
       -> HVectorOf (ADVal ranked)
  rrev f _parameters0 parameters =
    let g :: InterpretationTarget (ADVal (ADVal ranked)) TKUntyped
          -> InterpretationTarget (ADVal (ADVal ranked)) TKUntyped
        -- This computes the derivative of g again for each new @parmeters@.
        g !hv = HVectorPseudoTensor $ V.singleton $ DynamicRanked
                $ f $ unHVectorPseudoTensor hv
    -- The third argument is duplicable (a concrete vector), as required.
    in unHVectorPseudoTensor $ fst $ crevOnHVector Nothing g
       $ HVectorPseudoTensor parameters

instance ShareTensor (ADVal ranked) where
  tshare = id
  tunpair = id
  tunvector = unHVectorPseudoTensor

-- * Ranked tensor instance

instance ( KnownNat n, GoodScalar r, ADReadyNoLet ranked
         , ShareTensor ranked, ShareTensor (PrimalOf ranked) )
         => AdaptableHVector (ADVal ranked)
                             (ADVal ranked r n) where
{- TODO: RULE left-hand side too complicated to desugar in GHC 9.6.4
    with -O0, but not -O1
  {-# SPECIALIZE instance
      (KnownNat n, ADReadyNoLet ORArray)
      => AdaptableHVector (ADVal ORArray)
                          (ADVal ORArray Double n) #-}
  {-# SPECIALIZE instance
      (KnownNat n, ADReadyNoLet (AstRanked PrimalSpan))
      => AdaptableHVector (ADVal (AstRanked PrimalSpan))
                          (ADVal (AstRanked PrimalSpan) Double n) #-}
-}
  toHVector = V.singleton . DynamicRanked
  fromHVector _aInit = fromHVectorR

instance (KnownNat n, GoodScalar r, ADReadyNoLet ranked, ShareTensor ranked)
         => DualNumberValue (ADVal ranked r n) where
  type DValue (ADVal ranked r n) = ORArray r n  -- ! not Value(ranked)
  fromDValue t = constantADVal $ rconst $ runFlipR t

-- This is temporarily moved from Adaptor in order to specialize manually
instance AdaptableHVector ranked a
         => AdaptableHVector ranked [a] where
  {-# SPECIALIZE instance
      AdaptableHVector ORArray (OR.Array n Double)
      => AdaptableHVector ORArray
                          [OR.Array n Double] #-}
  {-# SPECIALIZE instance
      AdaptableHVector (AstRanked s)
                       (AstRanked s Double n)
      => AdaptableHVector (AstRanked s)
                          [AstRanked s Double n] #-}
  toHVector = V.concat . map toHVector
  fromHVector lInit source =
    let f (!lAcc, !restAcc) !aInit =
          case fromHVector aInit restAcc of
            Just (a, rest) -> (a : lAcc, rest)
            Nothing -> error "fromHVector: Nothing"
        (l, !restAll) = foldl' f ([], source) lInit
        !rl = reverse l
    in Just (rl, restAll)
    -- is the following as performant? benchmark:
    -- > fromHVector lInit source =
    -- >   let f = swap . flip fromHVector
    -- >   in swap $ mapAccumL f source lInit

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance (ADReadyNoLet ranked, ShareTensor ranked, ShareTensor (PrimalOf ranked))
         => RankedTensor (ADVal ranked) where
  rshape (D u _) = rshape u
  rminIndex (D u _) =
    let v = rminIndex u
    in dDnotShared v (dZeroOfShape v)
  rmaxIndex (D u _) =
    let v = rmaxIndex u
    in dDnotShared v (dZeroOfShape v)
  rfloor (D u _) =
    let v = rfloor u
    in dDnotShared v (dZeroOfShape v)

  -- TODO: speed up by using tindex0R and dIndex0 if the codomain has rank 0
  -- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
  -- dimension affected.
  rindex d i = indexPrimal d (rprimalPart <$> i)
  rsum (D u (DeltaR u')) = dD (rsum u) (DeltaR $ SumR u')
  rsum0 (D u (DeltaR u')) = dD (rsum0 u) (DeltaR $ Sum0R u')
  rdot0 (D ue (DeltaR u')) (D ve (DeltaR v')) =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (rdot0 u v) (dAdd (DeltaR $ Dot0R v u') (DeltaR $ Dot0R u v'))
  rscatter sh (D u (DeltaR u')) f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD (rscatter sh u g) (DeltaR $ ScatterR sh u' g)

  rfromVector = fromVector
  runravelToList (D u (DeltaR u')) =
    let lu = runravelToList u
        f i ui = dD ui (DeltaR $ IndexR u' (singletonIndex $ fromIntegral i))
    in imap f lu
  rreplicate k (D u (DeltaR u')) = dD (rreplicate k u) (DeltaR $ ReplicateR k u')
  rappend (D u (DeltaR u')) (D v (DeltaR v')) =
    dD (rappend u v) (DeltaR $ AppendR u' v')
  rslice i n (D u (DeltaR u')) = dD (rslice i n u) (DeltaR $ SliceR i n u')
  rreverse (D u (DeltaR u')) = dD (rreverse u) (DeltaR $ ReverseR u')
  rtranspose perm (D u (DeltaR u')) = dD (rtranspose perm u) (DeltaR $ TransposeR perm u')
  rreshape :: forall n m r. (GoodScalar r, KnownNat n, KnownNat m)
           => IShR m -> ADVal ranked r n -> ADVal ranked r m
  rreshape sh t@(D u (DeltaR u')) = case sameNat (Proxy @m) (Proxy @n) of
    Just Refl | sh == rshape u -> t
    _ -> dD (rreshape sh u) (DeltaR $ ReshapeR sh u')
  rbuild1 :: forall r n. (GoodScalar r, KnownNat n)
          => Int -> (IntOf (ADVal ranked) -> ADVal ranked r n)
          -> ADVal ranked r (1 + n)
  rbuild1 0 _ = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> rconst $ Nested.Internal.rfromListPrimLinear (0 :$: ZSR) []
                   -- the only case where we can guess sh
    _ ->  error "rbuild1: shape ambiguity, no arguments"
  rbuild1 k f = rfromList $ NonEmpty.fromList
                          $ map (f . fromIntegral) [0 .. k - 1]
                   -- element-wise (POPL) version
  rgather sh (D u (DeltaR u')) f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD (rgather sh u g) (DeltaR $ GatherR sh u' g)
      -- note how f is not interpreted as a function on dual numbers
      -- but just on integers and so no cotangents for results of application
      -- of f have to be computed and stored in contangent maps later on
  rcast (D u (DeltaR u')) = dD (rcast u) (DeltaR $ CastR u')
  rfromIntegral (D u _) =
    let v = rfromIntegral u
    in dDnotShared v (dZeroOfShape v)
  rconst t = constantADVal (rconst t)
  rfromS :: forall r sh. (GoodScalar r, KnownShS sh)
         => ADVal (ShapedOf ranked) r sh -> ADVal ranked r (X.Rank sh)
  rfromS (D u u') = dDnotShared (rfromS u) (DeltaR $ dRFromS $ unDeltaS u')
   where
    dRFromS :: (GoodScalar r2, KnownShS sh2)
            => Delta ranked (TKS r2 sh2) -> Delta ranked (TKR r2 (X.Rank sh2))
    dRFromS (SFromR d) = d  -- no information lost, so no checks
    dRFromS d = RFromS d

  rconstant t = dDnotShared t (dZeroOfShape t)
  rprimalPart (D u _) = u
  rdualPart (D _ u') = u'
  rD = dD
  rScale = dScale


-- * Shaped tensor instance

instance ( ADReadyNoLetS shaped, ShareTensor ranked
         , ShareTensor (PrimalOf ranked)
         , KnownShS sh, GoodScalar r
         , ranked ~ RankedOf shaped )
         => AdaptableHVector (ADVal ranked)
                             (ADVal shaped r sh) where
  toHVector = V.singleton . DynamicShaped
  fromHVector _aInit = fromHVectorS

instance ( ADReadyNoLetS shaped, ShareTensor (RankedOf shaped)
         , KnownShS sh, GoodScalar r )
         => DualNumberValue (ADVal shaped r sh) where
  type DValue (ADVal shaped r sh) = OSArray r sh   -- ! not Value(shaped)
  fromDValue t = constantADVal $ sconst $ runFlipS t

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance (ADReadyNoLetS shaped, ShareTensor (RankedOf shaped)
         , ShareTensor (PrimalOf (RankedOf shaped)) )
         => ShapedTensor (ADVal shaped) where
  sminIndex (D u _) =
    let v = sminIndex u
    in dDnotShared v (dZeroOfShape v)
  smaxIndex (D u _) =
    let v = smaxIndex u
    in dDnotShared v (dZeroOfShape v)
  sfloor (D u _) =
    let v = sfloor u
    in dDnotShared v (dZeroOfShape v)

  siota = constantADVal siota
  sindex d i = indexPrimalS d (rprimalPart <$> i)
  ssum (D u (DeltaS u')) = dD (ssum u) (DeltaS $ SumS u')
  ssum0 (D u (DeltaS u')) = dD (ssum0 u) (DeltaS $ Sum0S u')
  sdot0 (D ue (DeltaS u')) (D ve (DeltaS v')) =
    -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
    let !u = tshare ue in
    let !v = tshare ve
    in dD (sdot0 u v) (dAdd (DeltaS $ Dot0S v u') (DeltaS $ Dot0S u v'))
  sscatter (D u (DeltaS u')) f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD (sscatter u g) (DeltaS $ ScatterS u' g)

  sfromVector = fromVectorS
  sunravelToList (D u (DeltaS u')) =
    let lu = sunravelToList u
        f i ui = dD ui (DeltaS $ IndexS u' (ShapedList.singletonIndex
                                            $ fromIntegral i))
    in imap f lu
  sreplicate (D u (DeltaS u')) = dD (sreplicate u) (DeltaS $ ReplicateS u')
  sappend (D u (DeltaS u')) (D v (DeltaS v')) =
    dD (sappend u v) (DeltaS $ AppendS u' v')
  sslice (i_proxy :: Proxy i) n_proxy (D u (DeltaS u')) =
    dD (sslice i_proxy n_proxy u) (DeltaS $ SliceS @(RankedOf shaped) @i u')
  sreverse (D u (DeltaS u')) = dD (sreverse u) (DeltaS $ ReverseS u')

  stranspose :: forall perm r sh.
                ( PermC perm, KnownShS sh
                , X.Rank perm <= X.Rank sh, GoodScalar r )
             => Permutation.Perm perm -> ADVal shaped r sh
             -> ADVal shaped r (Permutation.PermutePrefix perm sh)
  stranspose perm (D u (DeltaS u')) | Dict <- Nested.Internal.Shape.shsKnownShS (Nested.Internal.Shape.shsPermutePrefix perm (knownShS @sh)) =
    dD (stranspose perm u) (DeltaS $ TransposeS @_ @_ @_ @(RankedOf shaped) perm u')
  sreshape :: forall sh sh2 r.
              ( GoodScalar r, KnownShS sh, KnownShS sh2
              , Nested.Internal.Shape.Product sh ~ Nested.Internal.Shape.Product sh2)
           => ADVal shaped r sh -> ADVal shaped r sh2
  sreshape t@(D u (DeltaS u')) = case sameShape @sh2 @sh of
    Just Refl -> t
    _ -> dD (sreshape u) (DeltaS $ ReshapeS u')
  sbuild1 :: forall r n sh. (GoodScalar r, KnownNat n, KnownShS sh)
          => (IntOf (ADVal shaped) -> ADVal shaped r sh)
          -> ADVal shaped r (n ': sh)
  sbuild1 f = case valueOf @n of
    0 -> sconst $ Nested.Internal.sfromListPrimLinear knownShS []
    k -> sfromList $ NonEmpty.fromList
                   $ map (f . fromIntegral)
                         [0 :: Int .. k - 1]
           -- element-wise (POPL) version
  sgather (D u (DeltaS u')) f =
    let g x = rprimalPart <$> f (rconstant <$> x)
    in dD (sgather u g) (DeltaS $ GatherS u' g)
  scast (D u (DeltaS u')) = dD (scast u) (DeltaS $ CastS u')
  sfromIntegral (D u _) =
    let v = sfromIntegral u
    in dDnotShared v (dZeroOfShape v)
  sconst t = constantADVal (sconst t)
  sfromR :: forall r sh. (GoodScalar r, KnownShS sh, KnownNat (X.Rank sh))
         => ADVal (RankedOf shaped) r (X.Rank sh) -> ADVal shaped r sh
  sfromR (D u u') = dDnotShared (sfromR u) (DeltaS $ dSFromR u')
   where
    dSFromR (DeltaR (RFromS @sh1 d)) =
      case sameShape @sh1 @sh of
        Just Refl -> d
        _ -> error "sfromR: different shapes in SFromR(RFromS)"
    dSFromR (DeltaR d) = SFromR d

  sconstant t = dDnotShared t (dZeroOfShape t)
  sprimalPart (D u _) = u
  sdualPart (D _ u') = u'
  sD = dD
  sScale = dScale


-- * HVectorTensor instance

instance (ADReadyNoLet ranked, HVectorOf ranked ~ HVector ranked)
         => AdaptableHVector (ADVal ranked)
                             (ADVal (HVectorPseudoTensor ranked)
                                    Float '()) where
  toHVector = aDValToHVector
  fromHVector (D (HVectorPseudoTensor h) _) params =
    let (portion, rest) = V.splitAt (V.length h) params
    in Just (hVectorADValToADVal portion, rest)

instance ( shaped ~ ShapedOf ranked, ADReadyNoLet ranked
         , ShareTensor ranked
         , ShareTensor (PrimalOf ranked) )
         => HVectorTensor (ADVal ranked) (ADVal shaped) where
  dshape = voidFromHVector
  tshapeFull stk t = case stk of
    STKR{} -> let D u _ = t
              in tshapeFull stk u
    STKS{} -> FTKS
    STKProduct stk1 stk2 -> FTKProduct (tshapeFull stk1 (fst t))
                                       (tshapeFull stk2 (snd t))
    STKUntyped -> let D u _ = hVectorADValToADVal $ unHVectorPseudoTensor t
                  in tshapeFull stk u
  tcond stk b u v = case stk of
    STKR{} -> ifF b u v
    STKS{} -> ifF b u v
    STKProduct stk1 stk2 ->
      let !t1 = tcond stk1 b (fst u) (fst v)
          !t2 = tcond stk2 b (snd u) (snd v)
      in (t1, t2)
    STKUntyped ->
      let fd = mapDynamic2 (ifF b) (ifF b)
      in HVectorPseudoTensor
         $ V.zipWith fd (unHVectorPseudoTensor u) (unHVectorPseudoTensor v)
  tprimalPart :: STensorKindType y
              -> InterpretationTarget (ADVal ranked) y
              -> InterpretationTarget ranked y
  tprimalPart stk t = case stk of
    STKR{} -> rprimalPart t
    STKS{} -> sprimalPart t
    STKProduct stk1 stk2 ->
      let !t1 = tprimalPart stk1 $ fst t
          !t2 = tprimalPart stk2 $ snd t
      in ttuple t1 t2
    STKUntyped ->
      let fd :: DynamicTensor (ADVal ranked) -> DynamicTensor ranked
          fd = mapDynamic rprimalPart sprimalPart
      in HVectorPseudoTensor $ tmkHVector
         $ V.map fd $ unHVectorPseudoTensor t
  dmkHVector = id
  dlambda _ = id
  dHApply (HFun f) = f
  dunHVector = id
  dbuild1 k f =
    ravelHVector $ map (f . fromIntegral) [0 .. sNatValue k - 1]
  drevDt :: forall x z. (TensorKind x, TensorKind z)
         => TensorKindFull x
         -> HFun x z
         -> HFun (TKProduct z x) x
  drevDt _ftk h =
    let rf :: forall f. ADReady f
           => InterpretationTarget f (TKProduct z x)
           -> InterpretationTarget f x
        -- This computes the derivative of g again for each new db and a.
        rf !db_a = blet db_a $ \ !db_aShared ->
          -- The third argument is duplicable (projections of a variable),
          -- as required.
          tunshare $ fst $ crevOnHVector
                             (Just $ toShare $ tproject1 db_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare $ tproject2 db_aShared)
    in HFun rf
  dfwd :: forall x z. (TensorKind x, TensorKind z)
       => TensorKindFull x
       -> HFun x z
       -> HFun (TKProduct x x) z
  dfwd _ftk h =
    let df :: forall f. ADReady f
           => InterpretationTarget f (TKProduct x x)
           -> InterpretationTarget f z
        -- This computes the derivative of g again for each new da and a.
        df !da_a = blet da_a $ \ !da_aShared ->
          -- The first and third arguments are duplicable
          -- (projections of a variable), as required.
          tunshare $ fst $ cfwdOnHVector
                             (toShare $ tproject2 da_aShared)
                             (unHFun h @(ADVal (ShareOf f)))
                             (toShare $ tproject1 da_aShared)
    in HFun df
  dmapAccumRDer _ !k accShs@(FTKUntyped accShsH) bShs@(FTKUntyped bShsH)
                eShs@(FTKUntyped eShsH) f df rf acc0D esD =
    assert (voidHVectorMatches (replicate1VoidHVector k eShsH)
                               (unHVectorPseudoTensor esD)
            && voidHVectorMatches accShsH (unHVectorPseudoTensor acc0D)) $
    let (acc0, acc0') = unADValHVector $ unHVectorPseudoTensor acc0D
        (esUnshared, es') = unADValHVector $ unHVectorPseudoTensor esD
        es = tshare $ HVectorPseudoTensor $ dmkHVector esUnshared
        codomainShs = FTKUntyped $ accShsH V.++ bShsH
        accLen = V.length accShsH
        hvToPair :: forall f. HVector f -> (HVector f, HVector f)
        hvToPair = V.splitAt accLen
        g :: forall f. ADReady f
          => InterpretationTarget f (TKProduct TKUntyped TKUntyped)
          -> InterpretationTarget f (TKProduct TKUntyped TKUntyped)
        g !acc_e = tlet acc_e $ \ (!acc1, !_e) ->
          tlet acc1 $ \ !acc ->
          tlet (unHFun f acc_e) $ \ (accRes1, bRes1) ->
          tlet bRes1 $ \ !bRes ->
            -- TODO: adding a bang before accRes and bRes was causing
            -- `error "tunshare: used not at PrimalSpan"` to fire;
            -- check again, understand and document
            ttuple accRes1
                   (HVectorPseudoTensor $ dmkHVector $ acc V.++ bRes)
        dg :: forall f. ADReady f
           => InterpretationTarget f (TKProduct (TKProduct TKUntyped TKUntyped)
                                                (TKProduct TKUntyped TKUntyped))
           -> InterpretationTarget f (TKProduct TKUntyped TKUntyped)
        dg !dacc_de_acc_e =
          tlet dacc_de_acc_e $ \(!dacc_de, !_acc_e) ->
          tlet dacc_de $ \ (!dacc1, !_de) ->
          tlet dacc1 $ \ !dacc ->
          tlet (unHFun df dacc_de_acc_e) $ \ (!accRes1, !bRes1) ->
          tlet bRes1 $ \ !bRes ->
            ttuple accRes1 (HVectorPseudoTensor $ dmkHVector $ dacc V.++ bRes)
        rg :: forall f. ADReady f
           => InterpretationTarget f (TKProduct (TKProduct TKUntyped TKUntyped)
                                                (TKProduct TKUntyped TKUntyped))
           -> InterpretationTarget f (TKProduct TKUntyped TKUntyped)
        rg !args = tlet args $ \ (!dx_db, !acc_e) ->
                   tlet dx_db $ \ (!dx1, !db1) ->
                   tlet db1 $ \ !db ->
          let (dbacc, dbRes) = hvToPair db
              dx_dbRes = ttuple dx1 (HVectorPseudoTensor $ dmkHVector dbRes)
          in tlet (unHFun rf (ttuple dx_dbRes acc_e))
             $ \ (!daccRes1, !deRes1) ->
                 tlet daccRes1 $ \ !daccRes ->
                   ttuple (HVectorPseudoTensor $ dmkHVector
                           $ V.zipWith addDynamic daccRes dbacc)
                          deRes1
        pUnshared = dmapAccumRDer (Proxy @ranked)
                                  k accShs codomainShs eShs
                                  (dlambda @ranked (FTKProduct accShs eShs)
                                   $ HFun g)
                                  (dlambda @ranked
                                     (FTKProduct (FTKProduct accShs eShs)
                                                 (FTKProduct accShs eShs))
                                   $ HFun dg)
                                  (dlambda @ranked
                                     (FTKProduct (FTKProduct accShs codomainShs)
                                                 (FTKProduct accShs eShs))
                                   $ HFun rg)
                                  (HVectorPseudoTensor $ dmkHVector acc0) es
        (accFin1, qbs1) = tunpair pUnshared
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        accFin = dunHVector $ unHVectorPseudoTensor accFin1
        qbs = dunHVector $ unHVectorPseudoTensor qbs1
        q = V.take accLen qbs
        bs = V.drop accLen qbs
        !_A = assert (voidHVectorMatches (replicate1VoidHVector k bShsH) bs) ()
        dual = wrapDelta $ MapAccumR k accShs bShs eShs q (dunHVector $ unHVectorPseudoTensor es) df rf acc0' es'
    in ( HVectorPseudoTensor $ ahhToHVector accFin (Project1G dual)
       , HVectorPseudoTensor $ ahhToHVector bs (Project2G dual) )
  dmapAccumLDer _ !k accShs@(FTKUntyped accShsH) bShs@(FTKUntyped bShsH)
                eShs@(FTKUntyped eShsH) f df rf acc0D esD =
    assert (voidHVectorMatches (replicate1VoidHVector k eShsH)
                               (unHVectorPseudoTensor esD)
            && voidHVectorMatches accShsH (unHVectorPseudoTensor acc0D)) $
    let (acc0, acc0') = unADValHVector $ unHVectorPseudoTensor acc0D
        (esUnshared, es') = unADValHVector $ unHVectorPseudoTensor esD
        es = tshare $ HVectorPseudoTensor $ dmkHVector esUnshared
        codomainShs = FTKUntyped $ accShsH V.++ bShsH
        accLen = V.length accShsH
        hvToPair :: forall f. HVector f -> (HVector f, HVector f)
        hvToPair = V.splitAt accLen
        g :: forall f. ADReady f
          => InterpretationTarget f (TKProduct TKUntyped TKUntyped)
          -> InterpretationTarget f (TKProduct TKUntyped TKUntyped)
        g !acc_e = tlet acc_e $ \ (!acc1, !_e) ->
          tlet acc1 $ \ !acc ->
          tlet (unHFun f acc_e) $ \ (accRes1, bRes1) ->
          tlet bRes1 $ \ !bRes ->
            -- TODO: adding a bang before accRes and bRes was causing
            -- `error "tunshare: used not at PrimalSpan"` to fire;
            -- check again, understand and document
            ttuple accRes1
                   (HVectorPseudoTensor $ dmkHVector $ acc V.++ bRes)
        dg :: forall f. ADReady f
           => InterpretationTarget f (TKProduct (TKProduct TKUntyped TKUntyped)
                                                (TKProduct TKUntyped TKUntyped))
           -> InterpretationTarget f (TKProduct TKUntyped TKUntyped)
        dg !dacc_de_acc_e =
          tlet dacc_de_acc_e $ \(!dacc_de, !_acc_e) ->
          tlet dacc_de $ \ (!dacc1, !_de) ->
          tlet dacc1 $ \ !dacc ->
          tlet (unHFun df dacc_de_acc_e) $ \ (!accRes1, !bRes1) ->
          tlet bRes1 $ \ !bRes ->
            ttuple accRes1 (HVectorPseudoTensor $ dmkHVector $ dacc V.++ bRes)
        rg :: forall f. ADReady f
           => InterpretationTarget f (TKProduct (TKProduct TKUntyped TKUntyped)
                                                (TKProduct TKUntyped TKUntyped))
           -> InterpretationTarget f (TKProduct TKUntyped TKUntyped)
        rg !args = tlet args $ \ (!dx_db, !acc_e) ->
                   tlet dx_db $ \ (!dx1, !db1) ->
                   tlet db1 $ \ !db ->
          let (dbacc, dbRes) = hvToPair db
              dx_dbRes = ttuple dx1 (HVectorPseudoTensor $ dmkHVector dbRes)
          in tlet (unHFun rf (ttuple dx_dbRes acc_e))
             $ \ (!daccRes1, !deRes1) ->
                 tlet daccRes1 $ \ !daccRes ->
                   ttuple (HVectorPseudoTensor $ dmkHVector
                           $ V.zipWith addDynamic daccRes dbacc)
                          deRes1
        pUnshared = dmapAccumLDer (Proxy @ranked)
                                  k accShs codomainShs eShs
                                  (dlambda @ranked (FTKProduct accShs eShs)
                                   $ HFun g)
                                  (dlambda @ranked
                                     (FTKProduct (FTKProduct accShs eShs)
                                                 (FTKProduct accShs eShs))
                                   $ HFun dg)
                                  (dlambda @ranked
                                     (FTKProduct (FTKProduct accShs codomainShs)
                                                 (FTKProduct accShs eShs))
                                   $ HFun rg)
                                  (HVectorPseudoTensor $ dmkHVector acc0) es
        (accFin1, qbs1) = tunpair pUnshared
        -- This code makes sense only thanks to HVector being a representation
        -- of tuples in the struct of arrays format.
        accFin = dunHVector $ unHVectorPseudoTensor accFin1
        qbs = dunHVector $ unHVectorPseudoTensor qbs1
        q = V.take accLen qbs
        bs = V.drop accLen qbs
        !_A = assert (voidHVectorMatches (replicate1VoidHVector k bShsH) bs) ()
        dual = wrapDelta $ MapAccumL k accShs bShs eShs q (dunHVector $ unHVectorPseudoTensor es) df rf acc0' es'
    in ( HVectorPseudoTensor $ ahhToHVector accFin (Project1G dual)
       , HVectorPseudoTensor $ ahhToHVector bs (Project2G dual) )

aDValToHVector
  :: (HVectorOf ranked ~ HVector ranked, RankedOf (ShapedOf ranked) ~ ranked)
  => ADVal (HVectorPseudoTensor ranked) r y -> HVector (ADVal ranked)
aDValToHVector (D (HVectorPseudoTensor h) (HVectorPseudoTensor h')) =
  ahhToHVector h h'

-- `Float '()` instead of `r y` is needed to avoid
-- `Ambiguous type variables ‘r1’, ‘y1’ arising from a use of ‘crev’`
-- in contexts like `crev (hVectorADValToADVal . f)`.
hVectorADValToADVal
  :: forall ranked. HVectorTensor ranked (ShapedOf ranked)
  => HVector (ADVal ranked) -> ADVal (HVectorPseudoTensor ranked) Float '()
hVectorADValToADVal hv =
  let (!as, !as') = unADValHVector hv
  in dDnotShared (HVectorPseudoTensor $ dmkHVector as)
                 (HVectorPseudoTensor $ HToH as')

unADValHVector
  :: HVector (ADVal f)
  -> (HVector f, HVector (Dual f))
unADValHVector = V.unzip . V.map unADValDynamicTensor

unADValDynamicTensor
  :: DynamicTensor (ADVal f)
  -> (DynamicTensor f, DynamicTensor (Dual f))
unADValDynamicTensor (DynamicRanked (D t t')) =
  (DynamicRanked t, DynamicRanked t')
unADValDynamicTensor (DynamicShaped (D t t')) =
  (DynamicShaped t, DynamicShaped t')
unADValDynamicTensor (DynamicRankedDummy p1 p2) =
  (DynamicRankedDummy p1 p2, DynamicRankedDummy p1 p2)
unADValDynamicTensor (DynamicShapedDummy p1 p2) =
  (DynamicShapedDummy p1 p2, DynamicShapedDummy p1 p2)

unADValInterpretation
  :: forall y ranked.
     ( HVectorTensor ranked (ShapedOf ranked), ProductTensor ranked
     , RankedOf (ShapedOf ranked) ~ ranked )
  => STensorKindType y
  -> InterpretationTarget (ADVal ranked) y
  -> ( InterpretationTarget ranked y
     , InterpretationTarget (Dual ranked) y )
unADValInterpretation stk t = case stk of
  STKR{} -> let D u u' = t in (u, u')
  STKS{} -> let D u u' = t in (u, u')
  STKProduct stk1 stk2 ->
    let (!u, !u') = unADValInterpretation stk1 $ fst t in
    let (!v, !v') = unADValInterpretation stk2 $ snd t
    in (ttuple u v, ttuple u' v')
  STKUntyped ->
    let (!u, !v) = unADValHVector $ unHVectorPseudoTensor t
    in (HVectorPseudoTensor $ dmkHVector u, HVectorPseudoTensor $ HToH v)

-- TODO: not dead code: will be used in dletHVectorInHVector.
aDValHVector :: ADReadyNoLet f
             => HVector f -> HVector (Dual f) -> HVector (ADVal f)
aDValHVector = V.zipWith aDValDynamicTensor

-- TODO: Apparently other combinations occur in dletHVectorInHVector. Why?
aDValDynamicTensor :: ADReadyNoLet f
                   => DynamicTensor f -> DynamicTensor (Dual f)
                   -> DynamicTensor (ADVal f)
aDValDynamicTensor (DynamicRanked @r1 @n1 t) (DynamicRanked @r2 @n2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameNat (Proxy @n1) (Proxy @n2) =
    DynamicRanked (dDnotShared t t')
aDValDynamicTensor (DynamicShaped @r1 @sh1 t) (DynamicShaped @r2 @sh2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
    DynamicShaped (dDnotShared t t')
aDValDynamicTensor (DynamicRankedDummy @r1 @sh1 _ _)
                   (DynamicRanked @r2 @n2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- matchingRank @sh1 @n2 =
    withListShape (shapeT @sh1) $ \(sh4 :: IShR n4) ->
      gcastWith (unsafeCoerce Refl :: n4 :~: X.Rank sh1) $
      DynamicRanked (dDnotShared (rzero sh4) t')
aDValDynamicTensor (DynamicShapedDummy @r1 @sh1 _ _)
                   (DynamicShaped @r2 @sh2 t')
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
    DynamicShaped (dDnotShared (srepl 0) t')
-- TODO: explain how these remaining cases arise (maybe ADVal (ADVal)?)
aDValDynamicTensor (DynamicRanked @r1 @n1 t')
                   (DynamicRankedDummy @r2 @sh2 _ _)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- matchingRank @sh2 @n1 =
    withListShape (shapeT @sh2) $ \(sh4 :: IShR n4) ->
      gcastWith (unsafeCoerce Refl :: n4 :~: X.Rank sh2) $
      DynamicRanked (dDnotShared t' (DeltaR $ ZeroR sh4))
aDValDynamicTensor (DynamicShaped @r1 @sh1 t')
                   (DynamicShapedDummy @r2 @sh2 _ _)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
    DynamicShaped (dDnotShared t' (DeltaS ZeroS))
aDValDynamicTensor (DynamicRankedDummy @r1 @sh1 _ _)
                   (DynamicRankedDummy @r2 @sh2 _ _)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
     DynamicRankedDummy @r1 @sh1 Proxy Proxy
aDValDynamicTensor (DynamicShapedDummy @r1 @sh1 _ _)
                   (DynamicShapedDummy @r2 @sh2 _ _)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameShape @sh1 @sh2 =
    DynamicShapedDummy @r1 @sh1 Proxy Proxy
aDValDynamicTensor u v = error $ "aDValDynamicTensor: wrong arguments: ("
                                 ++ show u ++ ", " ++ show v ++ ")"
