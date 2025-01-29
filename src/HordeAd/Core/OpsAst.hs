{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for AST terms. Most of these instances
-- vectorize any terms starting with the build constructor.
-- The AST term instances can be used as building blocks for 'ADVal'
-- instances defined in "TensorADVal" but may also be used standalone.
module HordeAd.Core.OpsAst
  ( forwardPassByInterpretation
  , revArtifactFromForwardPass, revProduceArtifact
  , fwdArtifactFromForwardPass, fwdProduceArtifact
  ) where

import Prelude

import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (type (+))
import Data.Type.Equality (gcastWith)
import Data.Type.Ord (Compare)

import Data.Array.Nested (type (++), Product, Rank, KnownShS (..), KnownShX (..), ShX (..), ShS (..))
import Data.Array.Mixed.Types (Init, unsafeCoerceRefl)
import Data.Array.Mixed.Shape (shxInit, IShX, ssxFromShape, withKnownShX)
import Data.Array.Nested.Internal.Shape (shsRank, shsPermutePrefix, shrRank, shsInit, withKnownShS)
import Data.Array.Mixed.Permutation qualified as Permutation

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInline
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.AstVectorize
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersAst
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.DeltaEval
import HordeAd.Core.Delta
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * Symbolic reverse and forward derivative computation

forwardPassByInterpretation
  :: forall x z. TensorKind x
  => (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodShare PrimalSpan x
  -> AstVarName FullSpan x
  -> AstTensor AstMethodLet FullSpan x
  -> ADVal (AstRaw PrimalSpan) z
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit hVectorPrimal var hVector =
  let deltaInputs = generateDeltaInputs $ ftkAst hVectorPrimal
      varInputs = dDnotShared (AstRaw hVectorPrimal) deltaInputs
      ast = g hVector
      env = extendEnv var varInputs envInit
  in interpretAst env ast

revArtifactFromForwardPass
  :: forall x z. (TensorKind x, TensorKind z)
  => Bool
  -> (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullTensorKind x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revArtifactFromForwardPass #-}
revArtifactFromForwardPass hasDt forwardPass ftk
 | Dict <- lemTensorKindOfAD (stensorKind @x)
 , Dict <- lemTensorKindOfAD (stensorKind @z) =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varPrimal, hVectorPrimal, var, hVector) = funToAstRev ftk in
  let -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D primalBody delta) = forwardPass hVectorPrimal var hVector in
  let (!varDt, !astDt) =
        funToAst (aDFTK $ ftkAst $ unAstRaw primalBody) id in
  let mdt = if hasDt then Just astDt else Nothing
      !gradient = gradientFromDelta ftk primalBody (AstRaw <$> mdt) delta
      !unGradient = unshareAstTensor $ unAstRaw gradient
      !unPrimal = unshareAstTensor $ unAstRaw primalBody
  in ( AstArtifactRev varDt varPrimal unGradient unPrimal
     , delta )

revProduceArtifact
  :: forall x z. (TensorKind x, TensorKind z)
  => Bool
  -> (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullTensorKind x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifact #-}
revProduceArtifact hasDt g envInit =
  revArtifactFromForwardPass hasDt (forwardPassByInterpretation g envInit)

fwdArtifactFromForwardPass
  :: forall x z. (TensorKind x, TensorKind z)
  => (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullTensorKind x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdArtifactFromForwardPass #-}
fwdArtifactFromForwardPass forwardPass ftk
 | Dict <- lemTensorKindOfAD (stensorKind @x)
 , Dict <- lemTensorKindOfAD (stensorKind @z) =
  let !(!varPrimalD, hVectorD, varPrimal, hVectorPrimal, var, hVector) =
        funToAstFwd ftk in
  let !(D primalBody delta) = forwardPass hVectorPrimal var hVector in
  let !derivative = derivativeFromDelta @x delta (AstRaw hVectorD)
      !unDerivative = unshareAstTensor $ unAstRaw derivative
      !unPrimal = unshareAstTensor $ unAstRaw primalBody
  in ( AstArtifactFwd varPrimalD varPrimal unDerivative unPrimal
     , delta )

fwdProduceArtifact
  :: forall x z. (TensorKind x, TensorKind z)
  => (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullTensorKind x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdProduceArtifact #-}
fwdProduceArtifact f envInit =
  fwdArtifactFromForwardPass (forwardPassByInterpretation f envInit)


-- * AstTensor instances

instance TensorKind y
         => TermValue (AstTensor AstMethodLet FullSpan y) where
  type Value (AstTensor AstMethodLet FullSpan y) = RepN y
  fromValue t =
    fromPrimal $ astConcrete (tftkG (stensorKind @y) $ unRepN t) t

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize
  :: (TensorKind z, AstSpan s)
  => SNat k -> (AstInt AstMethodLet -> AstTensor AstMethodLet s z)
  -> AstTensor AstMethodLet s (BuildTensorKind k z)
astBuild1Vectorize k f = build1Vectorize k $ funToAstI f

{-
-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDelta
  :: FullTensorKind TKUntyped
  -> HVectorPseudoTensor (AstRaw PrimalSpan) Float '()
  -> Maybe (HVectorPseudoTensor (AstRaw PrimalSpan) Float '())
  -> Delta (AstRaw PrimalSpan) TKUntyped
  -> AstRaw PrimalSpan TKUntyped #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState (AstRaw PrimalSpan) -> EvalState (AstRaw PrimalSpan) #-}
-}

instance AstSpan s => LetTensor (AstTensor AstMethodLet s) where
  tlet u f = astLetFun u f
  toShare t = AstRaw $ AstToShare t
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tunshare =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> unshareAstTensor . unAstRaw
      _ -> error "tunshare: used not at PrimalSpan"
  tfromS @_ @z = astFromS (stensorKind @z)

-- The checks and error messages in these function result in complete
-- shape-checking of the ranked and mixed user code (shaped is already
-- fully checked by Haskell).
instance AstSpan s => BaseTensor (AstTensor AstMethodLet s) where
  tconstantTarget = constantTarget
  taddTarget = addTarget
  rshape t = case ftkAst t of
    FTKR sh _ -> sh
  rminIndex @_ @r2 @n a = case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) (stensorKind @(TKR n r2))
          . fromPrimal . AstMinIndexS . primalPart . astSFromR @sh $ a
        ZSS -> error "xminIndex: impossible empty shape"
  rmaxIndex @_ @r2 @n a = case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) (stensorKind @(TKR n r2))
          . fromPrimal . AstMaxIndexS . primalPart . astSFromR @sh $ a
        ZSS -> error "xmaxIndex: impossible empty shape"
  rfloor @_ @r2 @n a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) (stensorKind @(TKR n r2))
        . fromPrimal . AstFloorS . primalPart . astSFromR @sh $ a

  riota @r n =
    withSNat n $ \(SNat @n) ->
      astFromS (stensorKind @(TKR 1 r)) $ fromPrimal $ AstIotaS @n @r
  rindex @_ @m @n a ix = case ftkAst a of
    FTKR @_ @x shmshn _ | SNat <- shrRank shmshn ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        withKnownShS (dropShS @m sh) $
        astFromS @(TKS2 (Drop m sh) x) (stensorKind @(TKR2 n x))
        $ astIndexStepS @(Take m sh) @(Drop m sh)
                        (astSFromR @sh a) (ixrToIxs ix)
  rsum v = withSNat (rlength v) $ \snat -> astSum snat stensorKind v
  rscatter @_ @m @_ @p shpshn0 t f = case ftkAst t of
    FTKR @_ @x shmshn0 x | SNat <- shrRank shmshn0
                         , SNat <- shrRank shpshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop p shpshn :~: shpshn) $
        case testEquality (dropShS @p shpshn) (dropShS @m shmshn) of
          Just Refl ->
            astFromS @(TKS2 shpshn x) (STKR (shrRank shpshn0) (ftkToStk x))
            $ astScatterS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                          (astSFromR @shmshn t)
            $ funToAstIxS (ixrToIxs . f . ixsToIxr)
                -- this introduces new variable names
          _ -> error $ "rscatter: shapes don't match: "
                       ++ show (dropShS @p shpshn, dropShS @m shmshn)
  rfromVector l = withSNat (V.length l) $ \snat -> astFromVector snat l
  rreplicate k = withSNat k $ \snat -> astReplicate snat stensorKind
  rappend @r @n u v = case ftkAst u of
    FTKR shu' _ | SNat <- shrRank shu' -> case ftkAst v of
      FTKR shv' _ ->
        withCastRS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastRS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                astFromS (stensorKind @(TKR2 (1 + n) r))
                $ astAppendS @mu @mv @restu (astSFromR @shu u)
                                            (astSFromR @shv v)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  rslice @r @n1 i n a = case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          withSNat i $ \(SNat @i) -> withSNat n $ \(SNat @n) ->
          withSNat (valueOf @m - i - n) $ \(SNat @k) ->
            gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
            astFromS @(TKS2 (n ': rest) x) (stensorKind @(TKR2 (1 + n1) r))
            . astSliceS @i @n @k . astSFromR @sh $ a
        ZSS -> error "xslice: impossible shape"
  rreverse @r @n a = case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          astFromS @(TKS2 sh x) (stensorKind @(TKR2 (1 + n) r))
          . astReverseS . astSFromR @sh $ a
        ZSS -> error "xreverse: impossible shape"
  rtranspose @r @n permr a = case ftkAst a of
    FTKR @_ @x sh' _  ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        Permutation.permFromList permr $ \(perm :: Permutation.Perm perm) ->
          gcastWith (unsafeCoerceRefl :: Compare (Rank perm) (Rank sh) :~: LT) $
          trustMeThisIsAPermutation @perm $
          case shsPermutePrefix perm sh of
            (sh2 :: ShS sh2) ->
              withKnownShS sh $
              withKnownShS sh2 $
              gcastWith (unsafeCoerceRefl :: Rank sh2 :~: Rank sh) $
              astFromS @(TKS2 sh2 x) (stensorKind @(TKR2 n r))
              . astTransposeS perm . astSFromR @sh $ a
  rreshape @r @_ @m sh2' a = case ftkAst a of
    FTKR @_ @x sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
      withCastRS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        astFromS @(TKS2 sh2 x) (stensorKind @(TKR2 m r))
        . astReshapeS . astSFromR @sh $ a
  rbuild1 k f = withSNat k $ \snat -> astBuild1Vectorize snat f
  rgather @_ @m @_ @p shmshn0 t f = case ftkAst t of
    FTKR shpshn0 x | SNat <- shrRank shpshn0
                   , SNat <- shrRank shmshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop p shpshn :~: shpshn) $
        case testEquality (dropShS @p shpshn) (dropShS @m shmshn) of
          Just Refl ->
            astFromS (STKR (shrRank shmshn0) (ftkToStk x))
            $ astGatherStepS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                             (astSFromR t)
            $ funToAstIxS (ixrToIxs . f . ixsToIxr)
                -- this introduces new variable names
          _ -> error $ "rgather: shapes don't match: "
                       ++ show (dropShS @p shpshn, dropShS @m shmshn)
  rcast @_ @r2 @n a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) (stensorKind @(TKR n r2))
        . astCastS . astSFromR @sh $ a
  rfromIntegral @_ @r2 @n a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) (stensorKind @(TKR n r2))
        . fromPrimal . astFromIntegralS . primalPart . astSFromR @sh $ a
  rzip @y @z @n a = case ftkAst a of
    FTKProduct (FTKR sh' _) (FTKR _ _) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFun a $ \a3 ->
          let (a31, a32) = tunpairDup a3
          in astFromS @(TKS2 sh (TKProduct y z))
                      (stensorKind @(TKR2 n (TKProduct y z)))
             $ AstZipS $ astPair (astSFromR @sh a31)
                                 (astSFromR @sh a32)
  runzip @y @z @n a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFun (AstUnzipS $ astSFromR @sh a) $ \b3 ->
          let (b31, b32) = tunpairDup b3
          in astPair (astFromS @(TKS2 sh y) (stensorKind @(TKR2 n y)) b31)
                     (astFromS @(TKS2 sh z) (stensorKind @(TKR2 n z)) b32)
  kfromR = astFromS stensorKind . astSFromR @'[]
  rfromK @r = astFromS (stensorKind @(TKR 0 r)) . astSFromK

  sminIndex @_ @_ @sh @n a =
    withKnownShS (shsInit (SNat @n :$$ knownShS @sh)) $
    fromPrimal . AstMinIndexS . primalPart $ a
  smaxIndex @_ @_ @sh @n a =
    withKnownShS (shsInit (SNat @n :$$ knownShS @sh)) $
    fromPrimal . AstMaxIndexS . primalPart $ a
  sfloor = fromPrimal . AstFloorS . primalPart

  siota = fromPrimal $ AstIotaS
  sindex v ix =
    astIndexStepS v ix
  ssum = astSum SNat stensorKind
  sscatter @_ @shm @shn @shp t f =
    astScatterS @shm @shn @shp t
    $ funToAstIxS f
        -- this introduces new variable names
  sfromVector @_ @k l = astFromVector (SNat @k) l
  sreplicate = astReplicate SNat stensorKind
  sappend u v = astAppendS u v
  sslice @_ @i Proxy Proxy = astSliceS @i
  sreverse = astReverseS
  stranspose perm = astTransposeS perm
  sreshape = astReshapeS
  sbuild1 @k f = astBuild1Vectorize (SNat @k) f
  sgather @_ @shm @shn @shp t f =
    astGatherStepS @shm @shn @shp t
    $ funToAstIxS f
        -- this introduces new variable names
  scast = astCastS
  sfromIntegral = fromPrimal . astFromIntegralS . primalPart
  szip = AstZipS
  sunzip = AstUnzipS
  kfromS = astFromS stensorKind
  sfromK = astSFromK

  xminIndex @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) (stensorKind @(TKX (Init sh') r2))
          . fromPrimal . AstMinIndexS @rest @n
          . primalPart . astSFromX @sh @sh' $ a
        ZSS -> error "xminIndex: impossible shape"
  xmaxIndex @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) (stensorKind @(TKX (Init sh') r2))
          . fromPrimal . AstMaxIndexS @rest @n
          . primalPart . astSFromX @sh @sh' $ a
        ZSS -> error "xmaxIndex: impossible shape"
  xfloor @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) (stensorKind @(TKX sh' r2))
        . fromPrimal . AstFloorS . primalPart . astSFromX @sh @sh' $ a

  xiota @n @r = astFromS (stensorKind @(TKX '[Just n] r))
                $ fromPrimal $ AstIotaS @n @r
  xshape t = case ftkAst t of
    FTKX sh _ -> sh
  xindex @_ @sh1 @sh2 a ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 _ | SNat <- ssxRank (knownShX @sh1) ->
      withCastXS sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        withKnownShS (takeShS @(Rank sh1) sh) $
        withKnownShS (dropShS @(Rank sh1) sh) $
        astFromS @(TKS2 (Drop (Rank sh1) sh) x)
                 (stensorKind @(TKX2 sh2 x))
        $ astIndexStepS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                        (astSFromX @sh @sh1sh2 a)
                        (ixxToIxs ix)
  xsum = astSum SNat stensorKind
  xscatter @_ @shm @_ @shp shpshn0 t f = case ftkAst t of
    FTKX shmshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        astFromS (STKX (ssxFromShape shpshn0) (ftkToStk x))
        $ astScatterS @(Take (Rank shm) shmshn)
                      @(Drop (Rank shm) shmshn)
                      @(Take (Rank shp) shpshn) (astSFromX t)
        $ funToAstIxS (ixxToIxs . f . ixsToIxx)
            -- this introduces new variable names
  xfromVector @_ @k l = astFromVector (SNat @k) l
  xreplicate = astReplicate SNat stensorKind
  xappend @r @sh u v = case ftkAst u of
    FTKX @shu' shu' _ -> case ftkAst v of
      FTKX @shv' shv' _ ->
        withCastXS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastXS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                astFromS (stensorKind @(TKX2 (Nothing ': sh) r))
                $ astAppendS @mu @mv @restu (astSFromX @shu @shu' u)
                                            (astSFromX @shv @shv' v)
              ZSS -> error "xappend: impossible shape"
          ZSS -> error "xappend: impossible shape"
  xslice @r @i @n @k @sh2 Proxy Proxy a = case ftkAst a of
    FTKX @sh' @x sh'@(_ :$% _) _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
          astFromS @(TKS2 (n ': rest) x)
                   (stensorKind @(TKX2 (Just n ': sh2) r))
          . astSliceS @i @n @k . astSFromX @sh @sh' $ a
        ZSS -> error "xslice: impossible shape"
  xreverse a = case ftkAst a of
    FTKX @sh' @x sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          astFromS @(TKS2 sh x) (stensorKind @(TKX2 sh' x))
          . astReverseS . astSFromX @sh @sh' $ a
        ZSS -> error "xreverse: impossible shape"
  xtranspose @perm perm a = case ftkAst a of
    FTKX @sh' @x sh' _ -> case shxPermutePrefix perm sh' of
      (sh2' :: IShX sh2') ->
        withKnownShX (ssxFromShape sh2') $
        withCastXS sh' $ \(sh :: ShS sh) ->
        withCastXS sh2' $ \(sh2 :: ShS sh2) ->
          withKnownShS sh $
          withKnownShS sh2 $
          gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm sh :~: sh2) $
          astFromS @(TKS2 sh2 x) (stensorKind @(TKX2 sh2' x))
          . astTransposeS perm . astSFromX @sh @sh' $ a
  xreshape sh2' a = case ftkAst a of
    FTKX @sh' @x sh' x ->
      withCastXS sh' $ \(sh :: ShS sh) ->
      withCastXS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        astFromS @(TKS2 sh2 x) (STKX (ssxFromShape sh2') (ftkToStk x))
        . astReshapeS . astSFromX @sh @sh' $ a
  xbuild1 @k f = astBuild1Vectorize (SNat @k) f
  xgather @_ @shm @_ @shp shmshn0 t f = case ftkAst t of
    FTKX shpshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        astFromS (STKX (ssxFromShape shmshn0) (ftkToStk x))
        $ astGatherStepS @(Take (Rank shm) shmshn)
                         @(Drop (Rank shm) shmshn)
                         @(Take (Rank shp) shpshn) (astSFromX t)
        $ funToAstIxS (ixxToIxs . f . ixsToIxx)
            -- this introduces new variable names
  xcast @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) (stensorKind @(TKX sh' r2))
        . astCastS . astSFromX @sh @sh' $ a
  xfromIntegral @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astFromS @(TKS sh r2) (stensorKind @(TKX sh' r2))
        . fromPrimal . astFromIntegralS
        . primalPart . astSFromX @sh @sh' $ a
  xzip @y @z @sh' a = case ftkAst a of
    FTKProduct (FTKX sh' _) (FTKX _ _) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFun a $ \a3 ->
          let (a31, a32) = tunpairDup a3
          in astFromS @(TKS2 sh (TKProduct y z))
                      (stensorKind @(TKX2 sh' (TKProduct y z)))
             $ AstZipS $ astPair (astSFromX @sh @sh' a31)
                                 (astSFromX @sh @sh' a32)
  xunzip @y @z @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFun (AstUnzipS $ astSFromX @sh @sh' a) $ \b3 ->
          let (b31, b32) = tunpairDup b3
          in astPair (astFromS @(TKS2 sh y) (stensorKind @(TKX2 sh' y)) b31)
                     (astFromS @(TKS2 sh z) (stensorKind @(TKX2 sh' z)) b32)
  kfromX = astFromS stensorKind . astSFromX @'[]
  xfromK @r = astFromS (stensorKind @(TKX '[] r)) . astSFromK

  kfloor = fromPrimal . AstFloorK . primalPart
  kfromIntegral = fromPrimal . astFromIntegralK . primalPart
  kcast = astCastK

  sfromR = astSFromR
  sfromX = astSFromX

  xnestR sh =
    withKnownShX sh $
    astXNestR
  xnestS sh =
    withKnownShX sh $
    astXNestS
  xnest sh =
    withKnownShX sh $
    astXNest
  xunNestR = astXUnNestR
  xunNestS = astXUnNestS
  xunNest = astXUnNest

  tpair t1 t2 = astPair t1 t2
  tproject1 = astProject1
  tproject2 = astProject2
  tftk _stk = ftkAst
  tcond !stk !b !u !v | Dict <- lemTensorKindOfSTK stk = astCond b u v
  tprimalPart stk t | Dict <- lemTensorKindOfSTK stk = primalPart t
  tdualPart stk t | Dict <- lemTensorKindOfSTK stk = dualPart t
  tfromPrimal stk t | Dict <- lemTensorKindOfSTK stk = fromPrimal t
  tfromDual stk t | Dict <- lemTensorKindOfSTK stk = fromDual t
  tconcrete ftk a | Dict <- lemTensorKindOfSTK (ftkToStk ftk) =
    fromPrimal $ astConcrete ftk a
  tlambda shss f =
    let (var, ast) = funToAst shss $ \ !ll ->
          unHFun f ll
    in AstLambda (var, shss, ast)
  tApply t ll = astApply t ll
  tunpairDup t = (tproject1 t, tproject2 t)
  -- TODO: (still) relevant?
  -- In this instance, these three ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  drev @x ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x) =
    -- we don't have an AST constructor to hold it, so we compute
    --
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let -- No bangs here, because this goes under lambda and may be unneeded
        -- or even incorrect (and so, e.g., trigger
        -- `error "tunshare: used not at PrimalSpan"`, because no derivative
        -- should be taken of spans other than PrimalSpan)
        (AstArtifactRev _varDt var gradient _primal, _delta) =
          revProduceArtifact False (unHFun f) emptyEnv ftkx
        (varP, ast) = funToAst ftkx $ \ !astP ->
          astLet var astP
          $ simplifyInline gradient
    in AstLambda (varP, ftkx, ast)
  drevDt @x @z ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x)
                      , Dict <- lemTensorKindOfAD (stensorKind @z) =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactRev varDt var gradient primal, _delta) =
          revProduceArtifact True (unHFun f) emptyEnv ftkx
        ftkz = aDFTK $ ftkAst primal
        ftk2 = FTKProduct ftkz ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          astLet varDt (astProject1 astP)
          $ astLet var (astProject2 astP)
          $ simplifyInline gradient
    in AstLambda (varP, ftk2, ast)
  dfwd @x @z ftkx f | Dict <- lemTensorKindOfAD (stensorKind @x)
                    , Dict <- lemTensorKindOfAD (stensorKind @z) =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactFwd varDs var derivative _primal, _delta) =
          fwdProduceArtifact (unHFun f) emptyEnv ftkx
        ftk2 = FTKProduct (aDFTK ftkx) ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          astLet varDs (astProject1 astP)
          $ astLet var (astProject2 astP)
          $ simplifyInline derivative
    in AstLambda (varP, ftk2, ast)
  dmapAccumRDer _ !k _ !bShs !eShs f df rf acc0 es =
    astMapAccumRDer k bShs eShs f df rf acc0 es
  dmapAccumLDer _ !k _ !bShs !eShs f df rf acc0 es =
    astMapAccumLDer k bShs eShs f df rf acc0 es


-- * AstRaw instances

instance AstSpan s => ShareTensor (AstRaw s) where
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tshare t = case unAstRaw t of
    u | astIsSmall True u -> t
    AstVar{} -> t
    AstShare{} -> t
    AstPrimalPart(AstVar{}) -> t
    AstDualPart(AstVar{}) -> t
    AstFromPrimal(AstVar{}) -> t
    AstFromDual(AstVar{}) -> t
    u -> AstRaw $ fun1ToAst $ \ !var -> AstShare var u
  tunpair (AstRaw (AstPair t1 t2)) = (AstRaw t1, AstRaw t2)
  tunpair t = let tShared = tshare t
              in (tproject1 tShared, tproject2 tShared)
  tfromSShare @_ @z (AstRaw a) = AstRaw $ AstFromS (stensorKind @z) a

instance AstSpan s => BaseTensor (AstRaw s) where
  tconstantTarget = constantTarget
  taddTarget = addTarget
  rshape t = case ftkAst $ unAstRaw t of
    FTKR sh _ -> sh
  rminIndex @_ @r2 @n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (stensorKind @(TKR n r2))
          . fromPrimal . AstMinIndexS . primalPart . AstSFromR @sh $ a
        ZSS -> error "xminIndex: impossible shape"
  rmaxIndex @_ @r2 @n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (stensorKind @(TKR n r2))
          . fromPrimal . AstMaxIndexS . primalPart . AstSFromR @sh $ a
        ZSS -> error "xmaxIndex: impossible shape"
  rfloor @_ @r2 @n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKR n r2))
        . fromPrimal . AstFloorS . primalPart . AstSFromR @sh $ a

  riota @r n =
    AstRaw
    $ withSNat n $ \(SNat @n) ->
        AstFromS (stensorKind @(TKR 1 r)) $ fromPrimal $ AstIotaS @n @r
  rindex @_ @m @n (AstRaw a) ix = AstRaw $ case ftkAst a of
    FTKR @_ @x shmshn _ | SNat <- shrRank shmshn ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        withKnownShS (dropShS @m sh) $
        AstFromS @(TKS2 (Drop m sh) x) (stensorKind @(TKR2 n x))
        $ AstIndexS @(Take m sh) @(Drop m sh)
                    (AstSFromR @sh a) (ixrToIxs (unAstRaw <$> ix))
  rsum v = withSNat (rlength v) $ \snat ->
             AstRaw . AstSum snat stensorKind . unAstRaw $ v
  rscatter @_ @m @_ @p shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR @_ @x shmshn0 x | SNat <- shrRank shmshn0
                         , SNat <- shrRank shpshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        AstFromS @(TKS2 shpshn x) (STKR (shrRank shpshn0) (ftkToStk x))
        $ AstScatterS @(Take m shmshn)
                      @(Drop m shmshn)
                      @(Take p shpshn) (AstSFromR @shmshn t)
        $ funToAstIxS (fmap unAstRaw . ixrToIxs . f . ixsToIxr . fmap AstRaw)
            -- this introduces new variable names
  rfromVector l = withSNat (V.length l) $ \snat ->
    AstRaw . AstFromVector snat . V.map unAstRaw $ l
  rreplicate k = withSNat k $ \snat ->
    AstRaw . AstReplicate snat stensorKind . unAstRaw
  rappend @r @n (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKR shu' _ | SNat <- shrRank shu' -> case ftkAst v of
      FTKR shv' _ ->
        withCastRS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastRS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                AstFromS (stensorKind @(TKR2 (1 + n) r))
                $ AstAppendS @mu @mv @restu (AstSFromR @shu u)
                                            (AstSFromR @shv v)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  rslice @r @n1 i n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          withSNat i $ \(SNat @i) -> withSNat n $ \(SNat @n) ->
          withSNat (valueOf @m - i - n) $ \(SNat @k) ->
            gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
            AstFromS @(TKS2 (n ': rest) x) (stensorKind @(TKR2 (1 + n1) r))
            . AstSliceS @i @n @k . AstSFromR @sh $ a
        ZSS -> error "xslice: impossible shape"
  rreverse  @r @n(AstRaw a) = AstRaw $ case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          AstFromS @(TKS2 sh x) (stensorKind @(TKR2 (1 + n) r))
          . AstReverseS . AstSFromR @sh $ a
        ZSS -> error "xreverse: impossible shape"
  rtranspose @r @n permr (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR @_ @x sh' _  ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        Permutation.permFromList permr $ \(perm :: Permutation.Perm perm) ->
          gcastWith (unsafeCoerceRefl :: Compare (Rank perm) (Rank sh) :~: LT) $
          trustMeThisIsAPermutation @perm $
          case shsPermutePrefix perm sh of
            (sh2 :: ShS sh2) ->
              withKnownShS sh $
              withKnownShS sh2 $
              gcastWith (unsafeCoerceRefl :: Rank sh2 :~: Rank sh) $
              AstFromS @(TKS2 sh2 x) (stensorKind @(TKR2 n r))
              . AstTransposeS perm . AstSFromR @sh $ a
  rreshape @r @_ @m sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR @_ @x sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
      withCastRS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        AstFromS @(TKS2 sh2 x) (stensorKind @(TKR2 m r))
        . AstReshapeS . AstSFromR @sh $ a
  rbuild1 k f = withSNat k $ \snat ->
    AstRaw $ AstBuild1 snat
    $ funToAstI  -- this introduces new variable names
    $ unAstRaw . f . AstRaw
  rgather @_ @m @_ @p shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR shpshn0 x | SNat <- shrRank shpshn0
                   , SNat <- shrRank shmshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        AstFromS (STKR (shrRank shmshn0) (ftkToStk x))
        $ AstGatherS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                     (AstSFromR t)
        $ funToAstIxS (fmap unAstRaw . ixrToIxs . f . ixsToIxr . fmap AstRaw)
            -- this introduces new variable names
  rcast @_ @r2 @n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKR n r2))
        . AstCastS . AstSFromR @sh $ a
  rfromIntegral @_ @r2 @n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKR n r2))
        . fromPrimal . AstFromIntegralS . primalPart . AstSFromR @sh $ a
  rzip @y @z @n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKProduct (FTKR sh' _) (FTKR _ _) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        let (a31, a32) = tunpair $ AstRaw a
        in AstFromS @(TKS2 sh (TKProduct y z))
                    (stensorKind @(TKR2 n (TKProduct y z)))
           $ AstZipS $ AstPair (AstSFromR @sh $ unAstRaw a31)
                               (AstSFromR @sh $ unAstRaw a32)
  runzip @y @z @n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        let b3 = AstUnzipS $ AstSFromR @sh a
            (b31, b32) = tunpair $ AstRaw b3
        in AstPair (AstFromS @(TKS2 sh y) (stensorKind @(TKR2 n y))
                    $ unAstRaw b31)
                   (AstFromS @(TKS2 sh z) (stensorKind @(TKR2 n z))
                    $ unAstRaw b32)
  kfromR = AstRaw . AstFromS stensorKind . AstSFromR @'[] . unAstRaw
  rfromK @r =
    AstRaw . AstFromS (stensorKind @(TKR 0 r)) . AstSFromK . unAstRaw

  xminIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (stensorKind @(TKX (Init sh') r2))
          . fromPrimal . AstMinIndexS @rest @n
          . primalPart . AstSFromX @sh @sh' $ a
        ZSS -> error "xminIndex: impossible shape"
  xmaxIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (stensorKind @(TKX (Init sh') r2))
          . fromPrimal . AstMaxIndexS @rest @n
          . primalPart . AstSFromX @sh @sh' $ a
        ZSS -> error "xmaxIndex: impossible shape"
  xfloor @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKX sh' r2))
        . fromPrimal . AstFloorS . primalPart . AstSFromX @sh @sh' $ a

  xiota @n @r = AstRaw $ AstFromS (stensorKind @(TKX '[Just n] r))
                $ fromPrimal $ AstIotaS @n @r
  xshape t = case ftkAst $ unAstRaw t of
    FTKX sh _ -> sh
  xindex @_ @sh1 @sh2 (AstRaw a) ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 _ | SNat <- ssxRank (knownShX @sh1) ->
      withCastXS sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        withKnownShS (takeShS @(Rank sh1) sh) $
        withKnownShS (dropShS @(Rank sh1) sh) $
        AstRaw $ AstFromS @(TKS2 (Drop (Rank sh1) sh) x)
                          (stensorKind @(TKX2 sh2 x))
        $ AstIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (AstSFromX @sh @sh1sh2 a)
                    (ixxToIxs (unAstRaw <$> ix))
  xsum = AstRaw . AstSum SNat stensorKind . unAstRaw
  xscatter @_ @shm @_ @shp shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shmshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        AstFromS (STKX (ssxFromShape shpshn0) (ftkToStk x))
        $ AstScatterS @(Take (Rank shm) shmshn)
                      @(Drop (Rank shm) shmshn)
                      @(Take (Rank shp) shpshn) (AstSFromX t)
        $ funToAstIxS (fmap unAstRaw . ixxToIxs . f . ixsToIxx . fmap AstRaw)
            -- this introduces new variable names
  xfromVector @_ @k l =
    AstRaw . AstFromVector (SNat @k) . V.map unAstRaw $ l
  xreplicate = AstRaw . AstReplicate SNat stensorKind . unAstRaw
  xappend @r @sh (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKX @shu' shu' _ -> case ftkAst v of
      FTKX @shv' shv' _ ->
        withCastXS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastXS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                AstFromS (stensorKind @(TKX2 (Nothing ': sh) r))
                $ AstAppendS @mu @mv @restu (AstSFromX @shu @shu' u)
                                            (AstSFromX @shv @shv' v)
              ZSS -> error "xappend: impossible shape"
          ZSS -> error "xappend: impossible shape"
  xslice @r @i @n @k @sh2 Proxy Proxy (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' @x sh'@(_ :$% _) _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
          AstFromS @(TKS2 (n ': rest) x)
                   (stensorKind @(TKX2 (Just n ': sh2) r))
          . AstSliceS @i @n @k . AstSFromX @sh @sh' $ a
        ZSS -> error "xslice: impossible shape"
  xreverse (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' @x sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          AstFromS @(TKS2 sh x) (stensorKind @(TKX2 sh' x))
          . AstReverseS . AstSFromX @sh @sh' $ a
        ZSS -> error "xreverse: impossible shape"
  xtranspose @perm perm (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' @x sh' _ -> case shxPermutePrefix perm sh' of
      (sh2' :: IShX sh2') ->
        withKnownShX (ssxFromShape sh2') $
        withCastXS sh' $ \(sh :: ShS sh) ->
        withCastXS sh2' $ \(sh2 :: ShS sh2) ->
          withKnownShS sh $
          withKnownShS sh2 $
          gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm sh :~: sh2) $
          AstFromS @(TKS2 sh2 x) (stensorKind @(TKX2 sh2' x))
          . AstTransposeS perm . AstSFromX @sh @sh' $ a
  xreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' @x sh' x ->
      withCastXS sh' $ \(sh :: ShS sh) ->
      withCastXS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        AstFromS @(TKS2 sh2 x) (STKX (ssxFromShape sh2') (ftkToStk x))
        . AstReshapeS . AstSFromX @sh @sh' $ a
  xbuild1 @k f = AstRaw $ AstBuild1 (SNat @k)
                 $ funToAstI  -- this introduces new variable names
                 $ unAstRaw . f . AstRaw
  xgather @_ @shm @_ @shp shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shpshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        AstFromS (STKX (ssxFromShape shmshn0) (ftkToStk x))
        $ AstGatherS @(Take (Rank shm) shmshn)
                     @(Drop (Rank shm) shmshn)
                     @(Take (Rank shp) shpshn) (AstSFromX t)
        $ funToAstIxS (fmap unAstRaw . ixxToIxs . f . ixsToIxx . fmap AstRaw)
            -- this introduces new variable names
  xcast @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKX sh' r2))
        . AstCastS . AstSFromX @sh @sh' $ a
  xfromIntegral @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKX sh' r2))
        . fromPrimal . AstFromIntegralS
        . primalPart . AstSFromX @sh @sh' $ a
  xzip @y @z @sh' (AstRaw a) = case ftkAst a of
    FTKProduct (FTKX sh' _) (FTKX _ _) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstRaw
        $ let (a31, a32) = tunpair $ AstRaw a
          in AstFromS @(TKS2 sh (TKProduct y z))
                      (stensorKind @(TKX2 sh' (TKProduct y z)))
             $ AstZipS $ AstPair (AstSFromX @sh @sh' $ unAstRaw a31)
                                 (AstSFromX @sh @sh' $ unAstRaw a32)
  xunzip @y @z @sh' (AstRaw a) = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstRaw
        $ let b3 = AstRaw $ AstUnzipS $ AstSFromX @sh @sh' a
              (b31, b32) = tunpair b3
          in AstPair (AstFromS @(TKS2 sh y) (stensorKind @(TKX2 sh' y))
                      $ unAstRaw b31)
                     (AstFromS @(TKS2 sh z) (stensorKind @(TKX2 sh' z))
                      $ unAstRaw b32)
  kfromX = AstRaw . AstFromS stensorKind . AstSFromX @'[] . unAstRaw
  xfromK @r = AstRaw . AstFromS (stensorKind @(TKX '[] r))
                   . AstSFromK . unAstRaw

  sminIndex @_ @_ @sh @n a =
    withKnownShS (shsInit (SNat @n :$$ knownShS @sh)) $
    AstRaw . fromPrimal . AstMinIndexS . primalPart . unAstRaw $ a
  smaxIndex @_ @_ @sh @n a =
    withKnownShS (shsInit (SNat @n :$$ knownShS @sh)) $
    AstRaw . fromPrimal . AstMaxIndexS . primalPart . unAstRaw $ a
  sfloor = AstRaw . fromPrimal . AstFloorS . primalPart . unAstRaw
  siota = AstRaw . fromPrimal $ AstIotaS
  sindex v ix = AstRaw $ AstIndexS (unAstRaw v) (unAstRaw <$> ix)
  ssum = AstRaw . AstSum SNat stensorKind . unAstRaw
  sscatter @_ @shm @shn @shp t f =
    AstRaw $ AstScatterS @shm @shn @shp (unAstRaw t)
           $ funToAstIxS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  sfromVector @_ @k l =
    AstRaw . AstFromVector (SNat @k) . V.map unAstRaw $ l
  sreplicate = AstRaw . AstReplicate SNat stensorKind . unAstRaw
  sappend u v = AstRaw $ AstAppendS (unAstRaw u) (unAstRaw v)
  sslice @_ @i Proxy Proxy = AstRaw . AstSliceS @i . unAstRaw
  sreverse = AstRaw . AstReverseS . unAstRaw
  stranspose perm = AstRaw . AstTransposeS perm . unAstRaw
  sreshape = AstRaw . AstReshapeS . unAstRaw
  sbuild1 @k f = AstRaw $ AstBuild1 (SNat @k)
                 $ funToAstI  -- this introduces new variable names
                 $ unAstRaw . f . AstRaw
  sgather @_ @shm @shn @shp t f =
    AstRaw $ AstGatherS @shm @shn @shp (unAstRaw t)
           $ funToAstIxS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  scast = AstRaw . AstCastS . unAstRaw
  sfromIntegral =
    AstRaw . fromPrimal . AstFromIntegralS . primalPart . unAstRaw
  szip = AstRaw . AstZipS . unAstRaw
  sunzip = AstRaw . AstUnzipS . unAstRaw
  kfromS = AstRaw . AstFromS stensorKind . unAstRaw
  sfromK = AstRaw . AstSFromK . unAstRaw

  kfloor = AstRaw . fromPrimal . AstFloorK . primalPart . unAstRaw
  kcast = AstRaw . AstCastK . unAstRaw
  kfromIntegral = AstRaw . fromPrimal . AstFromIntegralK
                  . primalPart . unAstRaw

  rfromS @x @sh | SNat <- shsRank (knownShS @sh) =
    AstRaw . AstFromS (stensorKind @(TKR2 (Rank sh) x)) . unAstRaw
  sfromR = AstRaw . cAstSFromR . unAstRaw
  sfromX = AstRaw . cAstSFromX . unAstRaw
  xfromS @_ @sh' @x = AstRaw . AstFromS (stensorKind @(TKX2 sh' x)) . unAstRaw

  xnestR sh =
    withKnownShX sh $
    AstRaw . AstXNestR . unAstRaw
  xnestS sh =
    withKnownShX sh $
    AstRaw . AstXNestS . unAstRaw
  xnest sh =
    withKnownShX sh $
    AstRaw . AstXNest . unAstRaw
  xunNestR = AstRaw . AstXUnNestR . unAstRaw
  xunNestS = AstRaw . AstXUnNestS . unAstRaw
  xunNest = AstRaw . AstXUnNest . unAstRaw

  tpair t1 t2 = AstRaw $ AstPair (unAstRaw t1) (unAstRaw t2)
  tproject1 t = AstRaw $ AstProject1 $ unAstRaw t
  tproject2 t = AstRaw $ AstProject2 $ unAstRaw t
  tftk _stk = ftkAst . unAstRaw
  tcond !stk !b !u !v | Dict <- lemTensorKindOfSTK stk =
    AstRaw $ AstCond b (unAstRaw u) (unAstRaw v)
  tprimalPart stk t | Dict <- lemTensorKindOfSTK stk =
    AstRaw $ primalPart $ unAstRaw t
  tdualPart stk t | Dict <- lemTensorKindOfSTK stk = dualPart $ unAstRaw t
  tfromPrimal stk t | Dict <- lemTensorKindOfSTK stk =
    AstRaw $ fromPrimal $ unAstRaw t
  tfromDual stk t | Dict <- lemTensorKindOfSTK stk =
    AstRaw $ fromDual t
  tconcrete ftk a | Dict <- lemTensorKindOfSTK (ftkToStk ftk) =
    AstRaw $ fromPrimal $ AstConcrete ftk a
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tApply t ll = AstRaw $ AstApply t (unAstRaw ll)
  -- TODO: (still) relevant?
  -- In this instance, these two ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  --
  -- TODO: dupe?
  -- These three methods are called at this type in delta evaluation via
  -- dmapAccumR and dmapAccumL, they have to work. We could refrain from
  -- simplifying the resulting terms, but it's not clear that's more consistent.
  drev = drev @(AstTensor AstMethodLet PrimalSpan)
  drevDt = drevDt @(AstTensor AstMethodLet PrimalSpan)
  dfwd = dfwd @(AstTensor AstMethodLet PrimalSpan)
  dmapAccumRDer @_ @bShs @eShs _ !k _ !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstRaw $ AstMapAccumRDer k bShs eShs f df rf (unAstRaw acc0) (unAstRaw es)
  dmapAccumLDer @_ @bShs @eShs _ !k _ !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstRaw $ AstMapAccumLDer k bShs eShs f df rf (unAstRaw acc0) (unAstRaw es)


-- * AstNoVectorize instances

instance AstSpan s => LetTensor (AstNoVectorize s) where
  tlet u f = AstNoVectorize
             $ tlet (unAstNoVectorize u)
                    (unAstNoVectorize . f . AstNoVectorize)
  toShare t = toShare $ unAstNoVectorize t
  tfromS = AstNoVectorize . tfromS . unAstNoVectorize

instance AstSpan s => BaseTensor (AstNoVectorize s) where
  tconstantTarget r ftk = AstNoVectorize $ tconstantTarget r ftk
  taddTarget stk a b = AstNoVectorize $ taddTarget stk (unAstNoVectorize a)
                                                       (unAstNoVectorize b)
  rshape = rshape . unAstNoVectorize
  rminIndex = AstNoVectorize . rminIndex . unAstNoVectorize
  rmaxIndex = AstNoVectorize . rmaxIndex . unAstNoVectorize
  rfloor = AstNoVectorize . rfloor . unAstNoVectorize
  riota = AstNoVectorize . riota
  rindex v ix =
    AstNoVectorize $ rindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  rsum = AstNoVectorize . rsum . unAstNoVectorize
  rscatter sh t f =
    AstNoVectorize $ rscatter sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  rfromVector = AstNoVectorize . rfromVector . V.map unAstNoVectorize
  rreplicate k = AstNoVectorize . rreplicate k . unAstNoVectorize
  rappend u v =
    AstNoVectorize $ rappend (unAstNoVectorize u) (unAstNoVectorize v)
  rslice i n = AstNoVectorize . rslice i n . unAstNoVectorize
  rreverse = AstNoVectorize . rreverse . unAstNoVectorize
  rtranspose perm = AstNoVectorize . rtranspose perm . unAstNoVectorize
  rreshape sh = AstNoVectorize . rreshape sh . unAstNoVectorize
  rbuild1 k f = withSNat k $ \snat ->
    AstNoVectorize $ AstBuild1 snat
    $ funToAstI  -- this introduces new variable names
    $ unAstNoVectorize . f . AstNoVectorize
  rgather sh t f =
    AstNoVectorize $ rgather sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  rcast = AstNoVectorize . rcast . unAstNoVectorize
  rfromIntegral = AstNoVectorize . rfromIntegral . unAstNoVectorize
  rzip = AstNoVectorize . rzip . unAstNoVectorize
  runzip = AstNoVectorize . runzip . unAstNoVectorize
  kfromR = AstNoVectorize . kfromR . unAstNoVectorize
  rfromK = AstNoVectorize . rfromK . unAstNoVectorize

  xminIndex = AstNoVectorize . xminIndex . unAstNoVectorize
  xmaxIndex = AstNoVectorize . xmaxIndex . unAstNoVectorize
  xfloor = AstNoVectorize . xfloor . unAstNoVectorize

  xiota @n = AstNoVectorize $ xiota @_ @n
  xshape = xshape . unAstNoVectorize
  xindex v ix =
    AstNoVectorize $ xindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  xsum = AstNoVectorize . xsum . unAstNoVectorize
  xscatter @_ @shm @shn @shp sh t f =
    AstNoVectorize $ xscatter @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  xfromVector = AstNoVectorize . xfromVector . V.map unAstNoVectorize
  xreplicate = AstNoVectorize . xreplicate . unAstNoVectorize

  xappend u v =
    AstNoVectorize $ xappend (unAstNoVectorize u) (unAstNoVectorize v)
  xslice proxy1 proxy2 =
    AstNoVectorize . xslice proxy1 proxy2 . unAstNoVectorize
  xreverse = AstNoVectorize . xreverse . unAstNoVectorize
  xtranspose perm =
    AstNoVectorize . xtranspose perm . unAstNoVectorize
  xreshape sh = AstNoVectorize . xreshape sh . unAstNoVectorize
  xbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k)
                 $ funToAstI  -- this introduces new variable names
                 $ unAstNoVectorize . f . AstNoVectorize
  xgather @_ @shm @shn @shp sh t f =
    AstNoVectorize $ xgather @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  xcast = AstNoVectorize . xcast . unAstNoVectorize
  xfromIntegral = AstNoVectorize . xfromIntegral . unAstNoVectorize
  xzip = AstNoVectorize . xzip . unAstNoVectorize
  xunzip = AstNoVectorize . xunzip . unAstNoVectorize
  kfromX = AstNoVectorize . kfromX . unAstNoVectorize
  xfromK = AstNoVectorize . xfromK . unAstNoVectorize

  sminIndex = AstNoVectorize . sminIndex . unAstNoVectorize
  smaxIndex = AstNoVectorize . smaxIndex . unAstNoVectorize
  sfloor = AstNoVectorize . sfloor . unAstNoVectorize
  siota = AstNoVectorize siota
  sindex v ix =
    AstNoVectorize $ sindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  ssum = AstNoVectorize . ssum . unAstNoVectorize
  sscatter @_ @shm @shn @shp t f =
    AstNoVectorize $ sscatter @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  sfromVector = AstNoVectorize . sfromVector . V.map unAstNoVectorize
  sreplicate = AstNoVectorize . sreplicate . unAstNoVectorize
  sappend u v =
    AstNoVectorize $ sappend (unAstNoVectorize u) (unAstNoVectorize v)
  sslice proxy1 proxy2 =
    AstNoVectorize . sslice proxy1 proxy2 . unAstNoVectorize
  sreverse = AstNoVectorize . sreverse . unAstNoVectorize
  stranspose perm =
    AstNoVectorize . stranspose perm . unAstNoVectorize
  sreshape = AstNoVectorize . sreshape . unAstNoVectorize
  sbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k)
                 $ funToAstI  -- this introduces new variable names
                 $ unAstNoVectorize . f . AstNoVectorize
  sgather @_ @shm @shn @shp t f =
    AstNoVectorize $ sgather @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  scast = AstNoVectorize . scast . unAstNoVectorize
  sfromIntegral = AstNoVectorize . sfromIntegral . unAstNoVectorize
  szip = AstNoVectorize . szip . unAstNoVectorize
  sunzip = AstNoVectorize . sunzip . unAstNoVectorize
  kfromS = AstNoVectorize . kfromS . unAstNoVectorize
  sfromK = AstNoVectorize . sfromK . unAstNoVectorize

  kfloor = AstNoVectorize . kfloor . unAstNoVectorize
  kcast = AstNoVectorize . kcast . unAstNoVectorize
  kfromIntegral = AstNoVectorize . kfromIntegral . unAstNoVectorize

  sfromR = AstNoVectorize . sfromR . unAstNoVectorize
  sfromX = AstNoVectorize . sfromX . unAstNoVectorize

  xnestR sh =
    withKnownShX sh $ AstNoVectorize . xnestR sh . unAstNoVectorize
  xnestS sh =
    withKnownShX sh $ AstNoVectorize . xnestS sh . unAstNoVectorize
  xnest sh =
    withKnownShX sh $ AstNoVectorize . xnest sh . unAstNoVectorize
  xunNestR = AstNoVectorize . xunNestR . unAstNoVectorize
  xunNestS = AstNoVectorize . xunNestS . unAstNoVectorize
  xunNest = AstNoVectorize . xunNest . unAstNoVectorize

  tpair t1 t2 =
    AstNoVectorize $ tpair (unAstNoVectorize t1) (unAstNoVectorize t2)
  tproject1 t = AstNoVectorize $ tproject1 $ unAstNoVectorize t
  tproject2 t = AstNoVectorize $ tproject2 $ unAstNoVectorize t
  tftk _stk = ftkAst . unAstNoVectorize
  tcond !stk !b !u !v =
    AstNoVectorize $ tcond stk b (unAstNoVectorize u) (unAstNoVectorize v)
  tfromPrimal stk t = AstNoVectorize $ tfromPrimal stk $ unAstNoVectorize t
  tprimalPart stk t = AstNoVectorize $ tprimalPart stk $ unAstNoVectorize t
  tdualPart stk t = tdualPart stk $ unAstNoVectorize t
  tfromDual stk t = AstNoVectorize $ tfromDual stk t
  tconcrete ftk a = AstNoVectorize $ tconcrete ftk a
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tApply t ll = AstNoVectorize $ tApply t (unAstNoVectorize ll)
  tunpairDup a = let (b, c) =  tunpairDup $ unAstNoVectorize a
                 in (AstNoVectorize b, AstNoVectorize c)
  drev = drev @(AstTensor AstMethodLet PrimalSpan)
  drevDt = drevDt @(AstTensor AstMethodLet PrimalSpan)
  dfwd = dfwd @(AstTensor AstMethodLet PrimalSpan)
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstNoVectorize $ dmapAccumRDer Proxy k accShs bShs eShs f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstNoVectorize $ dmapAccumLDer Proxy k accShs bShs eShs f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)


-- * AstNoSimplify instances

astLetFunNoSimplify
  :: forall y z s s2. (TensorKind z, AstSpan s)
  => AstTensor AstMethodLet s y
  -> (AstTensor AstMethodLet s y -> AstTensor AstMethodLet s2 z)
  -> AstTensor AstMethodLet s2 z
astLetFunNoSimplify a f | astIsSmall True a = f a
                            -- too important an optimization to skip
astLetFunNoSimplify a f = case a of
  AstFromS @y2 stkz v | Dict <- lemTensorKindOfSTK (ftkToStk (ftkAst v)) ->
    let (var, ast) = funToAst (ftkAst v) (f . AstFromS @y2 stkz)
    in AstLet var v ast
  AstFromPrimal (AstFromS @y2 stkz vRaw)
   | Dict <- lemTensorKindOfSTK (ftkToStk (ftkAst vRaw)) ->
    let v = AstFromPrimal vRaw
        (var, ast) = funToAst (ftkAst v) (f . AstFromS @y2 stkz)
    in AstLet var v ast
  _ -> case ftkAst a of
    ftk@(FTKR @_ @x2 sh' x) | SNat <- shrRank sh'
                            , Dict <- lemTensorKindOfSTK (ftkToStk x) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        let (var, ast) =
              funToAst (FTKS sh x) (f . AstFromS @(TKS2 sh x2) (ftkToStk ftk))
        in AstLet var (AstSFromR @sh a) ast
             -- safe, because subsitution ruled out above
    ftk@(FTKX @_ @x sh' x) | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShX (ssxFromShape sh') $
        withKnownShS sh $
        let (var, ast) =
              funToAst (FTKS sh x) (f . AstFromS @(TKS2 sh x) (ftkToStk ftk))
        in AstLet var (AstSFromX @sh a) ast
    -- TODO: also recursively product, though may be not worth it
    ftk | Dict <- lemTensorKindOfSTK (ftkToStk ftk) ->
          let (var, ast) = funToAst ftk f
          in AstLet var a ast

instance AstSpan s => LetTensor (AstNoSimplify s) where
  tlet u f = AstNoSimplify
             $ astLetFunNoSimplify (unAstNoSimplify u)
                                   (unAstNoSimplify . f . AstNoSimplify)
  toShare t = AstRaw $ AstToShare $ unAstNoSimplify t
  tfromS @_ @z = AstNoSimplify . AstFromS (stensorKind @z) . unAstNoSimplify

instance AstSpan s => BaseTensor (AstNoSimplify s) where
  tconstantTarget = constantTarget
  taddTarget = addTarget
  rshape t = case ftkAst $ unAstNoSimplify t of
    FTKR sh _ -> sh
  rminIndex @_ @r2 @n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (stensorKind @(TKR n r2))
          . fromPrimal . AstMinIndexS . primalPart . AstSFromR @sh $ a
        ZSS -> error "xminIndex: impossible shape"
  rmaxIndex @_ @r2 @n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (stensorKind @(TKR n r2))
          . fromPrimal . AstMaxIndexS . primalPart . AstSFromR @sh $ a
        ZSS -> error "xmaxIndex: impossible shape"
  rfloor @_ @r2 @n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKR n r2))
        . fromPrimal . AstFloorS . primalPart . AstSFromR @sh $ a

  riota @r n =
    AstNoSimplify
    $ withSNat n $ \(SNat @n) ->
        AstFromS (stensorKind @(TKR 1 r))  $ fromPrimal $ AstIotaS @n @r
  rindex @_ @m @n (AstNoSimplify a) ix = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x shmshn _ | SNat <- shrRank shmshn ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        withKnownShS (dropShS @m sh) $
        AstFromS @(TKS2 (Drop m sh) x) (stensorKind @(TKR2 n x))
        $ AstIndexS @(Take m sh) @(Drop m sh)
                    (AstSFromR @sh a) (ixrToIxs (unAstNoSimplify <$> ix))
  rsum v = withSNat (rlength v) $ \snat ->
             AstNoSimplify . AstSum snat stensorKind . unAstNoSimplify $ v
  rscatter @_ @m @_ @p
           shpshn0 (AstNoSimplify t) f = AstNoSimplify $ case ftkAst t of
    FTKR @_ @x shmshn0 x | SNat <- shrRank shmshn0
                         , SNat <- shrRank shpshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        AstFromS @(TKS2 shpshn x) (STKR (shrRank shpshn0) (ftkToStk x))
        $ AstScatterS @(Take m shmshn)
                      @(Drop m shmshn)
                      @(Take p shpshn) (AstSFromR @shmshn t)
        $ funToAstIxS (fmap unAstNoSimplify . ixrToIxs . f
                       . ixsToIxr . fmap AstNoSimplify)
            -- this introduces new variable names
  rfromVector l = withSNat (V.length l) $ \snat ->
    AstNoSimplify . AstFromVector snat . V.map unAstNoSimplify $ l
  rreplicate k = withSNat k $ \snat ->
    AstNoSimplify . AstReplicate snat stensorKind . unAstNoSimplify
  rappend @r @n (AstNoSimplify u) (AstNoSimplify v) = AstNoSimplify
                                                      $ case ftkAst u of
    FTKR shu' _ | SNat <- shrRank shu' -> case ftkAst v of
      FTKR shv' _ ->
        withCastRS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastRS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                AstFromS (stensorKind @(TKR2 (1 + n) r))
                $ AstAppendS @mu @mv @restu (AstSFromR @shu u)
                                            (AstSFromR @shv v)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  rslice @r @n1 i n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          withSNat i $ \(SNat @i) -> withSNat n $ \(SNat @n) ->
          withSNat (valueOf @m - i - n) $ \(SNat @k) ->
            gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
            AstFromS @(TKS2 (n ': rest) x) (stensorKind @(TKR2 (1 + n1) r))
            . AstSliceS @i @n @k . AstSFromR @sh $ a
        ZSS -> error "xslice: impossible shape"
  rreverse @r @n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x sh' _ | SNat <- shrRank sh' ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          AstFromS @(TKS2 sh x) (stensorKind @(TKR2 (1 + n) r))
          . AstReverseS . AstSFromR @sh $ a
        ZSS -> error "xreverse: impossible shape"
  rtranspose @r @n permr (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x sh' _  ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        Permutation.permFromList permr $ \(perm :: Permutation.Perm perm) ->
          gcastWith (unsafeCoerceRefl :: Compare (Rank perm) (Rank sh) :~: LT) $
          trustMeThisIsAPermutation @perm $
          case shsPermutePrefix perm sh of
            (sh2 :: ShS sh2) ->
              withKnownShS sh $
              withKnownShS sh2 $
              gcastWith (unsafeCoerceRefl :: Rank sh2 :~: Rank sh) $
              AstFromS @(TKS2 sh2 x) (stensorKind @(TKR2 n r))
              . AstTransposeS perm . AstSFromR @sh $ a
  rreshape @r @_ @m sh2' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR @_ @x sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
      withCastRS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        AstFromS @(TKS2 sh2 x) (stensorKind @(TKR2 m r))
        . AstReshapeS . AstSFromR @sh $ a
  rbuild1 k f = withSNat k $ \snat ->
    AstNoSimplify
    $ astBuild1Vectorize snat (unAstNoSimplify . f . AstNoSimplify)
  rgather @_ @m @_ @p
          shmshn0 (AstNoSimplify t) f = AstNoSimplify $ case ftkAst t of
    FTKR shpshn0 x | SNat <- shrRank shpshn0
                   , SNat <- shrRank shmshn0 ->
      withCastRS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastRS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop m shmshn :~: shpshn) $
        withKnownShS (takeShS @m shmshn) $
        withKnownShS (dropShS @m shmshn) $
        withKnownShS (takeShS @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        AstFromS (STKR (shrRank shmshn0) (ftkToStk x))
        $ AstGatherS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                     (AstSFromR t)
        $ funToAstIxS (fmap unAstNoSimplify . ixrToIxs . f
                       . ixsToIxr . fmap AstNoSimplify)
            -- this introduces new variable names
  rcast @_ @r2 @n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKR n r2))
        . AstCastS . AstSFromR @sh $ a
  rfromIntegral @_ @r2 @n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKR n r2))
        . fromPrimal . AstFromIntegralS . primalPart . AstSFromR @sh $ a
  rzip @y @z @n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKProduct (FTKR sh' _) (FTKR _ _) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFunNoSimplify a $ \a3 ->
          let (a31, a32) = tunpairDup a3
          in AstFromS @(TKS2 sh (TKProduct y z))
                      (stensorKind @(TKR2 n (TKProduct y z)))
             $ AstZipS $ AstPair (AstSFromR @sh a31)
                                 (AstSFromR @sh a32)
  runzip @y @z @n (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        astLetFunNoSimplify (AstUnzipS $ AstSFromR @sh a) $ \b3 ->
          let (b31, b32) = tunpairDup b3
          in AstPair (AstFromS @(TKS2 sh y) (stensorKind @(TKR2 n y)) b31)
                     (AstFromS @(TKS2 sh z) (stensorKind @(TKR2 n z)) b32)
  kfromR =
    AstNoSimplify . AstFromS stensorKind . AstSFromR @'[] . unAstNoSimplify
  rfromK @r =
    AstNoSimplify . AstFromS (stensorKind @(TKR 0 r))
    . AstSFromK . unAstNoSimplify

  xminIndex @_ @r2 (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (stensorKind @(TKX (Init sh') r2))
          . fromPrimal . AstMinIndexS @rest @n
          . primalPart . AstSFromX @sh @sh' $ a
        ZSS -> error "xminIndex: impossible shape"
  xmaxIndex @_ @r2 (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ rest ->
          withKnownShX (ssxFromShape $ shxInit sh') $
          withKnownShS rest $
          withKnownShS (shsInit sh) $
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (stensorKind @(TKX (Init sh') r2))
          . fromPrimal . AstMaxIndexS @rest @n
          . primalPart . AstSFromX @sh @sh' $ a
        ZSS -> error "xmaxIndex: impossible shape"
  xfloor @_ @r2 @sh' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKX sh' r2))
        . fromPrimal . AstFloorS . primalPart . AstSFromX @sh @sh' $ a

  xiota @n @r = AstNoSimplify $ AstFromS (stensorKind @(TKX '[Just n] r))
                $ fromPrimal $ AstIotaS @n @r
  xshape t = case ftkAst $ unAstNoSimplify t of
    FTKX sh _ -> sh
  xindex @_ @sh1 @sh2 (AstNoSimplify a) ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 _ | SNat <- ssxRank (knownShX @sh1) ->
      withCastXS sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        withKnownShS (takeShS @(Rank sh1) sh) $
        withKnownShS (dropShS @(Rank sh1) sh) $
        AstNoSimplify $ AstFromS @(TKS2 (Drop (Rank sh1) sh) x)
                                 (stensorKind @(TKX2 sh2 x))
       $ AstIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (AstSFromX @sh @sh1sh2 a)
                    (ixxToIxs (unAstNoSimplify <$> ix))
  xsum = AstNoSimplify . AstSum SNat stensorKind . unAstNoSimplify
  xscatter @_ @shm @_ @shp shpshn0 (AstNoSimplify t) f = AstNoSimplify
                                                         $ case ftkAst t of
    FTKX shmshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        AstFromS (STKX (ssxFromShape shpshn0) (ftkToStk x))
        $ AstScatterS @(Take (Rank shm) shmshn)
                      @(Drop (Rank shm) shmshn)
                      @(Take (Rank shp) shpshn) (AstSFromX t)
        $ funToAstIxS (fmap unAstNoSimplify . ixxToIxs . f . ixsToIxx
                       . fmap AstNoSimplify)
            -- this introduces new variable names
  xfromVector @_ @k l =
    AstNoSimplify . AstFromVector (SNat @k) . V.map unAstNoSimplify $ l
  xreplicate = AstNoSimplify . AstReplicate SNat stensorKind . unAstNoSimplify
  xappend @r @sh (AstNoSimplify u) (AstNoSimplify v) = AstNoSimplify
                                                       $ case ftkAst u of
    FTKX @shu' shu' _ -> case ftkAst v of
      FTKX @shv' shv' _ ->
        withCastXS shu' $ \(shu :: ShS shu) -> case shu of
          (:$$) @mu @restu _ restu ->
            withCastXS shv' $ \(shv :: ShS shv) -> case shv of
              (:$$) @mv @restv _ _ ->
                gcastWith (unsafeCoerceRefl :: restu :~: restv) $
                withKnownShS restu $
                AstFromS (stensorKind @(TKX2 (Nothing ': sh) r))
                $ AstAppendS @mu @mv @restu (AstSFromX @shu @shu' u)
                                            (AstSFromX @shv @shv' v)
              ZSS -> error "xappend: impossible shape"
          ZSS -> error "xappend: impossible shape"
  xslice @r @i @n @k @sh2 Proxy Proxy
         (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' @x sh'@(_ :$% _) _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @m @rest _ rest ->
          withKnownShS rest $
          gcastWith (unsafeCoerceRefl :: i + n + k :~: m) $
          AstFromS @(TKS2 (n ': rest) x)
                   (stensorKind @(TKX2 (Just n ': sh2) r))
          . AstSliceS @i @n @k . AstSFromX @sh @sh' $ a
        ZSS -> error "xslice: impossible shape"
  xreverse (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' @x sh' _ ->
      withKnownShX (ssxFromShape sh') $
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        _ :$$ rest ->
          withKnownShS rest $
          AstFromS @(TKS2 sh x) (stensorKind @(TKX2 sh' x))
          . AstReverseS . AstSFromX @sh @sh' $ a
        ZSS -> error "xreverse: impossible shape"
  xtranspose @perm perm (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' @x sh' _ -> case shxPermutePrefix perm sh' of
      (sh2' :: IShX sh2') ->
        withKnownShX (ssxFromShape sh2') $
        withCastXS sh' $ \(sh :: ShS sh) ->
        withCastXS sh2' $ \(sh2 :: ShS sh2) ->
          withKnownShS sh $
          withKnownShS sh2 $
          gcastWith (unsafeCoerceRefl
                     :: Permutation.PermutePrefix perm sh :~: sh2) $
          AstFromS @(TKS2 sh2 x) (stensorKind @(TKX2 sh2' x))
          . AstTransposeS perm . AstSFromX @sh @sh' $ a
  xreshape sh2' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX @sh' @x sh' x ->
      withCastXS sh' $ \(sh :: ShS sh) ->
      withCastXS sh2' $ \(sh2 :: ShS sh2) ->
        withKnownShS sh $
        withKnownShS sh2 $
        gcastWith (unsafeCoerceRefl :: Product sh :~: Product sh2) $
        AstFromS @(TKS2 sh2 x) (STKX (ssxFromShape sh2') (ftkToStk x))
        . AstReshapeS . AstSFromX @sh @sh' $ a
  xbuild1 @k f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @k) (unAstNoSimplify . f . AstNoSimplify)
  xgather @_ @shm @_ @shp shmshn0 (AstNoSimplify t) f = AstNoSimplify
                                                        $ case ftkAst t of
    FTKX shpshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withKnownShX (ssxFromShape shmshn0) $
      withKnownShX (ssxFromShape shpshn0) $
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shm) shmshn
                      :~: shpshn) $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        AstFromS (STKX (ssxFromShape shmshn0) (ftkToStk x))
        $ AstGatherS @(Take (Rank shm) shmshn)
                     @(Drop (Rank shm) shmshn)
                     @(Take (Rank shp) shpshn) (AstSFromX t)
        $ funToAstIxS (fmap unAstNoSimplify . ixxToIxs . f . ixsToIxx
                       . fmap AstNoSimplify)
            -- this introduces new variable names
  xcast @_ @r2 @sh' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKX sh' r2))
        . AstCastS . AstSFromX @sh @sh' $ a
  xfromIntegral @_ @r2 @sh' (AstNoSimplify a) = AstNoSimplify $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstFromS @(TKS sh r2) (stensorKind @(TKX sh' r2))
        . fromPrimal . AstFromIntegralS
        . primalPart . AstSFromX @sh @sh' $ a
  xzip @y @z @sh' (AstNoSimplify a) = case ftkAst a of
    FTKProduct (FTKX sh' _) (FTKX _ _) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstNoSimplify
        $ astLetFunNoSimplify a $ \a3 ->
          let (a31, a32) = tunpairDup a3
          in AstFromS @(TKS2 sh (TKProduct y z))
                      (stensorKind @(TKX2 sh' (TKProduct y z)))
             $ AstZipS $ AstPair (AstSFromX @sh @sh' a31)
                                 (AstSFromX @sh @sh' a32)
  xunzip @y @z @sh' (AstNoSimplify a) = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        AstNoSimplify
        $ astLetFunNoSimplify (AstUnzipS $ AstSFromX @sh @sh' a) $ \b3 ->
          let (b31, b32) = tunpairDup b3
          in AstPair (AstFromS @(TKS2 sh y) (stensorKind @(TKX2 sh' y)) b31)
                     (AstFromS @(TKS2 sh z) (stensorKind @(TKX2 sh' z)) b32)
  kfromX =
    AstNoSimplify . AstFromS stensorKind . AstSFromX @'[] . unAstNoSimplify
  xfromK @r = AstNoSimplify . AstFromS (stensorKind @(TKX '[] r))
                   . AstSFromK . unAstNoSimplify

  sminIndex @_ @_ @sh @n a =
    withKnownShS (shsInit (SNat @n :$$ knownShS @sh)) $
    AstNoSimplify . fromPrimal . AstMinIndexS
                  . primalPart . unAstNoSimplify $ a
  smaxIndex @_ @_ @sh @n a =
    withKnownShS (shsInit (SNat @n :$$ knownShS @sh)) $
    AstNoSimplify . fromPrimal . AstMaxIndexS
                  . primalPart . unAstNoSimplify $ a
  sfloor = AstNoSimplify . fromPrimal . AstFloorS
           . primalPart . unAstNoSimplify
  siota = AstNoSimplify . fromPrimal $ AstIotaS
  sindex v ix =
    AstNoSimplify $ AstIndexS (unAstNoSimplify v) (unAstNoSimplify <$> ix)
  ssum = AstNoSimplify . AstSum SNat stensorKind . unAstNoSimplify
  sscatter @_ @shm @shn @shp t f =
    AstNoSimplify $ AstScatterS @shm @shn @shp (unAstNoSimplify t)
                  $ funToAstIxS
                      (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                        -- this introduces new variable names
  sfromVector @_ @k l =
    AstNoSimplify . AstFromVector (SNat @k) . V.map unAstNoSimplify $ l
  sreplicate = AstNoSimplify . AstReplicate SNat stensorKind . unAstNoSimplify
  sappend u v =
    AstNoSimplify $ AstAppendS (unAstNoSimplify u) (unAstNoSimplify v)
  sslice @_ @i Proxy Proxy = AstNoSimplify . AstSliceS @i . unAstNoSimplify
  sreverse = AstNoSimplify . AstReverseS . unAstNoSimplify
  stranspose perm =
    AstNoSimplify . AstTransposeS perm . unAstNoSimplify
  sreshape = AstNoSimplify . AstReshapeS . unAstNoSimplify
  sbuild1 @k f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @k) (unAstNoSimplify . f . AstNoSimplify)
  sgather @_ @shm @shn @shp t f =
    AstNoSimplify $ AstGatherS @shm @shn @shp (unAstNoSimplify t)
                  $ funToAstIxS
                      (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                        -- this introduces new variable names
  scast = AstNoSimplify . AstCastS . unAstNoSimplify
  sfromIntegral = AstNoSimplify . fromPrimal . AstFromIntegralS
                  . primalPart . unAstNoSimplify
  szip = AstNoSimplify . AstZipS . unAstNoSimplify
  sunzip = AstNoSimplify . AstUnzipS . unAstNoSimplify
  kfromS = AstNoSimplify . AstFromS stensorKind . unAstNoSimplify
  sfromK = AstNoSimplify . AstSFromK . unAstNoSimplify

  kfloor = AstNoSimplify . fromPrimal . AstFloorK
           . primalPart . unAstNoSimplify
  kcast = AstNoSimplify . AstCastK . unAstNoSimplify
  kfromIntegral = AstNoSimplify . fromPrimal . AstFromIntegralK
                  . primalPart . unAstNoSimplify

  sfromR = AstNoSimplify . AstSFromR . unAstNoSimplify
  sfromX = AstNoSimplify . AstSFromX . unAstNoSimplify

  xnestR sh =
    withKnownShX sh $
    AstNoSimplify . AstXNestR . unAstNoSimplify
  xnestS sh =
    withKnownShX sh $
    AstNoSimplify . AstXNestS . unAstNoSimplify
  xnest sh =
    withKnownShX sh $
    AstNoSimplify . AstXNest . unAstNoSimplify
  xunNestR = AstNoSimplify . AstXUnNestR . unAstNoSimplify
  xunNestS = AstNoSimplify . AstXUnNestS . unAstNoSimplify
  xunNest = AstNoSimplify . AstXUnNest . unAstNoSimplify

  tpair t1 t2 = AstNoSimplify $ AstPair (unAstNoSimplify t1) (unAstNoSimplify t2)
  tproject1 t = AstNoSimplify $ AstProject1 $ unAstNoSimplify t
  tproject2 t = AstNoSimplify $ AstProject2 $ unAstNoSimplify t
  tftk _stk = ftkAst . unAstNoSimplify
  tcond !stk !b !u !v | Dict <- lemTensorKindOfSTK stk =
    AstNoSimplify $ AstCond b (unAstNoSimplify u) (unAstNoSimplify v)
  tprimalPart stk t | Dict <- lemTensorKindOfSTK stk =
    AstNoSimplify $ primalPart $ unAstNoSimplify t
  tdualPart stk t | Dict <- lemTensorKindOfSTK stk =
    dualPart $ unAstNoSimplify t
  tfromPrimal stk t | Dict <- lemTensorKindOfSTK stk =
    AstNoSimplify $ fromPrimal $ unAstNoSimplify t
  tfromDual stk t | Dict <- lemTensorKindOfSTK stk =
    AstNoSimplify $ fromDual t
  tconcrete ftk a | Dict <- lemTensorKindOfSTK (ftkToStk ftk) =
    AstNoSimplify $ fromPrimal $ AstConcrete ftk a
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tApply t ll = AstNoSimplify $ AstApply t (unAstNoSimplify ll)
  tunpairDup (AstNoSimplify (AstPair t1 t2)) =  -- a tiny bit of simplification
    (AstNoSimplify t1, AstNoSimplify t2)
  tunpairDup t = (tproject1 t, tproject2 t)
  drev = drev @(AstTensor AstMethodLet PrimalSpan)
  drevDt = drevDt @(AstTensor AstMethodLet PrimalSpan)
  dfwd = dfwd @(AstTensor AstMethodLet PrimalSpan)
  dmapAccumRDer @_ @bShs @eShs _ !k _ !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstNoSimplify $ AstMapAccumRDer k bShs eShs f df rf (unAstNoSimplify acc0) (unAstNoSimplify es)
  dmapAccumLDer @_ @bShs @eShs _ !k _ !bShs !eShs f df rf acc0 es
    | Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
    , Dict <- lemTensorKindOfBuild k (stensorKind @bShs) =
      AstNoSimplify $ AstMapAccumLDer k bShs eShs f df rf (unAstNoSimplify acc0) (unAstNoSimplify es)
