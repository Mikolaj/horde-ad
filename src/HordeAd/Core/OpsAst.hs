{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for AST terms. Most of these instances
-- vectorize any term with the build constructor in the root.
-- The AST term instances can be used as building blocks for ADVal(AST)
-- instances defined in "HordeAd.Core.OpsADVal" but may also be used standalone.
module HordeAd.Core.OpsAst
  ( IncomingCotangentHandling(..)
  , forwardPassByInterpretation
  , revArtifactFromForwardPass, revProduceArtifact
  , fwdArtifactFromForwardPass, fwdProduceArtifact
  ) where

import Prelude

import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.Exts (inline)
import GHC.TypeLits (OrderingI (..), cmpNat, type (+), type (-), type (<=?))
import System.IO.Unsafe (unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (shxFromShR, shxFromShS)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Init, snatPlus, unsafeCoerceRefl)

import HordeAd.AstEngine
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
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Delta
import HordeAd.Core.DeltaEval
import HordeAd.Core.Ops
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

-- * Symbolic reverse and forward derivative computation

data IncomingCotangentHandling = UseIncomingCotangent | IgnoreIncomingCotangent

-- Here a choice is made that derivatives are PrimalSpan terms.
-- This makes them easier to simplify and expresses via type that they
-- don't introduce tangents nor cotangents, but are purely primal functions.
-- They can still be liften to dual number functions via interpretations,
-- as is done, e.g., in tgrad below.
forwardPassByInterpretation
  :: forall x z.
     (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodShare PrimalSpan x
  -> AstVarName FullSpan x
  -> AstTensor AstMethodLet FullSpan x
  -> ADVal (AstRaw PrimalSpan) z
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit astVarPrimal var astVar0 =
  let deltaInputs = generateDeltaInputs $ varNameToFTK var
      varInputs = dDnotShared (AstRaw astVarPrimal) deltaInputs
      ast = g astVar0
      env = extendEnv var varInputs envInit
  in interpretAstFull env ast

revArtifactFromForwardPass
  :: forall x z.
     IncomingCotangentHandling
  -> (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullShapeTK x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
-- Break the inline chain to prevent false positives in inspection testing
-- and protect the unsafePerformIO.
{-# NOINLINE revArtifactFromForwardPass #-}
revArtifactFromForwardPass cotangentHandling
                           forwardPass xftk = unsafePerformIO $ do
  -- IO and bangs and the compound function to fix the numbering of variables
  -- for pretty-printing and prevent sharing the impure values
  -- in tests that reset the impure counters.
  (!varPrimal, astVarPrimal, var, astVar0) <- funToAstRevIO xftk
  -- Evaluate completely after terms constructed, to free memory
  -- before gradientFromDelta allocates new memory and new FFI is started.
  let !(D primalBody delta) = forwardPass astVarPrimal var astVar0
  let zftk = ftkAst $ unAstRaw primalBody
      (!varDt, astDt) = funToAst (adFTK zftk) Nothing id
  let oneAtF = treplTarget 1 $ adFTK zftk
      !dt = case cotangentHandling of
        UseIncomingCotangent -> AstRaw astDt
        IgnoreIncomingCotangent -> oneAtF
  let !gradient = gradientFromDelta xftk zftk dt delta
      !unGradient = unshareAstTensor $ unAstRaw gradient
      !unPrimal = unshareAstTensor $ unAstRaw primalBody
  return (AstArtifactRev varDt varPrimal unGradient unPrimal, delta)

revProduceArtifact
  :: forall x z.
     IncomingCotangentHandling
  -> (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullShapeTK x
  -> AstArtifactRev x z
revProduceArtifact cotangentHandling g envInit xftk =
  fst $ inline revArtifactFromForwardPass
          cotangentHandling (forwardPassByInterpretation g envInit) xftk

fwdArtifactFromForwardPass
  :: forall x z.
     (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullShapeTK x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
-- Break the inline chain to prevent false positives in inspection testing
-- and protect the unsafePerformIO.
{-# NOINLINE fwdArtifactFromForwardPass #-}
fwdArtifactFromForwardPass forwardPass xftk = unsafePerformIO $ do
  (!varPrimalD, astVarD, varPrimal, astVarPrimal, var, astVar0)
    <- funToAstFwdIO xftk
  let !(D primalBody delta) = forwardPass astVarPrimal var astVar0
  let !derivative = derivativeFromDelta @x delta (adFTK xftk) (AstRaw astVarD)
      !unDerivative = unshareAstTensor $ unAstRaw derivative
      !unPrimal = unshareAstTensor $ unAstRaw primalBody
  return (AstArtifactFwd varPrimalD varPrimal unDerivative unPrimal, delta)

fwdProduceArtifact
  :: forall x z.
     (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullShapeTK x
  -> AstArtifactFwd x z
{-# INLINE fwdProduceArtifact #-}
fwdProduceArtifact f envInit xftk =
  fst $ inline fwdArtifactFromForwardPass
          (forwardPassByInterpretation f envInit) xftk


-- * AstTensor instances

-- | This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast tensor instances are defined, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize
  :: AstSpan s
  => SNat k -> SingletonTK y
  -> (AstInt AstMethodLet -> AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s (BuildTensorKind k y)
astBuild1Vectorize k@(SNat @k) stk f =
  build1Vectorize k stk $ funToAstI (Just (0, valueOf @k - 1)) f

instance AstSpan s => LetTensor (AstTensor AstMethodLet s) where
  ttlet = astLetFun
  ttletPrimal = astLetFun
  toShare t = AstRaw $ AstToShare t
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tunshare =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> unshareAstTensor . unAstRaw
      _ -> error "tunshare: used not at PrimalSpan"

-- | The checks and error messages in these functions result in complete
-- shape-checking of the ranked and mixed user code (shaped is already
-- fully checked by the Haskell type system).
instance AstSpan s => BaseTensor (AstTensor AstMethodLet s) where
  -- Ranked ops
  rshape t = case ftkAst t of
    FTKR sh _ -> sh
  trsum v = withSNat (rwidth v) $ \snat -> astSum snat knownSTK v
  trreplicate k = withSNat k $ \snat -> astReplicate snat knownSTK
  trindex @m @n a ix = case ftkAst a of
    FTKR @_ @x shmshn _ ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        astFromS @(TKS2 (Drop m sh) x) (knownSTK @(TKR2 n x))
        $ astIndexS @(Take m sh) @(Drop m sh)
                    (dropShS @m sh) (astSFromR @sh sh a) (ixrToIxs ix)
  trscatter @m @_ @p shpshn0 t f = case ftkAst t of
    FTKR @_ @x shmshn0 x ->
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
            astFromS @(TKS2 shpshn x) (STKR (shrRank shpshn0) (ftkToSTK x))
            $ astScatterS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                          knownShS (astSFromR shmshn t)
            $ funToAstIxS knownShS (ixrToIxs . f . ixsToIxr)
                -- this introduces new variable names
          _ -> error $ "rscatter: shapes don't match: "
                       ++ show (dropShS @p shpshn, dropShS @m shmshn)
  trgather @m @_ @p shmshn0 t f = case ftkAst t of
    FTKR shpshn0 x ->
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
            astFromS (STKR (shrRank shmshn0) (ftkToSTK x))
            $ astGatherS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                         knownShS (astSFromR shpshn t)
            $ funToAstIxS knownShS (ixrToIxs . f . ixsToIxr)
                -- this introduces new variable names
          _ -> error $ "rgather: shapes don't match: "
                       ++ show (dropShS @p shpshn, dropShS @m shmshn)
  trconcrete a = tconcrete (FTKR (Nested.rshape a) FTKScalar) (Concrete a)
  trfloor @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKR (shrRank sh') knownSTK)
        . fromPrimal . astFloorS . primalPart . astSFromR @sh sh $ a
  trfromIntegral @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKR (shrRank sh') knownSTK)
        . fromPrimal . astFromIntegralS . primalPart . astSFromR @sh sh $ a
  trcast @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKR (shsRank sh) STKScalar)
        . astCastS . astSFromR sh $ a
  trminIndex @_ @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) (STKR (shsRank rest) STKScalar)
          . fromPrimal . AstMinIndexS . primalPart . astSFromR @sh sh $ a
        ZSS -> error "rminIndex: impossible empty shape"
  trmaxIndex @_ @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) (STKR (shsRank rest) STKScalar)
          . fromPrimal . AstMaxIndexS . primalPart . astSFromR @sh sh $ a
        ZSS -> error "rmaxIndex: impossible empty shape"
  triota @r n =
    withSNat n $ \(SNat @n) ->
      astFromS (knownSTK @(TKR 1 r)) $ fromPrimal $ AstIotaS @n @r SNat
  trappend u v = case ftkAst u of
    FTKR shu' x -> case ftkAst v of
      FTKR shv' _ ->
        withCastRS shu' $ \shu -> case shu of
          _ :$$ restu ->
            withCastRS shv' $ \shv -> case shv of
              _ :$$ restv ->
                case testEquality restu restv of
                  Just Refl ->
                    astFromS (STKR (shrRank shu') (ftkToSTK x))
                    $ astAppendS (astSFromR shu u) (astSFromR shv v)
                  _ -> error $ "rappend: shapes don't match: "
                               ++ show (restu, restv)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  trslice i n a = case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh -> case sh of
        msnat@(SNat @m) :$$ _ ->
          withSNat i $ \isnat@(SNat @i) -> withSNat n $ \nsnat@(SNat @n) ->
            case cmpNat (snatPlus isnat nsnat) msnat of
              GTI -> error $ "rslice: argument tensor too narrow: "
                             ++ show (i, n, sNatValue msnat)
              EQI ->
                astFromS (STKR (shrRank sh') (ftkToSTK x))
                . astSliceS isnat nsnat (SNat @(m - (i + n)))
                . astSFromR sh $ a
              LTI ->
                astFromS (STKR (shrRank sh') (ftkToSTK x))
                . astSliceS isnat nsnat (SNat @(m - (i + n)))
                . astSFromR sh $ a
        ZSS -> error "xslice: impossible shape"
  trreverse a = case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh -> case sh of
        _ :$$ _ ->
          astFromS (STKR (shrRank sh') (ftkToSTK x))
          . astReverseS . astSFromR sh $ a
        ZSS -> error "xreverse: impossible shape"
  trtranspose @n @r permr a = case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \(sh :: ShS sh)  ->
        Permutation.permFromList permr $ \(perm :: Permutation.Perm perm) ->
          let result :: AstTensor AstMethodLet s (TKR2 n r)
              result =
                -- A noble lie, verified down below.
                gcastWith (unsafeCoerceRefl
                           :: (Rank perm <=? Rank sh) :~: True) $
                fromMaybe (error "rtranspose: impossible non-permutation")
                $ Permutation.permCheckPermutation perm
                $ astFromS (STKR (shsRank sh) (ftkToSTK x))
                  . astTransposeS perm . astSFromR sh $ a
          in case (Permutation.permRank perm, shsRank sh) of
            (psnat@SNat, shsnat@SNat) ->
              case cmpNat psnat shsnat of
                GTI -> error $ "rtranspose: rank mismatch: "
                               ++ show (sNatValue psnat, sNatValue shsnat)
                EQI -> result
                LTI -> result
  trreshape sh2' a = case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh ->
      withCastRS sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl -> astFromS (STKR (shrRank sh2') (ftkToSTK x))
                       . astReshapeS sh2 . astSFromR sh $ a
          _ -> error $ "rreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  trbuild1 @n @x k f = withSNat k $ \snat ->
    astBuild1Vectorize snat (STKR (SNat @n) (knownSTK @x)) f

  -- Shaped ops
  sshape t = case ftkAst t of
    FTKS sh _ -> sh
  tssum = astSum SNat knownSTK
  tsindex = astIndexS knownShS
  tsscatter @shm @shn @shp t f =
    astScatterS @shm @shn @shp knownShS t
    $ funToAstIxS knownShS f  -- this introduces new variable names
  tsgather @shm @shn @shp t f =
    astGatherS @shm @shn @shp knownShS t
    $ funToAstIxS knownShS f  -- this introduces new variable names
  tsconcrete = fromPrimal . AstConcreteS
  tsfloor = fromPrimal . astFloorS . primalPart
  tsfromIntegral = fromPrimal . astFromIntegralS . primalPart
  tscast = astCastS
  tsminIndex = fromPrimal . AstMinIndexS . primalPart
  tsmaxIndex = fromPrimal . AstMaxIndexS . primalPart
  tsiota = fromPrimal $ AstIotaS SNat
  tsappend = astAppendS
  tsslice = astSliceS
  tsreverse = astReverseS
  tsbuild1 @k @sh @x =
    astBuild1Vectorize (SNat @k) (STKS (knownShS @sh) (knownSTK @x))

  -- Mixed ops
  xshape t = case ftkAst t of
    FTKX sh _ -> sh
  txsum = astSum SNat knownSTK
  txreplicate snat sh = astReplicate snat (STKX sh knownSTK)
  txindex @sh1 @sh2 a ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 _ | SNat <- ssxRank (knownShX @sh1) ->
      withCastXS sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        withKnownShS (takeShS @(Rank sh1) sh) $
        astFromS @(TKS2 (Drop (Rank sh1) sh) x) (knownSTK @(TKX2 sh2 x))
        $ astIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (dropShS @(Rank sh1) sh) (astSFromX @sh @sh1sh2 sh a)
                    (ixxToIxs ix)
  txscatter @shm @_ @shp shpshn0 t f = case ftkAst t of
    FTKX shmshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        case testEquality (dropShS @(Rank shp) shpshn)
                          (dropShS @(Rank shm) shmshn) of
          Just Refl ->
            astFromS (ftkToSTK $ FTKX shpshn0 x)
            $ astScatterS @(Take (Rank shm) shmshn)
                          @(Drop (Rank shm) shmshn)
                          @(Take (Rank shp) shpshn)
                          knownShS (astSFromX shmshn t)
            $ funToAstIxS knownShS (ixxToIxs . f . ixsToIxx)
                -- this introduces new variable names
          _ -> error $ "xscatter: shapes don't match: "
                       ++ show ( dropShS @(Rank shp) shpshn
                               , dropShS @(Rank shm) shmshn )
  txgather @shm @_ @shp shmshn0 t f = case ftkAst t of
    FTKX shpshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        case testEquality (dropShS @(Rank shp) shpshn)
                          (dropShS @(Rank shm) shmshn) of
          Just Refl ->
            astFromS (ftkToSTK $ FTKX shmshn0 x)
            $ astGatherS @(Take (Rank shm) shmshn)
                         @(Drop (Rank shm) shmshn)
                         @(Take (Rank shp) shpshn)
                         knownShS (astSFromX shpshn t)
            $ funToAstIxS knownShS (ixxToIxs . f . ixsToIxx)
                -- this introduces new variable names
          _ -> error $ "xgather: shapes don't match: "
                       ++ show ( dropShS @(Rank shp) shpshn
                               , dropShS @(Rank shm) shmshn )
  txconcrete a = tconcrete (FTKX (Nested.mshape a) FTKScalar) (Concrete a)
  txfloor @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKX (ssxFromShX sh') knownSTK)
        . fromPrimal . astFloorS . primalPart . astSFromX @sh @sh' sh $ a
  txfromIntegral @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKX (ssxFromShX sh') knownSTK)
        . fromPrimal . astFromIntegralS
        . primalPart . astSFromX @sh @sh' sh $ a
  txcast @_ @r2 a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKX (ssxFromShX sh') STKScalar)
        . astCastS . astSFromX sh $ a
  txminIndex @_ @_ @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2)
                   (STKX (ssxFromShX $ shxInit sh') STKScalar)
          . fromPrimal . AstMinIndexS @n @rest
          . primalPart . astSFromX @sh @sh' sh $ a
  txmaxIndex @_ @_ @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2)
                   (STKX (ssxFromShX $ shxInit sh') STKScalar)
          . fromPrimal . AstMaxIndexS @n @rest
          . primalPart . astSFromX @sh @sh' sh $ a
  txiota @n @r = astFromS (knownSTK @(TKX '[Just n] r))
                 $ fromPrimal $ AstIotaS @n @r SNat
  txappend u v = case ftkAst u of
    FTKX (Nested.SKnown m@SNat :$% shu') x -> case ftkAst v of
      FTKX (Nested.SKnown n@SNat :$% shv') _ ->
        withCastXS shu' $ \(shu :: ShS shu) ->
          withCastXS shv' $ \(shv :: ShS shv) ->
            case shxEqual shu' shv' of
              Just Refl ->
                gcastWith (unsafeCoerceRefl :: shu :~: shv) $
                astFromS (STKX (Nested.SKnown (snatPlus m n)
                                :!% ssxFromShX shu')
                               (ftkToSTK x))
                $ astAppendS (astSFromX (m :$$ shu) u)
                             (astSFromX (n :$$ shv) v)
              _ -> error $ "xappend: shapes don't match: "
                           ++ show (shu', shv')
  txslice i n@SNat k a = case ftkAst a of
    FTKX sh'@(_ :$% sh2') x ->
      withCastXS sh' $ \sh@(msnat :$$ _) ->
        case testEquality (snatPlus i (snatPlus n k)) msnat of
          Just Refl ->
            astFromS (STKX (Nested.SKnown n :!% ssxFromShX sh2')
                           (ftkToSTK x))
            . astSliceS i n k . astSFromX sh $ a
          _ -> error $ "xslice: argument tensor too narrow: "
                       ++ show ( sNatValue i, sNatValue n, sNatValue k
                               , sNatValue msnat )
  txreverse a = case ftkAst a of
    FTKX sh' x ->
      withCastXS sh' $ \(sh@(_ :$$ _) :: ShS sh) ->
        astFromS (ftkToSTK $ FTKX sh' x)
        . astReverseS . astSFromX @sh sh $ a
  txtranspose perm a = case ftkAst a of
    FTKX sh' x ->
      let sh2' = shxPermutePrefix perm sh'
      in withCastXS sh' $ \sh ->
           astFromS (ftkToSTK $ FTKX sh2' x)
           . astTransposeS perm . astSFromX sh $ a
  txreshape sh2' a = case ftkAst a of
    FTKX sh' x ->
      withCastXS sh' $ \sh ->
      withCastXS sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl ->
            astFromS (ftkToSTK $ FTKX sh2' x)
            . astReshapeS sh2 . astSFromX sh $ a
          _ -> error $ "xreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  txbuild1 @k @sh @x =
    astBuild1Vectorize (SNat @k) (STKX (knownShX @sh) (knownSTK @x))

  -- Scalar ops
  tkconcrete = fromPrimal . AstConcreteK
  tkfloor = fromPrimal . astFloorK . primalPart
  tkfromIntegral = fromPrimal . astFromIntegralK . primalPart
  tkcast = astCastK

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk = ftkAst
  tconcrete ftk a = fromPrimal $ astConcrete ftk a
  tpair = astPair
  tproject1 = astProject1
  tproject2 = astProject2
  tsreplicate snat sh = astReplicate snat (STKS sh knownSTK)
  tstranspose = astTransposeS
  tsreshape = astReshapeS
  tmapAccumRDer _ !k _ !bftk !eftk f df rf acc0 es =
    astMapAccumRDer k bftk eftk f df rf acc0 es
  tmapAccumLDer _ !k _ !bftk !eftk f df rf acc0 es =
    astMapAccumLDer k bftk eftk f df rf acc0 es
  tApply = astApply
  tlambda ftk f =
    let (var, ast) = funToAst ftk Nothing $ unHFun f
    in AstLambda var ast
  tcond _ !b !u !v = astCond b u v
  tprimalPart = primalPart
  tdualPart _ = dualPart
  tfromPrimal _ = fromPrimal
  tfromDual = fromDual
  tgrad xftk f =
    -- We don't have an AST constructor to hold it, so we compute outright.
    --
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let -- No bangs here, because this goes under lambda and should not be
        -- evaluated too early (which at some point was even incorrect
        -- and triggered error "tunshare: used not at PrimalSpan"; maybe this
        -- is related to terms getting spans converted when interpreted)
        AstArtifactRev{..} =
          revProduceArtifact
            IgnoreIncomingCotangent (simplifyInline . unHFun f) emptyEnv xftk
        -- A new variable is created to give it the right span as opposed
        -- to the fixed PrimalSpan that artVarDomainRev has.
        (varP, ast) = funToAst xftk Nothing $ \ !astP ->
          let env = extendEnv artVarDomainRev astP emptyEnv
          in interpretAst env $ simplifyInline artDerivativeRev
    in AstLambda varP ast
  tvjp ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let AstArtifactRev{..} =
          revProduceArtifact
            UseIncomingCotangent (simplifyInline . unHFun f) emptyEnv ftkx
        ftkz = varNameToFTK artVarDtRev
        ftk2 = FTKProduct ftkz ftkx
        (varP, ast) = funToAst ftk2 Nothing $ \ !astP ->
          let env = extendEnv artVarDtRev (astProject1 astP)
                    $ extendEnv artVarDomainRev (astProject2 astP) emptyEnv
          in interpretAst env $ simplifyInline artDerivativeRev
    in AstLambda varP ast
  tjvp ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let AstArtifactFwd{..} =
          fwdProduceArtifact (simplifyInline . unHFun f) emptyEnv ftkx
        ftk2 = FTKProduct (adFTK ftkx) ftkx
        (varP, ast) = funToAst ftk2 Nothing $ \ !astP ->
          let env = extendEnv artVarDsFwd (astProject1 astP)
                    $ extendEnv artVarDomainFwd (astProject2 astP) emptyEnv
          in interpretAst env $ simplifyInline artDerivativeFwd
    in AstLambda varP ast

  tfromVector = astFromVector
  tsum snat@SNat stk u = case stk of
    STKScalar -> kfromS $ tssum u
    STKR SNat x | Dict <- lemKnownSTK x -> trsum u
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tssum u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txsum u
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (tsum snat stk1 (tproject1 u3))
              (tsum snat stk2 (tproject2 u3))
  treplicate snat@SNat stk u = case stk of
    STKScalar -> tsreplicate snat ZSS $ sfromK u
    STKR SNat x | Dict <- lemKnownSTK x -> trreplicate (sNatValue snat) u
    STKS sh x | Dict <- lemKnownSTK x -> tsreplicate snat sh u
    STKX sh x | Dict <- lemKnownSTK x -> txreplicate snat sh u
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (treplicate snat stk1 (tproject1 u3))
              (treplicate snat stk2 (tproject2 u3))
  tindexBuild snat@SNat stk u i = case stk of
    STKScalar -> kfromS $ tsindex u (i :.$ ZIS)
    STKR SNat x | Dict <- lemKnownSTK x -> trindex u (i :.: ZIR)
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tsindex u (i :.$ ZIS)
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txindex u (i :.% ZIX)
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (tindexBuild snat stk1 (tproject1 u3) i)
              (tindexBuild snat stk2 (tproject2 u3) i)

  treplTarget = replTarget
  tdefTarget = defTarget
  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target


-- * AstRaw instances

instance AstSpan s => ShareTensor (AstRaw s) where
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tshare t =
    let u = unAstRaw t
    in if astIsSmall True u
       then t
       else AstRaw $ fun1ToAst (ftkAst u) $ \ !var -> AstShare var u
  tunpair (AstRaw (AstPair t1 t2)) = (AstRaw t1, AstRaw t2)
  tunpair t = let tShared = tshare t
              in (tproject1 tShared, tproject2 tShared)

instance AstSpan s => BaseTensor (AstRaw s) where
  -- Ranked ops
  rshape t = case ftkAst $ unAstRaw t of
    FTKR sh _ -> sh
  trsum v = withSNat (rwidth v) $ \snat ->
             AstRaw . AstSum snat knownSTK . unAstRaw $ v
  trreplicate k = withSNat k $ \snat ->
    AstRaw . AstReplicate snat knownSTK . unAstRaw
  trindex @m @n (AstRaw a) ix = AstRaw $ case ftkAst a of
    FTKR @_ @x shmshn _ ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        AstFromS @(TKS2 (Drop m sh) x) (knownSTK @(TKR2 n x))
        $ AstIndexS @(Take m sh) @(Drop m sh)
                    (dropShS @m sh) (AstSFromR @sh sh a)
                    (ixrToIxs (unAstRaw <$> ix))
  trscatter @m @_ @p shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR @_ @x shmshn0 x ->
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
            AstFromS @(TKS2 shpshn x) (STKR (shrRank shpshn0) (ftkToSTK x))
            $ AstScatterS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                          knownShS (AstSFromR shmshn t)
            $ funToAstIxS knownShS (fmap unAstRaw . ixrToIxs . f . ixsToIxr
                           . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "rscatter: shapes don't match: "
                       ++ show (dropShS @p shpshn, dropShS @m shmshn)
  trgather @m @_ @p shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR shpshn0 x ->
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
            AstFromS (STKR (shrRank shmshn0) (ftkToSTK x))
            $ AstGatherS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                         knownShS (AstSFromR shpshn t)
            $ funToAstIxS knownShS (fmap unAstRaw . ixrToIxs . f . ixsToIxr
                           . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "rgather: shapes don't match: "
                       ++ show (dropShS @p shpshn, dropShS @m shmshn)
  trconcrete a = tconcrete (FTKR (Nested.rshape a) FTKScalar) (Concrete a)
  trfloor @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKR (shrRank sh') knownSTK)
        . fromPrimal . AstFloorS . primalPart . AstSFromR @sh sh $ a
  trfromIntegral @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKR (shrRank sh') knownSTK)
        . fromPrimal . AstFromIntegralS . primalPart . AstSFromR @sh sh $ a
  trcast @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKR (shsRank sh) STKScalar)
        . AstCastS . AstSFromR sh $ a
  trminIndex @_ @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (STKR (shsRank rest) STKScalar)
          . fromPrimal . AstMinIndexS . primalPart . AstSFromR @sh sh $ a
        ZSS -> error "rminIndex: impossible shape"
  trmaxIndex @_ @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (STKR (shsRank rest) STKScalar)
          . fromPrimal . AstMaxIndexS . primalPart . AstSFromR @sh sh $ a
        ZSS -> error "rmaxIndex: impossible shape"
  triota @r n =
    AstRaw
    $ withSNat n $ \(SNat @n) ->
        AstFromS (knownSTK @(TKR 1 r)) $ fromPrimal $ AstIotaS @n @r SNat
  trappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKR shu' x -> case ftkAst v of
      FTKR shv' _ ->
        withCastRS shu' $ \shu -> case shu of
          _ :$$ restu ->
            withCastRS shv' $ \shv -> case shv of
              _ :$$ restv ->
                case testEquality restu restv of
                  Just Refl ->
                    AstFromS (STKR (shrRank shu') (ftkToSTK x))
                    $ AstAppendS (AstSFromR shu u) (AstSFromR shv v)
                  _ -> error $ "rappend: shapes don't match: "
                               ++ show (restu, restv)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  trslice i n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh -> case sh of
        msnat@(SNat @m) :$$ _ ->
          withSNat i $ \isnat@(SNat @i) -> withSNat n $ \nsnat@(SNat @n) ->
            case cmpNat (snatPlus isnat nsnat) msnat of
              GTI -> error $ "rslice: argument tensor too narrow: "
                             ++ show (i, n, sNatValue msnat)
              EQI ->
                AstFromS (STKR (shrRank sh') (ftkToSTK x))
                . AstSliceS isnat nsnat (SNat @(m - (i + n)))
                . AstSFromR sh $ a
              LTI ->
                AstFromS (STKR (shrRank sh') (ftkToSTK x))
                . AstSliceS isnat nsnat (SNat @(m - (i + n)))
                . AstSFromR sh $ a
        ZSS -> error "xslice: impossible shape"
  trreverse (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh -> case sh of
        _ :$$ _ ->
          AstFromS (STKR (shrRank sh') (ftkToSTK x))
          . AstReverseS . AstSFromR sh $ a
        ZSS -> error "xreverse: impossible shape"
  trtranspose @n @r permr (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        Permutation.permFromList permr $ \(perm :: Permutation.Perm perm) ->
          let result :: AstTensor AstMethodShare s (TKR2 n r)
              result =
                -- A noble lie, verified down below.
                gcastWith (unsafeCoerceRefl
                           :: (Rank perm <=? Rank sh) :~: True) $
                fromMaybe (error "rtranspose: impossible non-permutation")
                $ Permutation.permCheckPermutation perm
                $ AstFromS (STKR (shsRank sh) (ftkToSTK x))
                  . AstTransposeS perm . AstSFromR sh $ a
          in case (Permutation.permRank perm, shsRank sh) of
            (psnat@SNat, shsnat@SNat) ->
              case cmpNat psnat shsnat of
                GTI -> error $ "rtranspose: rank mismatch: "
                               ++ show (sNatValue psnat, sNatValue shsnat)
                EQI -> result
                LTI -> result
  trreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh ->
      withCastRS sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl -> AstFromS (STKR (shrRank sh2') (ftkToSTK x))
                       . AstReshapeS sh2 . AstSFromR sh $ a
          _ -> error $ "rreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  trbuild1 k f = withSNat k $ \snat ->
    AstRaw $ AstBuild1 snat knownSTK
    $ funToAstI (Just (0, fromIntegral k - 1))
        -- this introduces new variable names
    $ unAstRaw . f . AstRaw

  -- Shaped ops
  sshape t = case ftkAst $ unAstRaw t of
    FTKS sh _ -> sh
  tssum = AstRaw . AstSum SNat knownSTK . unAstRaw
  tsindex v ix = AstRaw $ AstIndexS knownShS (unAstRaw v) (unAstRaw <$> ix)
  tsscatter @shm @shn @shp t f =
    AstRaw $ AstScatterS @shm @shn @shp knownShS (unAstRaw t)
           $ funToAstIxS knownShS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  tsgather @shm @shn @shp t f =
    AstRaw $ AstGatherS @shm @shn @shp knownShS (unAstRaw t)
           $ funToAstIxS knownShS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  tsconcrete = AstRaw . fromPrimal . AstConcreteS
  tsfloor = AstRaw . fromPrimal . AstFloorS . primalPart . unAstRaw
  tsfromIntegral =
    AstRaw . fromPrimal . AstFromIntegralS . primalPart . unAstRaw
  tscast = AstRaw . AstCastS . unAstRaw
  tsminIndex = AstRaw . fromPrimal . AstMinIndexS . primalPart . unAstRaw
  tsmaxIndex = AstRaw . fromPrimal . AstMaxIndexS . primalPart . unAstRaw
  tsiota = AstRaw . fromPrimal $ AstIotaS SNat
  tsappend u v = AstRaw $ AstAppendS (unAstRaw u) (unAstRaw v)
  tsslice i n k = AstRaw . AstSliceS i n k . unAstRaw
  tsreverse = AstRaw . AstReverseS . unAstRaw
  tsbuild1 @k f = AstRaw $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstI (Just (0, valueOf @k - 1))
                      -- this introduces new variable names
                  $ unAstRaw . f . AstRaw

  -- Mixed ops
  xshape t = case ftkAst $ unAstRaw t of
    FTKX sh _ -> sh
  txsum = AstRaw . AstSum SNat knownSTK . unAstRaw
  txreplicate snat sh = AstRaw . AstReplicate snat (STKX sh knownSTK) . unAstRaw
  txindex @sh1 @sh2 (AstRaw a) ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 _ | SNat <- ssxRank (knownShX @sh1) ->
      withCastXS sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        withKnownShS (takeShS @(Rank sh1) sh) $
        AstRaw $ AstFromS @(TKS2 (Drop (Rank sh1) sh) x)
                          (knownSTK @(TKX2 sh2 x))
        $ AstIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (dropShS @(Rank sh1) sh) (AstSFromX @sh @sh1sh2 sh a)
                    (ixxToIxs (unAstRaw <$> ix))
  txscatter @shm @_ @shp shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shmshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        case testEquality (dropShS @(Rank shp) shpshn)
                          (dropShS @(Rank shm) shmshn) of
          Just Refl ->
            AstFromS (ftkToSTK $ FTKX shpshn0 x)
            $ AstScatterS @(Take (Rank shm) shmshn)
                          @(Drop (Rank shm) shmshn)
                          @(Take (Rank shp) shpshn)
                          knownShS (AstSFromX shmshn t)
            $ funToAstIxS knownShS (fmap unAstRaw . ixxToIxs . f . ixsToIxx
                           . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "xscatter: shapes don't match: "
                       ++ show ( dropShS @(Rank shp) shpshn
                               , dropShS @(Rank shm) shmshn )
  txgather @shm @_ @shp shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shpshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withCastXS shmshn0 $ \(shmshn :: ShS shmshn) ->
      withCastXS shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (takeShS @(Rank shm) shmshn) $
        withKnownShS (dropShS @(Rank shm) shmshn) $
        withKnownShS (takeShS @(Rank shp) shpshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        case testEquality (dropShS @(Rank shp) shpshn)
                          (dropShS @(Rank shm) shmshn) of
          Just Refl ->
            AstFromS (ftkToSTK $ FTKX shmshn0 x)
            $ AstGatherS @(Take (Rank shm) shmshn)
                         @(Drop (Rank shm) shmshn)
                         @(Take (Rank shp) shpshn) knownShS (AstSFromX shpshn t)
            $ funToAstIxS knownShS (fmap unAstRaw . ixxToIxs . f . ixsToIxx
                           . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "xgather: shapes don't match: "
                       ++ show ( dropShS @(Rank shp) shpshn
                               , dropShS @(Rank shm) shmshn )
  txconcrete a = tconcrete (FTKX (Nested.mshape a) FTKScalar) (Concrete a)
  txfloor @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKX (ssxFromShX sh') knownSTK)
        . fromPrimal . AstFloorS . primalPart . AstSFromX @sh @sh' sh $ a
  txfromIntegral @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKX (ssxFromShX sh') knownSTK)
        . fromPrimal . AstFromIntegralS
        . primalPart . AstSFromX @sh @sh' sh $ a
  txcast @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKX (ssxFromShX sh') STKScalar)
        . AstCastS . AstSFromX sh $ a
  txminIndex @_ @_ @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2)
                   (STKX (ssxFromShX $ shxInit sh') STKScalar)
          . fromPrimal . AstMinIndexS @n @rest
          . primalPart . AstSFromX @sh @sh' sh $ a
  txmaxIndex @_ @_ @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2)
                   (STKX (ssxFromShX $ shxInit sh') STKScalar)
          . fromPrimal . AstMaxIndexS @n @rest
          . primalPart . AstSFromX @sh @sh' sh $ a
  txiota @n @r = AstRaw $ AstFromS (knownSTK @(TKX '[Just n] r))
                 $ fromPrimal $ AstIotaS @n @r SNat
  txappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKX (Nested.SKnown m@SNat :$% shu') x -> case ftkAst v of
      FTKX (Nested.SKnown n@SNat :$% shv') _ ->
        withCastXS shu' $ \(shu :: ShS shu) ->
          withCastXS shv' $ \(shv :: ShS shv) ->
            case shxEqual shu' shv' of
              Just Refl ->
                gcastWith (unsafeCoerceRefl :: shu :~: shv) $
                AstFromS (STKX (Nested.SKnown (snatPlus m n)
                                :!% ssxFromShX shu')
                               (ftkToSTK x))
                $ AstAppendS (AstSFromX (m :$$ shu) u)
                             (AstSFromX (n :$$ shv) v)
              _ -> error $ "xappend: shapes don't match: "
                           ++ show (shu', shv')
  txslice i n@SNat k (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh'@(_ :$% sh2') x ->
      withCastXS sh' $ \sh@(msnat :$$ _) ->
        case testEquality (snatPlus i (snatPlus n k)) msnat of
          Just Refl ->
            AstFromS (STKX (Nested.SKnown n :!% ssxFromShX sh2')
                           (ftkToSTK x))
            . AstSliceS i n k . AstSFromX sh $ a
          _ -> error $ "xslice: argument tensor too narrow: "
                       ++ show ( sNatValue i, sNatValue n, sNatValue k
                               , sNatValue msnat )
  txreverse (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      withCastXS sh' $ \(sh@(_ :$$ _) :: ShS sh) ->
        AstFromS (ftkToSTK $ FTKX sh' x)
        . AstReverseS . AstSFromX @sh sh $ a
  txtranspose perm (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      let sh2' = shxPermutePrefix perm sh'
      in withCastXS sh' $ \sh ->
           AstFromS (ftkToSTK $ FTKX sh2' x)
           . AstTransposeS perm
           . AstSFromX sh $ a
  txreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      withCastXS sh' $ \sh ->
      withCastXS sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl ->
            AstFromS (ftkToSTK $ FTKX sh2' x)
            . AstReshapeS sh2 . AstSFromX sh $ a
          _ -> error $ "xreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  txbuild1 @k f = AstRaw $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstI (Just (0, valueOf @k - 1))
                      -- this introduces new variable names
                  $ unAstRaw . f . AstRaw

  -- Scalar ops
  tkconcrete = AstRaw . fromPrimal . AstConcreteK
  tkfloor = AstRaw . fromPrimal . AstFloorK . primalPart . unAstRaw
  tkfromIntegral = AstRaw . fromPrimal . AstFromIntegralK
                   . primalPart . unAstRaw
  tkcast = AstRaw . AstCastK . unAstRaw

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk = ftkAst . unAstRaw
  tconcrete ftk a = AstRaw $ fromPrimal $ unAstRaw $ astConcreteRaw ftk a
  tpair t1 t2 = AstRaw $ AstPair (unAstRaw t1) (unAstRaw t2)
  tproject1 t = AstRaw $ AstProject1 $ unAstRaw t
  tproject2 t = AstRaw $ AstProject2 $ unAstRaw t
  tsreplicate snat sh = AstRaw . AstReplicate snat (STKS sh knownSTK) . unAstRaw
  tstranspose perm = AstRaw . AstTransposeS perm . unAstRaw
  tsreshape sh = AstRaw . AstReshapeS sh . unAstRaw
  tmapAccumRDer _ !k _ !bftk !eftk f df rf acc0 es =
      AstRaw $ AstMapAccumRDer k bftk eftk f df rf (unAstRaw acc0) (unAstRaw es)
  tmapAccumLDer _ !k _ !bftk !eftk f df rf acc0 es =
      AstRaw $ AstMapAccumLDer k bftk eftk f df rf (unAstRaw acc0) (unAstRaw es)
  tApply t ll = AstRaw $ AstApply t (unAstRaw ll)
  tlambda = tlambda @(AstTensor AstMethodLet s)
  tcond _ !b !u !v = AstRaw $ AstCond b (unAstRaw u) (unAstRaw v)
  tprimalPart t = AstRaw $ primalPart $ unAstRaw t
  tdualPart _ t = dualPart $ unAstRaw t
  tfromPrimal _ t = AstRaw $ fromPrimal $ unAstRaw t
  tfromDual t = AstRaw $ fromDual t
  -- These three methods are called at this type in delta evaluation via
  -- tmapAccumR and tmapAccumL, so they have to work. We could refrain from
  -- simplifying the resulting terms, but it's not clear that's more consistent.
  tgrad = tgrad @(AstTensor AstMethodLet s)
  tvjp = tvjp @(AstTensor AstMethodLet s)
  tjvp = tjvp @(AstTensor AstMethodLet s)

  tfromVector k stk =
    AstRaw . AstFromVector k stk . V.map unAstRaw

  treplTarget = replTarget
  tdefTarget = defTarget
  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target

instance AstSpan s => ConvertTensor (AstRaw s) where
  tconvert c _astk bftk =
    AstRaw . AstConvert c bftk . unAstRaw

  tfromS zstk (AstRaw a) = AstRaw $ AstFromS zstk a
  rfromX a = case ftkAst $ unAstRaw a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        rfromS $ sfromX @_ @sh a
  xfromR a = case ftkAst $ unAstRaw a of
    FTKR shr _ ->
      withCastRS shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        xfromS @_ @sh $ sfromR a

  kfromS = AstRaw . AstFromS knownSTK . unAstRaw
  rfromS @sh @x | SNat <- shsRank (knownShS @sh) =
    AstRaw . AstFromS (knownSTK @(TKR2 (Rank sh) x)) . unAstRaw
  sfromK = AstRaw . cAstSFromK . unAstRaw
  sfromR = AstRaw . cAstSFromR knownShS . unAstRaw
  sfromX = AstRaw . cAstSFromX knownShS . unAstRaw
  xfromS @_ @sh' @x = AstRaw . AstFromS (knownSTK @(TKX2 sh' x)) . unAstRaw

  rzip @_ @_ @n (AstRaw a)
   | Refl <- lemRankReplicate (Proxy @n) = AstRaw $ case ftkAst a of
    FTKProduct (FTKR sh y) (FTKR _sh z) ->
      let c = ConvCmp
                (ConvXR (ftkToSTK (FTKProduct y z)))
                (ConvCmp
                   (ConvZip (ftkToSTK y) (ftkToSTK z))
                   (ConvT2 ConvRX ConvRX))
          ftk2 = FTKR sh (FTKProduct y z)
      in AstConvert c ftk2 a
  runzip @_ @_ @n (AstRaw a)
   | Refl <- lemRankReplicate (Proxy @n) = AstRaw $ case ftkAst a of
    FTKR sh (FTKProduct y z) ->
      let c = ConvCmp
                (ConvT2 (ConvXR (ftkToSTK y)) (ConvXR (ftkToSTK z)))
                (ConvCmp
                   (ConvUnzip (ftkToSTK y) (ftkToSTK z))
                   ConvRX)
          ftk2 = FTKProduct (FTKR sh y) (FTKR sh z)
      in AstConvert c ftk2 a
  szip (AstRaw a) = AstRaw $ case ftkAst a of
    FTKProduct (FTKS sh y) (FTKS _sh z) ->
      let c = ConvCmp
                ConvXS
                (ConvCmp
                   (ConvZip (ftkToSTK y) (ftkToSTK z))
                   (ConvT2 ConvSX ConvSX))
          ftk2 = FTKS sh (FTKProduct y z)
      in AstConvert c ftk2 a
  sunzip (AstRaw a) = AstRaw $ case ftkAst a of
    FTKS sh (FTKProduct y z) ->
      let c = ConvCmp
                (ConvT2 ConvXS ConvXS)
                (ConvCmp
                   (ConvUnzip (ftkToSTK y) (ftkToSTK z))
                   ConvSX)
          ftk2 = FTKProduct (FTKS sh y) (FTKS sh z)
      in AstConvert c ftk2 a
  xzip (AstRaw a) = AstRaw $ case ftkAst a of
    FTKProduct (FTKX sh y) (FTKX _sh z) ->
      let c = ConvZip (ftkToSTK y) (ftkToSTK z)
          ftk2 = FTKX sh (FTKProduct y z)
      in AstConvert c ftk2 a
  xunzip (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh (FTKProduct y z) ->
      let c = ConvUnzip (ftkToSTK y) (ftkToSTK z)
          ftk2 = FTKProduct (FTKX sh y) (FTKX sh z)
      in AstConvert c ftk2 a

  xnestR @sh1 @m @x sh1 (AstRaw a)
   | Refl <- lemRankReplicate (Proxy @m) = AstRaw $ case ftkAst a of
    FTKX sh1sh2 x ->
      let c :: TKConversion (TKX2 (sh1 ++ Replicate m Nothing) x)
                          (TKX2 sh1 (TKR2 m x))
          c = ConvCmp
                (ConvXX (ConvXR (knownSTK @x)))
                (ConvNest @_ @_ @(Replicate m Nothing)
                          (STKX sh1 (knownSTK @x)))
          ftk2 = FTKX (shxTakeSSX (Proxy @(Replicate m Nothing)) sh1sh2 sh1)
                      (FTKR (shrFromShX (shxDropSSX sh1sh2 sh1)) x)
      in AstConvert c ftk2 a
  xnestS @_ @sh2 @x sh1 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1sh2 x ->
      let c = ConvCmp
                (ConvXX ConvXS)
                (ConvNest (STKX sh1 (knownSTK @x)))
          ftk2 = FTKX (shxTakeSSX (Proxy @(MapJust sh2)) sh1sh2 sh1)
                      (FTKS (knownShS @sh2) x)
      in AstConvert c ftk2 a
  xnest @_ @sh2 @x sh1 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1sh2 x ->
      let c = ConvNest (STKX sh1 (knownSTK @x))
          ftk2 = FTKX (shxTakeSSX (Proxy @sh2) sh1sh2 sh1)
                      (FTKX (shxDropSSX sh1sh2 sh1) x)
      in AstConvert c ftk2 a
  xunNestR (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1 (FTKR sh2 x) ->
      let c = ConvCmp
                ConvUnnest
                (ConvXX ConvRX)
          ftk2 = FTKX (sh1 `shxAppend` shxFromShR sh2) x
      in AstConvert c ftk2 a
  xunNestS (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1 (FTKS sh2 x) ->
      let c = ConvCmp
                ConvUnnest
                (ConvXX ConvSX)
          ftk2 = FTKX (sh1 `shxAppend` shxFromShS sh2) x
      in AstConvert c ftk2 a
  xunNest (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1 (FTKX sh2 x) ->
      let c = ConvUnnest
          ftk2 = FTKX (sh1 `shxAppend` sh2) x
      in AstConvert c ftk2 a

  tpairConv = tpair
  tunpairConv = tunpair

-- All but the last case are shortcuts for common forms.
astConcreteRaw :: FullShapeTK y -> Concrete y
               -> AstRaw PrimalSpan y
astConcreteRaw ftk v = case ftk of
  FTKScalar -> AstRaw $ AstConcreteK $ unConcrete v
  FTKR sh' FTKScalar -> AstRaw $
    withCastRS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS (ftkToSTK ftk) $ AstConcreteS (unConcrete $ sfromR @_ @sh v)
  FTKS _ FTKScalar -> AstRaw $ AstConcreteS $ unConcrete v
  FTKX sh' FTKScalar -> AstRaw $
    withCastXS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS (ftkToSTK ftk) $ AstConcreteS (unConcrete $ sfromX @_ @sh v)
  FTKProduct ftk1 ftk2 -> AstRaw $
    AstPair (unAstRaw $ astConcreteRaw ftk1 (tproject1 v))
            (unAstRaw $ astConcreteRaw ftk2 (tproject2 v))
  _ -> concreteTarget (tkconcrete . unConcrete) (tsconcrete . unConcrete)
                      (\stk a -> AstRaw $ AstFromS stk $ unAstRaw a)
                      (ftkToSTK ftk) v


-- * AstNoVectorize instances

instance AstSpan s => LetTensor (AstNoVectorize s) where
  ttlet u f = AstNoVectorize
              $ ttlet (unAstNoVectorize u)
                      (unAstNoVectorize . f . AstNoVectorize)
  ttletPrimal u f = AstNoVectorize
                    $ ttletPrimal (unAstNoVectorize u)
                                  (unAstNoVectorize . f . AstNoVectorize)
  toShare t = toShare $ unAstNoVectorize t

instance AstSpan s => BaseTensor (AstNoVectorize s) where
  -- Ranked ops
  rshape = rshape . unAstNoVectorize
  trsum = AstNoVectorize . trsum . unAstNoVectorize
  trreplicate k = AstNoVectorize . trreplicate k . unAstNoVectorize
  trindex v ix =
    AstNoVectorize $ trindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  trscatter sh t f =
    AstNoVectorize $ trscatter sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  trgather sh t f =
    AstNoVectorize $ trgather sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  trconcrete = AstNoVectorize . trconcrete
  trfloor = AstNoVectorize . trfloor . unAstNoVectorize
  trfromIntegral = AstNoVectorize . trfromIntegral . unAstNoVectorize
  trcast = AstNoVectorize . trcast . unAstNoVectorize
  trminIndex = AstNoVectorize . trminIndex . unAstNoVectorize
  trmaxIndex = AstNoVectorize . trmaxIndex . unAstNoVectorize
  triota = AstNoVectorize . triota
  trappend u v =
    AstNoVectorize $ trappend (unAstNoVectorize u) (unAstNoVectorize v)
  trslice i n = AstNoVectorize . trslice i n . unAstNoVectorize
  trreverse = AstNoVectorize . trreverse . unAstNoVectorize
  trtranspose perm = AstNoVectorize . trtranspose perm . unAstNoVectorize
  trreshape sh = AstNoVectorize . trreshape sh . unAstNoVectorize
  trbuild1 k f = withSNat k $ \snat ->
    AstNoVectorize $ AstBuild1 snat knownSTK
    $ funToAstI (Just (0, fromIntegral k - 1))
        -- this introduces new variable names
    $ unAstNoVectorize . f . AstNoVectorize

  -- Shaped ops
  sshape = sshape . unAstNoVectorize
  tssum = AstNoVectorize . tssum . unAstNoVectorize
  tsindex v ix =
    AstNoVectorize $ tsindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  tsscatter @_ @shm @shn @shp t f =
    AstNoVectorize $ tsscatter @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  tsgather @_ @shm @shn @shp t f =
    AstNoVectorize $ tsgather @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  tsconcrete = AstNoVectorize . tsconcrete
  tsfloor = AstNoVectorize . tsfloor . unAstNoVectorize
  tsfromIntegral = AstNoVectorize . tsfromIntegral . unAstNoVectorize
  tscast = AstNoVectorize . tscast . unAstNoVectorize
  tsminIndex = AstNoVectorize . tsminIndex . unAstNoVectorize
  tsmaxIndex = AstNoVectorize . tsmaxIndex . unAstNoVectorize
  tsiota = AstNoVectorize tsiota
  tsappend u v =
    AstNoVectorize $ tsappend (unAstNoVectorize u) (unAstNoVectorize v)
  tsslice i n k = AstNoVectorize . tsslice i n k . unAstNoVectorize
  tsreverse = AstNoVectorize . tsreverse . unAstNoVectorize
  tsbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstI (Just (0, valueOf @k - 1))
                      -- this introduces new variable names
                  $ unAstNoVectorize . f . AstNoVectorize

  -- Mixed ops
  xshape = xshape . unAstNoVectorize
  txsum = AstNoVectorize . txsum . unAstNoVectorize
  txreplicate snat sh = AstNoVectorize . txreplicate snat sh . unAstNoVectorize
  txindex v ix =
    AstNoVectorize $ txindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  txscatter @_ @shm @shn @shp sh t f =
    AstNoVectorize $ txscatter @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  txgather @_ @shm @shn @shp sh t f =
    AstNoVectorize $ txgather @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  txconcrete = AstNoVectorize . txconcrete
  txfloor = AstNoVectorize . txfloor . unAstNoVectorize
  txfromIntegral = AstNoVectorize . txfromIntegral . unAstNoVectorize
  txcast = AstNoVectorize . txcast . unAstNoVectorize
  txminIndex = AstNoVectorize . txminIndex . unAstNoVectorize
  txmaxIndex = AstNoVectorize . txmaxIndex . unAstNoVectorize
  txiota @n = AstNoVectorize $ txiota @_ @n
  txappend u v =
    AstNoVectorize $ txappend (unAstNoVectorize u) (unAstNoVectorize v)
  txslice i n k = AstNoVectorize . txslice i n k . unAstNoVectorize
  txreverse = AstNoVectorize . txreverse . unAstNoVectorize
  txtranspose perm = AstNoVectorize . txtranspose perm . unAstNoVectorize
  txreshape sh = AstNoVectorize . txreshape sh . unAstNoVectorize
  txbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstI (Just (0, valueOf @k - 1))
                      -- this introduces new variable names
                  $ unAstNoVectorize . f . AstNoVectorize

  -- Scalar ops
  tkconcrete = AstNoVectorize . tkconcrete
  tkfloor = AstNoVectorize . tkfloor . unAstNoVectorize
  tkfromIntegral = AstNoVectorize . tkfromIntegral . unAstNoVectorize
  tkcast = AstNoVectorize . tkcast . unAstNoVectorize

  -- General operations that don't require LetTensor nor ShareTensor
  tftk stk = tftk stk . unAstNoVectorize
  tconcrete ftk a = AstNoVectorize $ tconcrete ftk a
  tpair t1 t2 =
    AstNoVectorize $ tpair (unAstNoVectorize t1) (unAstNoVectorize t2)
  tproject1 t = AstNoVectorize $ tproject1 $ unAstNoVectorize t
  tproject2 t = AstNoVectorize $ tproject2 $ unAstNoVectorize t
  tsreplicate snat sh = AstNoVectorize . tsreplicate snat sh. unAstNoVectorize
  tstranspose perm =
    AstNoVectorize . tstranspose perm . unAstNoVectorize
  tsreshape sh = AstNoVectorize . tsreshape sh . unAstNoVectorize
  tmapAccumRDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    AstNoVectorize $ tmapAccumRDer Proxy k accftk bftk eftk f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  tmapAccumLDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    AstNoVectorize $ tmapAccumLDer Proxy k accftk bftk eftk f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  tApply t ll = AstNoVectorize $ tApply t (unAstNoVectorize ll)
  tlambda = tlambda @(AstTensor AstMethodLet s)
  tcond !stk !b !u !v =
    AstNoVectorize $ tcond stk b (unAstNoVectorize u) (unAstNoVectorize v)
  tprimalPart t = AstNoVectorize $ tprimalPart $ unAstNoVectorize t
  tdualPart stk t = tdualPart stk $ unAstNoVectorize t
  tfromPrimal stk t = AstNoVectorize $ tfromPrimal stk $ unAstNoVectorize t
  tfromDual t = AstNoVectorize $ tfromDual t
  tgrad = tgrad @(AstTensor AstMethodLet s)
  tvjp = tvjp @(AstTensor AstMethodLet s)
  tjvp = tjvp @(AstTensor AstMethodLet s)

  tfromVector k stk =
    AstNoVectorize . tfromVector k stk . V.map unAstNoVectorize
  tsum k stk =
    AstNoVectorize . tsum k stk . unAstNoVectorize
  treplicate k stk =
    AstNoVectorize . treplicate k stk . unAstNoVectorize
  tindexBuild k stk u i =
    AstNoVectorize $ tindexBuild k stk (unAstNoVectorize u) (unAstNoVectorize i)

  treplTarget r ftk = AstNoVectorize $ treplTarget r ftk
  tdefTarget = AstNoVectorize . tdefTarget
  taddTarget stk a b = AstNoVectorize $ taddTarget stk (unAstNoVectorize a)
                                                       (unAstNoVectorize b)
  tmultTarget stk a b = AstNoVectorize $ tmultTarget stk (unAstNoVectorize a)
                                                         (unAstNoVectorize b)
  tsum0Target stk a = AstNoVectorize $ tsum0Target stk (unAstNoVectorize a)
  tdot0Target stk a b = AstNoVectorize $ tdot0Target stk (unAstNoVectorize a)
                                                         (unAstNoVectorize b)

instance AstSpan s => ConvertTensor (AstNoVectorize s) where
  tconvert c _astk bftk =
    AstNoVectorize . astConvert c bftk . unAstNoVectorize

  tfromS zstk = AstNoVectorize . tfromS zstk . unAstNoVectorize
  rfromX = AstNoVectorize . rfromX . unAstNoVectorize
  xfromR = AstNoVectorize . xfromR . unAstNoVectorize

  sfromK = AstNoVectorize . sfromK . unAstNoVectorize
  sfromR = AstNoVectorize . sfromR . unAstNoVectorize
  sfromX = AstNoVectorize . sfromX . unAstNoVectorize

  rzip = AstNoVectorize . rzip . unAstNoVectorize
  runzip = AstNoVectorize . runzip . unAstNoVectorize
  szip = AstNoVectorize . szip . unAstNoVectorize
  sunzip = AstNoVectorize . sunzip . unAstNoVectorize
  xzip = AstNoVectorize . xzip . unAstNoVectorize
  xunzip = AstNoVectorize . xunzip . unAstNoVectorize

  xnestR sh = AstNoVectorize . xnestR sh . unAstNoVectorize
  xnestS sh = AstNoVectorize . xnestS sh . unAstNoVectorize
  xnest sh = AstNoVectorize . xnest sh . unAstNoVectorize
  xunNestR = AstNoVectorize . xunNestR . unAstNoVectorize
  xunNestS = AstNoVectorize . xunNestS . unAstNoVectorize
  xunNest = AstNoVectorize . xunNest . unAstNoVectorize

  tpairConv = tpair
  tunpairConv a = let (b, c) = tunpairConv $ unAstNoVectorize a
                  in (AstNoVectorize b, AstNoVectorize c)


-- * AstNoSimplify instances

astLetFunNoSimplify
  :: forall y z s s2. AstSpan s
  => AstTensor AstMethodLet s y
  -> (AstTensor AstMethodLet s y -> AstTensor AstMethodLet s2 z)
  -> AstTensor AstMethodLet s2 z
astLetFunNoSimplify a f | astIsSmall True a = f a
                            -- too important an optimization to skip
astLetFunNoSimplify a f = case a of
  AstFromS @y2 stkz v ->
    let (var, ast) = funToAst2 (ftkAst v) Nothing (f . AstFromS @y2 stkz)
    in AstLet var v ast
  AstFromPrimal (AstFromS @y2 stkz vRaw) ->
    let v = AstFromPrimal vRaw
        (var, ast) = funToAst2 (ftkAst v) Nothing (f . AstFromS @y2 stkz)
    in AstLet var v ast
  _ -> case ftkAst a of
    ftk@(FTKR @_ @x2 sh' x) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst2 (FTKS sh x) Nothing
                        (f . AstFromS @(TKS2 sh x2) (ftkToSTK ftk))
        in AstLet var (AstSFromR @sh sh a) ast
             -- safe, because subsitution ruled out above
    ftk@(FTKX @_ @x sh' x) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst2 (FTKS sh x) Nothing
                        (f . AstFromS @(TKS2 sh x) (ftkToSTK ftk))
        in AstLet var (AstSFromX @sh sh a) ast
    -- processing product recursively may be not worth it
    ftk -> let (var, ast) = funToAst2 ftk Nothing f
           in AstLet var a ast

instance AstSpan s => LetTensor (AstNoSimplify s) where
  ttlet u f = AstNoSimplify
              $ astLetFunNoSimplify (unAstNoSimplify u)
                                    (unAstNoSimplify . f . AstNoSimplify)
  ttletPrimal u f = AstNoSimplify
                    $ astLetFunNoSimplify (unAstNoSimplify u)
                                          (unAstNoSimplify . f . AstNoSimplify)
  toShare t = AstRaw $ AstToShare $ unAstNoSimplify t

wAstNoSimplify :: AstRaw s y -> AstNoSimplify s y
wAstNoSimplify =
  AstNoSimplify
  . (unsafeCoerce :: AstTensor AstMethodShare s y
                  -> AstTensor AstMethodLet s y)
  . unAstRaw

wunAstNoSimplify :: AstNoSimplify s y -> AstRaw s y
wunAstNoSimplify =
  AstRaw
  . (unsafeCoerce :: AstTensor AstMethodLet s y
                  -> AstTensor AstMethodShare s y)
  . unAstNoSimplify

instance AstSpan s => BaseTensor (AstNoSimplify s) where
  -- The implementation of these methods differs from the AstRaw instance:
  trbuild1 @n @x k f = withSNat k $ \snat ->
    AstNoSimplify
    $ astBuild1Vectorize snat (STKR (SNat @n) (knownSTK @x))
                         (unAstNoSimplify . f . AstNoSimplify)
  tsbuild1 @k @sh @x f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @k) (STKS (knownShS @sh) (knownSTK @x))
                         (unAstNoSimplify . f . AstNoSimplify)
  txbuild1 @k @sh @x f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @k) (STKX (knownShX @sh) (knownSTK @x))
                         (unAstNoSimplify . f . AstNoSimplify)
  -- These three have tricky types, so we repaat the AstRaw definitions:
  tcond _ !b !u !v =
    AstNoSimplify $ AstCond b (unAstNoSimplify u) (unAstNoSimplify v)
  tdualPart _ t = dualPart $ unAstNoSimplify t
  tfromDual t = AstNoSimplify $ fromDual t

  -- All the following implementations piggy-back on AstRaw implementations.
  -- Ranked ops
  rshape = rshape . wunAstNoSimplify
  trsum = wAstNoSimplify . trsum . wunAstNoSimplify
  trreplicate k = wAstNoSimplify . trreplicate k . wunAstNoSimplify
  trindex v ix =
    wAstNoSimplify $ trindex (wunAstNoSimplify v) (wunAstNoSimplify <$> ix)
  trscatter sh t f =
    wAstNoSimplify $ trscatter sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  trgather sh t f =
    wAstNoSimplify $ trgather sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  trconcrete = wAstNoSimplify . trconcrete
  trfloor = wAstNoSimplify . trfloor . wunAstNoSimplify
  trfromIntegral = wAstNoSimplify . trfromIntegral . wunAstNoSimplify
  trcast = wAstNoSimplify . trcast . wunAstNoSimplify
  trminIndex = wAstNoSimplify . trminIndex . wunAstNoSimplify
  trmaxIndex = wAstNoSimplify . trmaxIndex . wunAstNoSimplify
  triota = wAstNoSimplify . triota
  trappend u v =
    wAstNoSimplify $ trappend (wunAstNoSimplify u) (wunAstNoSimplify v)
  trslice i n = wAstNoSimplify . trslice i n . wunAstNoSimplify
  trreverse = wAstNoSimplify . trreverse . wunAstNoSimplify
  trtranspose perm = wAstNoSimplify . trtranspose perm . wunAstNoSimplify
  trreshape sh = wAstNoSimplify . trreshape sh . wunAstNoSimplify

  -- Shaped ops
  sshape = sshape . wunAstNoSimplify
  tssum = wAstNoSimplify . tssum . wunAstNoSimplify
  tsindex v ix =
    wAstNoSimplify $ tsindex (wunAstNoSimplify v) (wunAstNoSimplify <$> ix)
  tsscatter @_ @shm @shn @shp t f =
    wAstNoSimplify $ tsscatter @_ @_ @shm @shn @shp (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  tsgather @_ @shm @shn @shp t f =
    wAstNoSimplify $ tsgather @_ @_ @shm @shn @shp (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  tsconcrete = wAstNoSimplify . tsconcrete
  tsfloor = wAstNoSimplify . tsfloor . wunAstNoSimplify
  tsfromIntegral = wAstNoSimplify . tsfromIntegral . wunAstNoSimplify
  tscast = wAstNoSimplify . tscast . wunAstNoSimplify
  tsminIndex = wAstNoSimplify . tsminIndex . wunAstNoSimplify
  tsmaxIndex = wAstNoSimplify . tsmaxIndex . wunAstNoSimplify
  tsiota = wAstNoSimplify tsiota
  tsappend u v =
    wAstNoSimplify $ tsappend (wunAstNoSimplify u) (wunAstNoSimplify v)
  tsslice i n k = wAstNoSimplify . tsslice i n k . wunAstNoSimplify
  tsreverse = wAstNoSimplify . tsreverse . wunAstNoSimplify

  -- Mixed ops
  xshape = xshape . wunAstNoSimplify
  txsum = wAstNoSimplify . txsum . wunAstNoSimplify
  txreplicate snat sh = wAstNoSimplify . txreplicate snat sh . wunAstNoSimplify
  txindex v ix =
    wAstNoSimplify $ txindex (wunAstNoSimplify v) (wunAstNoSimplify <$> ix)
  txscatter @_ @shm @shn @shp sh t f =
    wAstNoSimplify $ txscatter @_ @_ @shm @shn @shp sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  txgather @_ @shm @shn @shp sh t f =
    wAstNoSimplify $ txgather @_ @_ @shm @shn @shp sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  txconcrete = wAstNoSimplify . txconcrete
  txfloor = wAstNoSimplify . txfloor . wunAstNoSimplify
  txfromIntegral = wAstNoSimplify . txfromIntegral . wunAstNoSimplify
  txcast = wAstNoSimplify . txcast . wunAstNoSimplify
  txminIndex = wAstNoSimplify . txminIndex . wunAstNoSimplify
  txmaxIndex = wAstNoSimplify . txmaxIndex . wunAstNoSimplify
  txiota @n = wAstNoSimplify $ txiota @_ @n
  txappend u v =
    wAstNoSimplify $ txappend (wunAstNoSimplify u) (wunAstNoSimplify v)
  txslice i n k = wAstNoSimplify . txslice i n k . wunAstNoSimplify
  txreverse = wAstNoSimplify . txreverse . wunAstNoSimplify
  txtranspose perm = wAstNoSimplify . txtranspose perm . wunAstNoSimplify
  txreshape sh = wAstNoSimplify . txreshape sh . wunAstNoSimplify

  -- Scalar ops
  tkconcrete = wAstNoSimplify . tkconcrete
  tkfloor = wAstNoSimplify . tkfloor . wunAstNoSimplify
  tkfromIntegral = wAstNoSimplify . tkfromIntegral . wunAstNoSimplify
  tkcast = wAstNoSimplify . tkcast . wunAstNoSimplify

  -- General operations that don't require LetTensor nor ShareTensor
  tftk stk = tftk stk . wunAstNoSimplify
  tconcrete ftk a = wAstNoSimplify $ tconcrete ftk a
  tpair t1 t2 =
    wAstNoSimplify $ tpair (wunAstNoSimplify t1) (wunAstNoSimplify t2)
  tproject1 t = wAstNoSimplify $ tproject1 $ wunAstNoSimplify t
  tproject2 t = wAstNoSimplify $ tproject2 $ wunAstNoSimplify t
  tsreplicate snat sh = wAstNoSimplify . tsreplicate snat sh . wunAstNoSimplify
  tstranspose perm =
    wAstNoSimplify . tstranspose perm . wunAstNoSimplify
  tsreshape sh = wAstNoSimplify . tsreshape sh . wunAstNoSimplify
  tmapAccumRDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    wAstNoSimplify $ tmapAccumRDer Proxy k accftk bftk eftk f df rf
                       (wunAstNoSimplify acc0) (wunAstNoSimplify es)
  tmapAccumLDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    wAstNoSimplify $ tmapAccumLDer Proxy k accftk bftk eftk f df rf
                       (wunAstNoSimplify acc0) (wunAstNoSimplify es)
  tApply t ll = wAstNoSimplify $ tApply t (wunAstNoSimplify ll)
  tlambda = tlambda @(AstRaw s)
  tprimalPart t = wAstNoSimplify $ tprimalPart $ wunAstNoSimplify t
  tfromPrimal stk t = wAstNoSimplify $ tfromPrimal stk $ wunAstNoSimplify t
  tgrad = tgrad @(AstRaw s)
  tvjp = tvjp @(AstRaw s)
  tjvp = tjvp @(AstRaw s)

  tfromVector k stk =
    wAstNoSimplify . tfromVector k stk . V.map wunAstNoSimplify
  tsum snat@SNat stk u = case stk of
    STKScalar -> kfromS $ tssum u
    STKR SNat x | Dict <- lemKnownSTK x -> trsum u
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tssum u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txsum u
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (tsum snat stk1 (tproject1 u3))
              (tsum snat stk2 (tproject2 u3))
  treplicate snat@SNat stk u = case stk of
    STKScalar -> tsreplicate snat ZSS $ sfromK u
    STKR SNat x | Dict <- lemKnownSTK x -> trreplicate (sNatValue snat) u
    STKS sh x | Dict <- lemKnownSTK x -> tsreplicate snat sh u
    STKX sh x | Dict <- lemKnownSTK x -> txreplicate snat sh u
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (treplicate snat stk1 (tproject1 u3))
              (treplicate snat stk2 (tproject2 u3))
  tindexBuild snat@SNat stk u i = case stk of
    STKScalar -> kfromS $ tsindex u (i :.$ ZIS)
    STKR SNat x | Dict <- lemKnownSTK x -> trindex u (i :.: ZIR)
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tsindex u (i :.$ ZIS)
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txindex u (i :.% ZIX)
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (tindexBuild snat stk1 (tproject1 u3) i)
              (tindexBuild snat stk2 (tproject2 u3) i)

  treplTarget r ftk = wAstNoSimplify $ treplTarget r ftk
  tdefTarget = wAstNoSimplify . tdefTarget
  taddTarget stk a b = wAstNoSimplify $ taddTarget stk (wunAstNoSimplify a)
                                                       (wunAstNoSimplify b)
  tmultTarget stk a b = wAstNoSimplify $ tmultTarget stk (wunAstNoSimplify a)
                                                         (wunAstNoSimplify b)
  tsum0Target stk a = wAstNoSimplify $ tsum0Target stk (wunAstNoSimplify a)
  tdot0Target stk a b = wAstNoSimplify $ tdot0Target stk (wunAstNoSimplify a)
                                                         (wunAstNoSimplify b)

instance AstSpan s => ConvertTensor (AstNoSimplify s) where
  tconvert c astk bftk =
    wAstNoSimplify . tconvert c astk bftk . wunAstNoSimplify

  tfromS zstk = AstNoSimplify . AstFromS zstk . unAstNoSimplify
  rfromX = wAstNoSimplify . rfromX . wunAstNoSimplify
  xfromR = wAstNoSimplify . xfromR . wunAstNoSimplify

  sfromK = wAstNoSimplify . sfromK . wunAstNoSimplify
  sfromR = wAstNoSimplify . sfromR . wunAstNoSimplify
  sfromX = wAstNoSimplify . sfromX . wunAstNoSimplify

  rzip = wAstNoSimplify . rzip . wunAstNoSimplify
  runzip = wAstNoSimplify . runzip . wunAstNoSimplify
  szip = wAstNoSimplify . szip . wunAstNoSimplify
  sunzip = wAstNoSimplify . sunzip . wunAstNoSimplify
  xzip = wAstNoSimplify . xzip . wunAstNoSimplify
  xunzip = wAstNoSimplify . xunzip . wunAstNoSimplify

  xnestR sh = wAstNoSimplify . xnestR sh . wunAstNoSimplify
  xnestS sh = wAstNoSimplify . xnestS sh . wunAstNoSimplify
  xnest sh = wAstNoSimplify . xnest sh . wunAstNoSimplify
  xunNestR = wAstNoSimplify . xunNestR . wunAstNoSimplify
  xunNestS = wAstNoSimplify . xunNestS . wunAstNoSimplify
  xunNest = wAstNoSimplify . xunNest . wunAstNoSimplify

  tpairConv = tpair
  tunpairConv (AstNoSimplify (AstPair t1 t2)) =  -- a tiny bit of simplification
    (AstNoSimplify t1, AstNoSimplify t2)
  tunpairConv t = (tproject1 t, tproject2 t)
