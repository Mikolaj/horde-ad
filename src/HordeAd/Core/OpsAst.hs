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
  , revArtifactFromForwardPass, revProduceArtifact, revProduceArtifactDt
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

import Data.Array.Nested (Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert
  ( ixrFromIxS
  , ixsFromIxR
  , ixsFromIxR'
  , ixsFromIxX'
  , ixxFromIxS
  , withShsFromShR
  , withShsFromShX
  )
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
import HordeAd.Core.Conversion
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Delta
import HordeAd.Core.DeltaEval
import HordeAd.Core.Ops
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind
import HordeAd.Core.UnwindNum

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
  :: forall x z. TKAllNum (ADTensorKind z)
  => IncomingCotangentHandling
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
      unPrimal = unshareAstTensor $ unAstRaw primalBody
  return (AstArtifactRev varDt varPrimal unGradient unPrimal, delta)

revProduceArtifact
  :: forall x z. TKAllNum (ADTensorKind z)
  => IncomingCotangentHandling
  -> (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullShapeTK x
  -> AstArtifactRev x z
{-# INLINE revProduceArtifact #-}
revProduceArtifact cotangentHandling g envInit xftk =
  fst $ inline revArtifactFromForwardPass
          cotangentHandling (forwardPassByInterpretation g envInit) xftk

-- These two functions are as above, but the dt must be provided and so,
-- due to technical reasons, the type is less constrained.
revArtifactFromForwardPassDt
  :: forall x z.
     (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullShapeTK x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
-- Break the inline chain to prevent false positives in inspection testing
-- and protect the unsafePerformIO.
{-# NOINLINE revArtifactFromForwardPassDt #-}
revArtifactFromForwardPassDt forwardPass xftk = unsafePerformIO $ do
  -- IO and bangs and the compound function to fix the numbering of variables
  -- for pretty-printing and prevent sharing the impure values
  -- in tests that reset the impure counters.
  (!varPrimal, astVarPrimal, var, astVar0) <- funToAstRevIO xftk
  -- Evaluate completely after terms constructed, to free memory
  -- before gradientFromDelta allocates new memory and new FFI is started.
  let !(D primalBody delta) = forwardPass astVarPrimal var astVar0
  let zftk = ftkAst $ unAstRaw primalBody
      (!varDt, !dt) = funToAst (adFTK zftk) Nothing id
  let !gradient = gradientFromDelta xftk zftk (AstRaw dt) delta
      !unGradient = unshareAstTensor $ unAstRaw gradient
      unPrimal = unshareAstTensor $ unAstRaw primalBody
  return (AstArtifactRev varDt varPrimal unGradient unPrimal, delta)

revProduceArtifactDt
  :: forall x z.
     (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullShapeTK x
  -> AstArtifactRev x z
{-# INLINE revProduceArtifactDt #-}
revProduceArtifactDt g envInit xftk =
  fst $ inline revArtifactFromForwardPassDt
          (forwardPassByInterpretation g envInit) xftk

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
      unPrimal = unshareAstTensor $ unAstRaw primalBody
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
{-# INLINE astBuild1Vectorize #-}
astBuild1Vectorize k@(SNat @k) stk f =
  build1Vectorize k stk $ funToAstI (Just (0, valueOf @k - 1)) f

instance AstSpan s => LetTensor (AstTensor AstMethodLet s) where
  ttlet = astLetFun
  ttletPrimal = astLetFun
  ttletPlain = astLetFun
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
--
-- Them methods are listed in ranked, shaped, mixed order to keep
-- similar code transformations together.
instance AstSpan s => BaseTensor (AstTensor AstMethodLet s) where
  -- Ranked ops
  rshape t = case ftkAst t of
    FTKR sh _ -> sh
  trsum v = withSNat (rwidth v) $ \snat -> astSum snat knownSTK v
  trreplicate k = withSNat k $ \snat -> astReplicate snat knownSTK
  trconcrete a = tconcrete (FTKR (Nested.rshape a) FTKScalar) (Concrete a)
  trfloor @_ @r2 a = case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        astFromS' @(TKS sh r2) (FTKR sh' FTKScalar)
        . fromPlain . astFloorS . astPlainPart . astSFromR' @sh sh $ a
  trfromIntegral @_ @r2 a = case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        astFromS' @(TKS sh r2) (FTKR sh' FTKScalar)
        . fromPlain . astFromIntegralS . astPlainPart . astSFromR' @sh sh $ a
  trcast @_ @r2 a = case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        astFromS' @(TKS sh r2) (FTKR sh' FTKScalar)
        . astCastS . astSFromR' sh $ a
  trindex @m @n a ix = case ftkAst a of
    FTKR @_ @x shmshn x ->
      withShsFromShR shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (shsTake @m sh) $
        astFromS' @(TKS2 (Drop m sh) x) (FTKR (shrDrop @m shmshn) x)
        $ astIndexS @(Take m sh) @(Drop m sh)
                    (shsDrop @m sh) (astSFromR' @sh sh a)
                    (ixsFromIxR' knownShS ix)
  trindex0 a ix = kfromR $ trindex a ix
  trscatter @m @_ @p shpshn0 t f = case ftkAst t of
    FTKR @_ @x shmshn0 x ->
      withShsFromShR shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShR shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (shsTake @m shmshn) $
        withKnownShS (shsDrop @m shmshn) $
        withKnownShS (shsTake @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop p shpshn :~: shpshn) $
        case testEquality (shsDrop @p shpshn) (shsDrop @m shmshn) of
          Just Refl ->
            astFromS' @(TKS2 shpshn x) (FTKR shpshn0 x)
            $ astScatterS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                          knownShS (astSFromR' shmshn t)
            $ funToAstIxS knownShS (ixsFromIxR' knownShS . f . ixrFromIxS)
                -- this introduces new variable names
          _ -> error $ "rscatter: shapes don't match: "
                       ++ show (shsDrop @p shpshn, shsDrop @m shmshn)
  trgather @m @_ @p shmshn0 t f = case ftkAst t of
    FTKR shpshn0 x ->
      withShsFromShR shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShR shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (shsTake @m shmshn) $
        withKnownShS (shsDrop @m shmshn) $
        withKnownShS (shsTake @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop p shpshn :~: shpshn) $
        case testEquality (shsDrop @p shpshn) (shsDrop @m shmshn) of
          Just Refl ->
            astFromS' (FTKR shmshn0 x)
            $ astGatherS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                         knownShS (astSFromR' shpshn t)
            $ funToAstIxS knownShS (ixsFromIxR' knownShS . f . ixrFromIxS)
                -- this introduces new variable names
          _ -> error $ "rgather: shapes don't match: "
                       ++ show (shsDrop @p shpshn, shsDrop @m shmshn)
  trminIndex @_ @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ _ ->
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS' @(TKS (Init sh) r2) (FTKR (shrInit sh') FTKScalar)
          . fromPlain . AstMinIndexS . astPlainPart . astSFromR' @sh sh $ a
        ZSS -> error "rminIndex: impossible empty shape"
  trmaxIndex @_ @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS' @(TKS (Init sh) r2) (FTKR (shrInit sh') FTKScalar)
          . fromPlain . AstMaxIndexS . astPlainPart . astSFromR' @sh sh $ a
        ZSS -> error "rmaxIndex: impossible empty shape"
  triota @r n =
    withSNat n $ \(SNat @n) ->
      astFromS' (FTKR (n :$: ZSR) FTKScalar)
      $ fromPlain $ AstIotaS @n @r SNat
  trappend u v = case ftkAst u of
    FTKR shu' x -> case ftkAst v of
      FTKR shv' _ ->
        withShsFromShR shu' $ \shu -> case shu of
          _ :$$ restu ->
            withShsFromShR shv' $ \shv -> case shv of
              _ :$$ restv ->
                case testEquality restu restv of
                  Just Refl ->
                    astFromS' (FTKR shu' x)
                    $ astAppendS (astSFromR' shu u) (astSFromR' shv v)
                  _ -> error $ "rappend: shapes don't match: "
                               ++ show (restu, restv)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  trslice i n a = case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh -> case sh of
        msnat@(SNat @m) :$$ _ ->
          withSNat i $ \isnat@(SNat @i) -> withSNat n $ \nsnat@(SNat @n) ->
            case cmpNat (snatPlus isnat nsnat) msnat of
              GTI -> error $ "rslice: argument tensor too narrow: "
                             ++ show (i, n, sNatValue msnat)
              EQI ->
                astFromS' (FTKR sh' x)
                . astSliceS isnat nsnat (SNat @(m - (i + n)))
                . astSFromR' sh $ a
              LTI ->
                astFromS' (FTKR sh' x)
                . astSliceS isnat nsnat (SNat @(m - (i + n)))
                . astSFromR' sh $ a
        ZSS -> error "xslice: impossible shape"
  trreverse a = case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh -> case sh of
        _ :$$ _ ->
          astFromS' (FTKR sh' x)
          . astReverseS . astSFromR' sh $ a
        ZSS -> error "xreverse: impossible shape"
  trtranspose @n @r permr a = case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \(sh :: ShS sh)  ->
        Permutation.permFromListCont permr $ \(perm :: Permutation.Perm perm) ->
          let result :: AstTensor AstMethodLet s (TKR2 n r)
              result =
                -- A noble lie, verified down below.
                gcastWith (unsafeCoerceRefl
                           :: (Rank perm <=? Rank sh) :~: True) $
                fromMaybe (error "rtranspose: impossible non-permutation")
                $ Permutation.permCheckPermutation perm
                $ astFromS' (FTKR (shrPermutePrefix permr sh') x)
                  . astTransposeS perm . astSFromR' sh $ a
          in case (Permutation.permRank perm, shsRank sh) of
            (psnat@SNat, shsnat@SNat) ->
              case cmpNat psnat shsnat of
                GTI -> error $ "rtranspose: rank mismatch: "
                               ++ show (sNatValue psnat, sNatValue shsnat)
                EQI -> result
                LTI -> result
  trreshape sh2' a = case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh ->
      withShsFromShR sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl -> astFromS' (FTKR sh2' x)
                       . astReshapeS sh2 . astSFromR' sh $ a
          _ -> error $ "rreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  trbuild1 @n @x k f = withSNat k $ \snat ->
    astBuild1Vectorize snat (STKR (SNat @n) (knownSTK @x)) f

  -- Shaped ops
  sshape t = case ftkAst t of
    FTKS sh _ -> sh
  tssum = astSum SNat knownSTK
  tsreplicate snat sh = astReplicate snat (STKS sh knownSTK)
  tsconcrete = fromPlain . AstConcreteS
  tsfloor = fromPlain . astFloorS . astPlainPart
  tsfromIntegral = fromPlain . astFromIntegralS . astPlainPart
  tscast = astCastS
  tsindex = astIndexS knownShS
  tsindex0 @sh a ix | Refl <- lemAppNil @sh = kfromS $ tsindex a ix
  tsscatter @shm @shn @shp t f =
    astScatterS @shm @shn @shp knownShS t
    $ funToAstIxS knownShS f  -- this introduces new variable names
  tsgather @shm @shn @shp t f =
    astGatherS @shm @shn @shp knownShS t
    $ funToAstIxS knownShS f  -- this introduces new variable names
  tsminIndex = fromPlain . AstMinIndexS . astPlainPart
  tsmaxIndex = fromPlain . AstMaxIndexS . astPlainPart
  tsiota = fromPlain $ AstIotaS SNat
  tsappend = astAppendS
  tsslice = astSliceS
  tsreverse = astReverseS
  tstranspose = astTransposeS
  tsreshape = astReshapeS
  tsbuild1 @k @sh @x =
    astBuild1Vectorize (SNat @k) (STKS (knownShS @sh) (knownSTK @x))

  -- Mixed ops
  xshape t = case ftkAst t of
    FTKX sh _ -> sh
  txsum = astSum SNat knownSTK
  txreplicate snat sh = astReplicate snat (STKX sh knownSTK)
  txconcrete a = tconcrete (FTKX (Nested.mshape a) FTKScalar) (Concrete a)
  txfloor @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        astFromS' @(TKS sh r2) (FTKX sh' FTKScalar)
        . fromPlain . astFloorS . astPlainPart . astSFromX' @sh @sh' sh $ a
  txfromIntegral @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        astFromS' @(TKS sh r2) (FTKX sh' FTKScalar)
        . fromPlain . astFromIntegralS
        . astPlainPart . astSFromX' @sh @sh' sh $ a
  txcast @_ @r2 a = case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        astFromS' @(TKS sh r2) (FTKX sh' FTKScalar)
        . astCastS . astSFromX' sh $ a
  txindex @sh1 @sh2 a ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 x | SNat <- ssxRank (knownShX @sh1) ->
      withShsFromShX sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShX (ssxFromShX sh1sh2) $
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) sh1sh2 :~: sh2) $
        withKnownShS (shsTake @(Rank sh1) sh) $
        astFromS' @(TKS2 (Drop (Rank sh1) sh) x)
                  (FTKX (shxDrop @(Rank sh1) sh1sh2) x)
        $ astIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (shsDrop @(Rank sh1) sh) (astSFromX' @sh @sh1sh2 sh a)
                    (ixsFromIxX' knownShS ix)
  txindex0 @sh a ix | Refl <- lemAppNil @sh = kfromX $ txindex a ix
  txscatter @shm @_ @shp shpshn0 t f = case ftkAst t of
    FTKX shmshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withShsFromShX shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShX shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (shsTake @(Rank shm) shmshn) $
        withKnownShS (shsDrop @(Rank shm) shmshn) $
        withKnownShS (shsTake @(Rank shp) shpshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        case testEquality (shsDrop @(Rank shp) shpshn)
                          (shsDrop @(Rank shm) shmshn) of
          Just Refl ->
            astFromS' (FTKX shpshn0 x)
            $ astScatterS @(Take (Rank shm) shmshn)
                          @(Drop (Rank shm) shmshn)
                          @(Take (Rank shp) shpshn)
                          knownShS (astSFromX' shmshn t)
            $ funToAstIxS knownShS (ixsFromIxX' knownShS
                                    . f . ixxCast knownShX . ixxFromIxS)
                -- this introduces new variable names
          _ -> error $ "xscatter: shapes don't match: "
                       ++ show ( shsDrop @(Rank shp) shpshn
                               , shsDrop @(Rank shm) shmshn )
  txgather @shm @_ @shp shmshn0 t f = case ftkAst t of
    FTKX shpshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withShsFromShX shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShX shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (shsTake @(Rank shm) shmshn) $
        withKnownShS (shsDrop @(Rank shm) shmshn) $
        withKnownShS (shsTake @(Rank shp) shpshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        case testEquality (shsDrop @(Rank shp) shpshn)
                          (shsDrop @(Rank shm) shmshn) of
          Just Refl ->
            astFromS' (FTKX shmshn0 x)
            $ astGatherS @(Take (Rank shm) shmshn)
                         @(Drop (Rank shm) shmshn)
                         @(Take (Rank shp) shpshn)
                         knownShS (astSFromX' shpshn t)
            $ funToAstIxS knownShS (ixsFromIxX' knownShS
                                    . f . ixxCast knownShX . ixxFromIxS)
                -- this introduces new variable names
          _ -> error $ "xgather: shapes don't match: "
                       ++ show ( shsDrop @(Rank shp) shpshn
                               , shsDrop @(Rank shm) shmshn )
  txminIndex @_ @_ @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS' @(TKS (Init sh) r2)
                    (FTKX (shxInit sh') FTKScalar)
          . fromPlain . AstMinIndexS @n @rest
          . astPlainPart . astSFromX' @sh @sh' sh $ a
  txmaxIndex @_ @_ @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS' @(TKS (Init sh) r2)
                   (FTKX (shxInit sh') FTKScalar)
          . fromPlain . AstMaxIndexS @n @rest
          . astPlainPart . astSFromX' @sh @sh' sh $ a
  txiota @n @r = astFromS' (FTKX (SKnown (SNat @n) :$% ZSX) FTKScalar)
                 $ fromPlain $ AstIotaS @n @r SNat
  txappend u v = case ftkAst u of
    FTKX (Nested.SKnown m@SNat :$% shu') x -> case ftkAst v of
      FTKX (Nested.SKnown n@SNat :$% shv') _ ->
        withShsFromShX shu' $ \(shu :: ShS shu) ->
          withShsFromShX shv' $ \(shv :: ShS shv) ->
            case shxEqual shu' shv' of
              Just Refl ->
                gcastWith (unsafeCoerceRefl :: shu :~: shv) $
                astFromS' (FTKX (Nested.SKnown (snatPlus m n) :$% shu') x)
                $ astAppendS (astSFromX' (m :$$ shu) u)
                             (astSFromX' (n :$$ shv) v)
              _ -> error $ "xappend: shapes don't match: "
                           ++ show (shu', shv')
  txslice i n@SNat k a = case ftkAst a of
    FTKX sh'@(_ :$% sh2') x ->
      withShsFromShX sh' $ \sh@(msnat :$$ _) ->
        case testEquality (snatPlus i (snatPlus n k)) msnat of
          Just Refl ->
            astFromS' (FTKX (SKnown n :$% sh2') x)
            . astSliceS i n k . astSFromX' sh $ a
          _ -> error $ "xslice: argument tensor too narrow: "
                       ++ show ( sNatValue i, sNatValue n, sNatValue k
                               , sNatValue msnat )
  txreverse a = case ftkAst a of
    FTKX sh' x ->
      withShsFromShX sh' $ \(sh@(_ :$$ _) :: ShS sh) ->
        astFromS' (FTKX sh' x)
        . astReverseS . astSFromX' @sh sh $ a
  txtranspose perm a = case ftkAst a of
    FTKX sh' x ->
      let sh2' = shxPermutePrefix perm sh'
      in withShsFromShX sh' $ \sh ->
           astFromS' (FTKX sh2' x)
           . astTransposeS perm . astSFromX' sh $ a
  txreshape sh2' a = case ftkAst a of
    FTKX sh' x ->
      withShsFromShX sh' $ \sh ->
      withShsFromShX sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl ->
            astFromS' (FTKX sh2' x)
            . astReshapeS sh2 . astSFromX' sh $ a
          _ -> error $ "xreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  txbuild1 @k @sh @x =
    astBuild1Vectorize (SNat @k) (STKX (knownShX @sh) (knownSTK @x))

  -- Scalar ops
  tkconcrete = fromPlain . AstConcreteK
  tkfloor = fromPlain . astFloorK . astPlainPart
  tkfromIntegral = fromPlain . astFromIntegralK . astPlainPart
  tkcast = astCastK

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk = ftkAst
  tpair = astPair
  tproject1 = astProject1
  tproject2 = astProject2
  tcond _ !b !u !v = astCond b u v
  tconcrete ftk a = fromPlain $ astConcrete ftk a
  tfromVector = astFromVector
  tmapAccumRDer _ !k _ !bftk !eftk f df rf acc0 es =
    astMapAccumRDer k bftk eftk f df rf acc0 es
  tmapAccumLDer _ !k _ !bftk !eftk f df rf acc0 es =
    astMapAccumLDer k bftk eftk f df rf acc0 es
  tapply = astApply
  tlambda ftk f =
    let (var, ast) = funToAst ftk Nothing $ unHFun f
    in AstLambda var ast
  tgrad @_ @r xftk f | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
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
          revProduceArtifactDt
            (simplifyInline . unHFun f) emptyEnv ftkx
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

  tprimalPart = astPrimalPart
  tdualPart _ = dualPart
  tplainPart = astPlainPart
  tfromPrimal _ = fromPrimal
  tfromDual = fromDual
  tfromPlain _ = fromPlain

  treplTarget = replTarget
  tdefTarget = defTarget
  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target


-- * AstRaw instances

instance AstSpan s => LetTensor (AstRaw s) where
  ttlet u f =
    let !var2 = tshare u
    in f var2
  ttletPrimal u f =
    let !var2 = tshare u
    in f var2
  ttletPlain u f =
    let !var2 = tshare u
    in f var2
  toShare = id
  tunshare = id

instance AstSpan s => ShareTensor (AstRaw s) where
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tshare t = AstRaw $ astShareNoSimplify $ unAstRaw t
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
  trconcrete a = tconcrete (FTKR (Nested.rshape a) FTKScalar) (Concrete a)
  trfloor @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        cAstFromS @(TKS sh r2) (FTKR sh' FTKScalar)
        . fromPlain . AstFloorS . plainPart . cAstSFromR @sh sh $ a
  trfromIntegral @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        cAstFromS @(TKS sh r2) (FTKR sh' FTKScalar)
        . fromPlain . AstFromIntegralS . plainPart . cAstSFromR @sh sh $ a
  trcast @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        cAstFromS @(TKS sh r2) (FTKR sh' FTKScalar)
        . AstCastS . cAstSFromR sh $ a
  trindex @m @n (AstRaw a) ix = AstRaw $ case ftkAst a of
    FTKR @_ @x shmshn x ->
      withShsFromShR shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (shsTake @m sh) $
        cAstFromS @(TKS2 (Drop m sh) x) (FTKR (shrDrop @m shmshn) x)
        $ AstIndexS @(Take m sh) @(Drop m sh)
                    (shsDrop @m sh) (cAstSFromR @sh sh a)
                    (ixsFromIxR knownShS (unAstRaw <$> ix))
  trindex0 a ix = kfromR $ trindex a ix
  trscatter @m @_ @p shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR @_ @x shmshn0 x ->
      withShsFromShR shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShR shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (shsTake @m shmshn) $
        withKnownShS (shsDrop @m shmshn) $
        withKnownShS (shsTake @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop p shpshn :~: shpshn) $
        case testEquality (shsDrop @p shpshn) (shsDrop @m shmshn) of
          Just Refl ->
            cAstFromS @(TKS2 shpshn x) (FTKR shpshn0 x)
            $ AstScatterS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                          knownShS (cAstSFromR shmshn t)
            $ funToAstIxS knownShS (fmap unAstRaw . ixsFromIxR knownShS
                                    . f . ixrFromIxS
                                    . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "rscatter: shapes don't match: "
                       ++ show (shsDrop @p shpshn, shsDrop @m shmshn)
  trgather @m @_ @p shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR shpshn0 x ->
      withShsFromShR shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShR shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (shsTake @m shmshn) $
        withKnownShS (shsDrop @m shmshn) $
        withKnownShS (shsTake @p shpshn) $
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop p shpshn :~: shpshn) $
        case testEquality (shsDrop @p shpshn) (shsDrop @m shmshn) of
          Just Refl ->
            cAstFromS (FTKR shmshn0 x)
            $ AstGatherS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                         knownShS (cAstSFromR shpshn t)
            $ funToAstIxS knownShS (fmap unAstRaw . ixsFromIxR knownShS
                                    . f . ixrFromIxS
                           . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "rgather: shapes don't match: "
                       ++ show (shsDrop @p shpshn, shsDrop @m shmshn)
  trminIndex @_ @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ _ ->
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          cAstFromS @(TKS (Init sh) r2) (FTKR (shrInit sh') FTKScalar)
          . fromPlain . AstMinIndexS . plainPart . cAstSFromR @sh sh $ a
        ZSS -> error "rminIndex: impossible shape"
  trmaxIndex @_ @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          cAstFromS @(TKS (Init sh) r2) (FTKR (shrInit sh') FTKScalar)
          . fromPlain . AstMaxIndexS . plainPart . cAstSFromR @sh sh $ a
        ZSS -> error "rmaxIndex: impossible shape"
  triota @r n =
    AstRaw
    $ withSNat n $ \(SNat @n) ->
        cAstFromS (FTKR (n :$: ZSR) FTKScalar)
        $ fromPlain $ AstIotaS @n @r SNat
  trappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    ftk@(FTKR shu' _) -> case ftkAst v of
      FTKR shv' _ ->
        withShsFromShR shu' $ \shu -> case shu of
          _ :$$ restu ->
            withShsFromShR shv' $ \shv -> case shv of
              _ :$$ restv ->
                case testEquality restu restv of
                  Just Refl ->
                    cAstFromS ftk
                    $ AstAppendS (cAstSFromR shu u) (cAstSFromR shv v)
                  _ -> error $ "rappend: shapes don't match: "
                               ++ show (restu, restv)
              ZSS -> error "rappend: impossible shape"
          ZSS -> error "rappend: impossible shape"
  trslice i n (AstRaw a) = AstRaw $ case ftkAst a of
    ftk@(FTKR sh' _) ->
      withShsFromShR sh' $ \sh -> case sh of
        msnat@(SNat @m) :$$ _ ->
          withSNat i $ \isnat@(SNat @i) -> withSNat n $ \nsnat@(SNat @n) ->
            case cmpNat (snatPlus isnat nsnat) msnat of
              GTI -> error $ "rslice: argument tensor too narrow: "
                             ++ show (i, n, sNatValue msnat)
              EQI ->
                cAstFromS ftk
                . AstSliceS isnat nsnat (SNat @(m - (i + n)))
                . cAstSFromR sh $ a
              LTI ->
                cAstFromS ftk
                . AstSliceS isnat nsnat (SNat @(m - (i + n)))
                . cAstSFromR sh $ a
        ZSS -> error "xslice: impossible shape"
  trreverse (AstRaw a) = AstRaw $ case ftkAst a of
    ftk@(FTKR sh' _) ->
      withShsFromShR sh' $ \sh -> case sh of
        _ :$$ _ ->
          cAstFromS ftk
          . AstReverseS . cAstSFromR sh $ a
        ZSS -> error "xreverse: impossible shape"
  trtranspose @n @r permr (AstRaw a) = AstRaw $ case ftkAst a of
    ftk@(FTKR sh' _) ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        Permutation.permFromListCont permr $ \(perm :: Permutation.Perm perm) ->
          let result :: AstTensor AstMethodShare s (TKR2 n r)
              result =
                -- A noble lie, verified down below.
                gcastWith (unsafeCoerceRefl
                           :: (Rank perm <=? Rank sh) :~: True) $
                fromMaybe (error "rtranspose: impossible non-permutation")
                $ Permutation.permCheckPermutation perm
                $ cAstFromS ftk
                  . AstTransposeS perm . cAstSFromR sh $ a
          in case (Permutation.permRank perm, shsRank sh) of
            (psnat@SNat, shsnat@SNat) ->
              case cmpNat psnat shsnat of
                GTI -> error $ "rtranspose: rank mismatch: "
                               ++ show (sNatValue psnat, sNatValue shsnat)
                EQI -> result
                LTI -> result
  trreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh ->
      withShsFromShR sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl -> cAstFromS (FTKR sh2' x)
                       . AstReshapeS sh2 . cAstSFromR sh $ a
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
  tsreplicate snat sh = AstRaw . AstReplicate snat (STKS sh knownSTK) . unAstRaw
  tsconcrete = AstRaw . fromPlain . AstConcreteS
  tsfloor = AstRaw . fromPlain . AstFloorS . plainPart . unAstRaw
  tsfromIntegral =
    AstRaw . fromPlain . AstFromIntegralS . plainPart . unAstRaw
  tscast = AstRaw . AstCastS . unAstRaw
  tsindex v ix = AstRaw $ AstIndexS knownShS (unAstRaw v) (unAstRaw <$> ix)
  tsindex0 @sh a ix | Refl <- lemAppNil @sh = kfromS $ tsindex a ix
  tsscatter @shm @shn @shp t f =
    AstRaw $ AstScatterS @shm @shn @shp knownShS (unAstRaw t)
           $ funToAstIxS knownShS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  tsgather @shm @shn @shp t f =
    AstRaw $ AstGatherS @shm @shn @shp knownShS (unAstRaw t)
           $ funToAstIxS knownShS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  tsminIndex = AstRaw . fromPlain . AstMinIndexS . plainPart . unAstRaw
  tsmaxIndex = AstRaw . fromPlain . AstMaxIndexS . plainPart . unAstRaw
  tsiota = AstRaw . fromPlain $ AstIotaS SNat
  tsappend u v = AstRaw $ AstAppendS (unAstRaw u) (unAstRaw v)
  tsslice i n k = AstRaw . AstSliceS i n k . unAstRaw
  tsreverse = AstRaw . AstReverseS . unAstRaw
  tstranspose perm = AstRaw . AstTransposeS perm . unAstRaw
  tsreshape sh = AstRaw . AstReshapeS sh . unAstRaw
  tsbuild1 @k f = AstRaw $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstI (Just (0, valueOf @k - 1))
                      -- this introduces new variable names
                  $ unAstRaw . f . AstRaw

  -- Mixed ops
  xshape t = case ftkAst $ unAstRaw t of
    FTKX sh _ -> sh
  txsum = AstRaw . AstSum SNat knownSTK . unAstRaw
  txreplicate snat sh = AstRaw . AstReplicate snat (STKX sh knownSTK) . unAstRaw
  txconcrete a = tconcrete (FTKX (Nested.mshape a) FTKScalar) (Concrete a)
  txfloor @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        cAstFromS @(TKS sh r2) (FTKX sh' FTKScalar)
        . fromPlain . AstFloorS . plainPart . cAstSFromX @sh @sh' sh $ a
  txfromIntegral @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        cAstFromS @(TKS sh r2) (FTKX sh' FTKScalar)
        . fromPlain . AstFromIntegralS
        . plainPart . cAstSFromX @sh @sh' sh $ a
  txcast @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        cAstFromS @(TKS sh r2) (FTKX sh' FTKScalar)
        . AstCastS . cAstSFromX sh $ a
  txindex @sh1 @sh2 (AstRaw a) ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 x | SNat <- ssxRank (knownShX @sh1) ->
      withShsFromShX sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShX (ssxFromShX sh1sh2) $
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) sh1sh2 :~: sh2) $
        withKnownShS (shsTake @(Rank sh1) sh) $
        AstRaw $ cAstFromS @(TKS2 (Drop (Rank sh1) sh) x)
                           (FTKX (shxDrop @(Rank sh1) sh1sh2) x)
        $ AstIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (shsDrop @(Rank sh1) sh) (cAstSFromX @sh @sh1sh2 sh a)
                    (ixsFromIxX' knownShS (unAstRaw <$> ix))
  txindex0 @sh a ix | Refl <- lemAppNil @sh = kfromX $ txindex a ix
  txscatter @shm @_ @shp shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shmshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withShsFromShX shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShX shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (shsTake @(Rank shm) shmshn) $
        withKnownShS (shsDrop @(Rank shm) shmshn) $
        withKnownShS (shsTake @(Rank shp) shpshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        case testEquality (shsDrop @(Rank shp) shpshn)
                          (shsDrop @(Rank shm) shmshn) of
          Just Refl ->
            cAstFromS (FTKX shpshn0 x)
            $ AstScatterS @(Take (Rank shm) shmshn)
                          @(Drop (Rank shm) shmshn)
                          @(Take (Rank shp) shpshn)
                          knownShS (cAstSFromX shmshn t)
            $ funToAstIxS knownShS (fmap unAstRaw
                                    . ixsFromIxX' knownShS
                                    . f . ixxCast knownShX . ixxFromIxS
                                    . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "xscatter: shapes don't match: "
                       ++ show ( shsDrop @(Rank shp) shpshn
                               , shsDrop @(Rank shm) shmshn )
  txgather @shm @_ @shp shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shpshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withShsFromShX shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShX shpshn0 $ \(shpshn :: ShS shpshn) ->
        withKnownShS shmshn $
        withKnownShS shpshn $
        withKnownShS (shsTake @(Rank shm) shmshn) $
        withKnownShS (shsDrop @(Rank shm) shmshn) $
        withKnownShS (shsTake @(Rank shp) shpshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        case testEquality (shsDrop @(Rank shp) shpshn)
                          (shsDrop @(Rank shm) shmshn) of
          Just Refl ->
            cAstFromS (FTKX shmshn0 x)
            $ AstGatherS @(Take (Rank shm) shmshn)
                         @(Drop (Rank shm) shmshn)
                         @(Take (Rank shp) shpshn)
                         knownShS (cAstSFromX shpshn t)
            $ funToAstIxS knownShS (fmap unAstRaw
                                    . ixsFromIxX' knownShS
                                    . f . ixxCast knownShX . ixxFromIxS
                                    . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "xgather: shapes don't match: "
                       ++ show ( shsDrop @(Rank shp) shpshn
                               , shsDrop @(Rank shm) shmshn )
  txminIndex @_ @_ @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          cAstFromS @(TKS (Init sh) r2)
                    (FTKX (shxInit sh') FTKScalar)
          . fromPlain . AstMinIndexS @n @rest
          . plainPart . cAstSFromX @sh @sh' sh $ a
  txmaxIndex @_ @_ @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          cAstFromS @(TKS (Init sh) r2)
                   (FTKX (shxInit sh') FTKScalar)
          . fromPlain . AstMaxIndexS @n @rest
          . plainPart . cAstSFromX @sh @sh' sh $ a
  txiota @n @r = AstRaw $ cAstFromS (FTKX (SKnown (SNat @n) :$% ZSX) FTKScalar)
                 $ fromPlain $ AstIotaS @n @r SNat
  txappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKX (Nested.SKnown m@SNat :$% shu') x -> case ftkAst v of
      FTKX (Nested.SKnown n@SNat :$% shv') _ ->
        withShsFromShX shu' $ \(shu :: ShS shu) ->
          withShsFromShX shv' $ \(shv :: ShS shv) ->
            case shxEqual shu' shv' of
              Just Refl ->
                gcastWith (unsafeCoerceRefl :: shu :~: shv) $
                cAstFromS (FTKX (SKnown (snatPlus m n) :$% shu') x)
                $ AstAppendS (cAstSFromX (m :$$ shu) u)
                             (cAstSFromX (n :$$ shv) v)
              _ -> error $ "xappend: shapes don't match: "
                           ++ show (shu', shv')
  txslice i n@SNat k (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh'@(_ :$% sh2') x ->
      withShsFromShX sh' $ \sh@(msnat :$$ _) ->
        case testEquality (snatPlus i (snatPlus n k)) msnat of
          Just Refl ->
            cAstFromS (FTKX (SKnown n :$% sh2') x)
            . AstSliceS i n k . cAstSFromX sh $ a
          _ -> error $ "xslice: argument tensor too narrow: "
                       ++ show ( sNatValue i, sNatValue n, sNatValue k
                               , sNatValue msnat )
  txreverse (AstRaw a) = AstRaw $ case ftkAst a of
    ftk@(FTKX sh' _) ->
      withShsFromShX sh' $ \(sh@(_ :$$ _) :: ShS sh) ->
        cAstFromS ftk
        . AstReverseS . cAstSFromX @sh sh $ a
  txtranspose perm (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      let sh2' = shxPermutePrefix perm sh'
      in withShsFromShX sh' $ \sh ->
           cAstFromS (FTKX sh2' x)
           . AstTransposeS perm
           . cAstSFromX sh $ a
  txreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      withShsFromShX sh' $ \sh ->
      withShsFromShX sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl ->
            cAstFromS (FTKX sh2' x)
            . AstReshapeS sh2 . cAstSFromX sh $ a
          _ -> error $ "xreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  txbuild1 @k f = AstRaw $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstI (Just (0, valueOf @k - 1))
                      -- this introduces new variable names
                  $ unAstRaw . f . AstRaw

  -- Scalar ops
  tkconcrete = AstRaw . fromPlain . AstConcreteK
  tkfloor = AstRaw . fromPlain . AstFloorK . plainPart . unAstRaw
  tkfromIntegral = AstRaw . fromPlain . AstFromIntegralK
                   . plainPart . unAstRaw
  tkcast = AstRaw . AstCastK . unAstRaw

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk = ftkAst . unAstRaw
  tpair t1 t2 = AstRaw $ AstPair (unAstRaw t1) (unAstRaw t2)
  tproject1 t = AstRaw $ AstProject1 $ unAstRaw t
  tproject2 t = AstRaw $ AstProject2 $ unAstRaw t
  tcond _ !b !u !v = AstRaw $ AstCond (unAstRaw b) (unAstRaw u) (unAstRaw v)
  tconcrete ftk a = AstRaw $ fromPlain $ unAstRaw $ astConcreteRaw ftk a
  tfromVector k stk =
    AstRaw . AstFromVector k stk . V.map unAstRaw
  tmapAccumRDer _ !k _ !bftk !eftk f df rf acc0 es =
    AstRaw $ AstMapAccumRDer k bftk eftk f df rf (unAstRaw acc0) (unAstRaw es)
  tmapAccumLDer _ !k _ !bftk !eftk f df rf acc0 es =
    AstRaw $ AstMapAccumLDer k bftk eftk f df rf (unAstRaw acc0) (unAstRaw es)
  tapply t ll = AstRaw $ AstApply t (unAstRaw ll)
  tlambda = tlambda @(AstTensor AstMethodLet s)
  -- These three methods are called at this type in delta evaluation via
  -- tmapAccumR and tmapAccumL, so they have to work. We could refrain from
  -- simplifying the resulting terms, but it's not clear that's more consistent.
  tgrad = tgrad @(AstTensor AstMethodLet s)
  tvjp = tvjp @(AstTensor AstMethodLet s)
  tjvp = tjvp @(AstTensor AstMethodLet s)

  tprimalPart t = AstRaw $ primalPart $ unAstRaw t
  tdualPart _ t = dualPart $ unAstRaw t
  tplainPart t = AstRaw $ plainPart $ unAstRaw t
  tfromPrimal _ t = AstRaw $ fromPrimal $ unAstRaw t
  tfromDual t = AstRaw $ fromDual t
  tfromPlain _ t = AstRaw $ fromPlain $ unAstRaw t

  treplTarget = replTarget
  tdefTarget = defTarget
  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target

instance AstSpan s => ConvertTensor (AstRaw s) where
  tconvert c _astk = AstRaw . cAstConvert c . unAstRaw

  rfromX a = case ftkAst $ unAstRaw a of
    FTKX sh' _ ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        withKnownShS sh $
        rfromS $ sfromX @_ @sh a
  xfromR a = case ftkAst $ unAstRaw a of
    FTKR shr _ ->
      withShsFromShR shr $ \(sh :: ShS sh) ->
        withKnownShS sh $
        xfromS @_ @sh $ sfromR a

  sfromR = AstRaw . cAstSFromR knownShS . unAstRaw
  sfromX = AstRaw . cAstSFromX knownShS . unAstRaw
  xfromS @_ @sh' = AstRaw . cAstXFromS (knownShX @sh') . unAstRaw

  rzip @_ @_ @n (AstRaw a)
   | Refl <- lemRankReplicate (Proxy @n) = AstRaw $ case ftkAst a of
    FTKProduct (FTKR _sh y) (FTKR _ z) ->
      let c = convCmp
                (ConvXR (ftkToSTK (FTKProduct y z)))
                (convCmp
                   (ConvZip (ftkToSTK y) (ftkToSTK z))
                   (ConvT2 ConvRX ConvRX))
      in cAstConvert c a
  runzip @_ @_ @n (AstRaw a)
   | Refl <- lemRankReplicate (Proxy @n) = AstRaw $ case ftkAst a of
    FTKR _sh (FTKProduct y z) ->
      let c = convCmp
                (ConvT2 (ConvXR (ftkToSTK y)) (ConvXR (ftkToSTK z)))
                (convCmp
                   (ConvUnzip (ftkToSTK y) (ftkToSTK z))
                   ConvRX)
      in cAstConvert c a
  szip (AstRaw a) = AstRaw $ case ftkAst a of
    FTKProduct (FTKS _sh y) (FTKS _ z) ->
      let c = convCmp
                ConvXS
                (convCmp
                   (ConvZip (ftkToSTK y) (ftkToSTK z))
                   (ConvT2 ConvSX ConvSX))
      in cAstConvert c a
  sunzip (AstRaw a) = AstRaw $ case ftkAst a of
    FTKS _sh (FTKProduct y z) ->
      let c = convCmp
                (ConvT2 ConvXS ConvXS)
                (convCmp
                   (ConvUnzip (ftkToSTK y) (ftkToSTK z))
                   ConvSX)
      in cAstConvert c a
  xzip (AstRaw a) = AstRaw $ case ftkAst a of
    FTKProduct (FTKX _sh y) (FTKX _ z) ->
      let c = ConvZip (ftkToSTK y) (ftkToSTK z)
      in cAstConvert c a
  xunzip (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX _sh (FTKProduct y z) ->
      let c = ConvUnzip (ftkToSTK y) (ftkToSTK z)
      in cAstConvert c a

  xnestR @sh1 @m @x sh1 (AstRaw a)
    | Refl <- lemRankReplicate (Proxy @m) = AstRaw $
      let c :: TKConversion (TKX2 (sh1 ++ Replicate m Nothing) x)
                            (TKX2 sh1 (TKR2 m x))
          c = convCmp
                (ConvXX (ConvXR (knownSTK @x)))
                (ConvNest @_ @_ @(Replicate m Nothing)
                          (STKX sh1 (knownSTK @x)))
      in cAstConvert c a
  xnestS @_ @_ @x sh1 (AstRaw a) = AstRaw $
    let c = convCmp (ConvXX ConvXS)
                    (ConvNest (STKX sh1 (knownSTK @x)))
    in cAstConvert c a
  xnest @_ @_ @x sh1 (AstRaw a) = AstRaw $
    let c = ConvNest (STKX sh1 (knownSTK @x))
    in cAstConvert c a
  xunNestR (AstRaw a) = AstRaw $
    let c = convCmp ConvUnnest
                    (ConvXX ConvRX)
    in cAstConvert c a
  xunNestS (AstRaw a) = AstRaw $
    let c = convCmp ConvUnnest
                    (ConvXX ConvSX)
    in cAstConvert c a
  xunNest (AstRaw a) = AstRaw $
    let c = ConvUnnest
    in cAstConvert c a

  tpairConv = tpair
  tunpairConv = tunpair

-- All but the last case are shortcuts for common forms.
astConcreteRaw :: FullShapeTK y -> Concrete y -> AstRaw PlainSpan y
astConcreteRaw ftk v = case ftk of
  FTKScalar -> AstRaw $ AstConcreteK $ unConcrete v
  FTKR sh' FTKScalar -> AstRaw $
    withShsFromShR sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      cAstFromS ftk $ AstConcreteS $ unConcrete $ sfromR @_ @sh v
  FTKS _ FTKScalar -> AstRaw $ AstConcreteS $ unConcrete v
  FTKX sh' FTKScalar -> AstRaw $
    withShsFromShX sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      cAstFromS ftk $ AstConcreteS $ unConcrete $ sfromX @_ @sh v
  FTKProduct ftk1 ftk2 -> AstRaw $
    AstPair (unAstRaw $ astConcreteRaw ftk1 (tproject1 v))
            (unAstRaw $ astConcreteRaw ftk2 (tproject2 v))
  _ -> concreteTarget (tkconcrete . unConcrete) (tsconcrete . unConcrete)
                      (\ftk2 a -> AstRaw $ cAstFromS ftk2 $ unAstRaw a)
                      (ftkToSTK ftk) v


-- * AstNoVectorize instances

instance AstSpan s => LetTensor (AstNoVectorize s) where
  ttlet u f = AstNoVectorize
              $ ttlet (unAstNoVectorize u)
                      (unAstNoVectorize . f . AstNoVectorize)
  ttletPrimal u f = AstNoVectorize
                    $ ttletPrimal (unAstNoVectorize u)
                                  (unAstNoVectorize . f . AstNoVectorize)
  ttletPlain u f = AstNoVectorize
                   $ ttletPlain (unAstNoVectorize u)
                                (unAstNoVectorize . f . AstNoVectorize)
  toShare t = toShare $ unAstNoVectorize t

instance AstSpan s => BaseTensor (AstNoVectorize s) where
  -- Ranked ops
  rshape = rshape . unAstNoVectorize
  trsum = AstNoVectorize . trsum . unAstNoVectorize
  trreplicate k = AstNoVectorize . trreplicate k . unAstNoVectorize
  trconcrete = AstNoVectorize . trconcrete
  trfloor = AstNoVectorize . trfloor . unAstNoVectorize
  trfromIntegral = AstNoVectorize . trfromIntegral . unAstNoVectorize
  trcast = AstNoVectorize . trcast . unAstNoVectorize
  trindex v ix =
    AstNoVectorize $ trindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  trindex0 a ix = kfromR $ trindex a ix
  trscatter sh t f =
    AstNoVectorize $ trscatter sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  trgather sh t f =
    AstNoVectorize $ trgather sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
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
  tsreplicate snat sh = AstNoVectorize . tsreplicate snat sh. unAstNoVectorize
  tsconcrete = AstNoVectorize . tsconcrete
  tsfloor = AstNoVectorize . tsfloor . unAstNoVectorize
  tsfromIntegral = AstNoVectorize . tsfromIntegral . unAstNoVectorize
  tscast = AstNoVectorize . tscast . unAstNoVectorize
  tsindex v ix =
    AstNoVectorize $ tsindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  tsindex0 @sh a ix | Refl <- lemAppNil @sh = kfromS $ tsindex a ix
  tsscatter @_ @shm @shn @shp t f =
    AstNoVectorize $ tsscatter @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  tsgather @_ @shm @shn @shp t f =
    AstNoVectorize $ tsgather @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  tsminIndex = AstNoVectorize . tsminIndex . unAstNoVectorize
  tsmaxIndex = AstNoVectorize . tsmaxIndex . unAstNoVectorize
  tsiota = AstNoVectorize tsiota
  tsappend u v =
    AstNoVectorize $ tsappend (unAstNoVectorize u) (unAstNoVectorize v)
  tsslice i n k = AstNoVectorize . tsslice i n k . unAstNoVectorize
  tsreverse = AstNoVectorize . tsreverse . unAstNoVectorize
  tstranspose perm =
    AstNoVectorize . tstranspose perm . unAstNoVectorize
  tsreshape sh = AstNoVectorize . tsreshape sh . unAstNoVectorize
  tsbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstI (Just (0, valueOf @k - 1))
                      -- this introduces new variable names
                  $ unAstNoVectorize . f . AstNoVectorize

  -- Mixed ops
  xshape = xshape . unAstNoVectorize
  txsum = AstNoVectorize . txsum . unAstNoVectorize
  txreplicate snat sh = AstNoVectorize . txreplicate snat sh . unAstNoVectorize
  txconcrete = AstNoVectorize . txconcrete
  txfloor = AstNoVectorize . txfloor . unAstNoVectorize
  txfromIntegral = AstNoVectorize . txfromIntegral . unAstNoVectorize
  txcast = AstNoVectorize . txcast . unAstNoVectorize
  txindex v ix =
    AstNoVectorize $ txindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  txindex0 @sh a ix | Refl <- lemAppNil @sh = kfromX $ txindex a ix
  txscatter @_ @shm @shn @shp sh t f =
    AstNoVectorize $ txscatter @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  txgather @_ @shm @shn @shp sh t f =
    AstNoVectorize $ txgather @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
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
  tpair t1 t2 =
    AstNoVectorize $ tpair (unAstNoVectorize t1) (unAstNoVectorize t2)
  tproject1 t = AstNoVectorize $ tproject1 $ unAstNoVectorize t
  tproject2 t = AstNoVectorize $ tproject2 $ unAstNoVectorize t
  tcond !stk !b !u !v =
    AstNoVectorize $ tcond stk (unAstNoVectorize b)
                               (unAstNoVectorize u) (unAstNoVectorize v)
  tconcrete ftk a = AstNoVectorize $ tconcrete ftk a
  tfromVector k stk =
    AstNoVectorize . tfromVector k stk . V.map unAstNoVectorize
  tmapAccumRDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    AstNoVectorize $ tmapAccumRDer Proxy k accftk bftk eftk f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  tmapAccumLDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    AstNoVectorize $ tmapAccumLDer Proxy k accftk bftk eftk f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  tapply t ll = AstNoVectorize $ tapply t (unAstNoVectorize ll)
  tlambda = tlambda @(AstTensor AstMethodLet s)
  tgrad = tgrad @(AstTensor AstMethodLet s)
  tvjp = tvjp @(AstTensor AstMethodLet s)
  tjvp = tjvp @(AstTensor AstMethodLet s)

  tsum k stk =
    AstNoVectorize . tsum k stk . unAstNoVectorize
  treplicate k stk =
    AstNoVectorize . treplicate k stk . unAstNoVectorize
  tindexBuild k stk u i =
    AstNoVectorize $ tindexBuild k stk (unAstNoVectorize u) (unAstNoVectorize i)

  tprimalPart t = AstNoVectorize $ tprimalPart $ unAstNoVectorize t
  tdualPart stk t = tdualPart stk $ unAstNoVectorize t
  tplainPart t = AstNoVectorize $ tplainPart $ unAstNoVectorize t
  tfromPrimal stk t = AstNoVectorize $ tfromPrimal stk $ unAstNoVectorize t
  tfromDual t = AstNoVectorize $ tfromDual t
  tfromPlain stk t = AstNoVectorize $ tfromPlain stk $ unAstNoVectorize t

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
  tconvert c _astk = AstNoVectorize . astConvert c . unAstNoVectorize

  rfromX = AstNoVectorize . rfromX . unAstNoVectorize
  xfromR = AstNoVectorize . xfromR . unAstNoVectorize

  sfromR = AstNoVectorize . sfromR . unAstNoVectorize
  sfromX = AstNoVectorize . sfromX . unAstNoVectorize
  xfromS = AstNoVectorize . xfromS . unAstNoVectorize

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

instance AstSpan s => LetTensor (AstNoSimplify s) where
  ttlet u f = AstNoSimplify
              $ astLetFunNoSimplify (unAstNoSimplify u)
                                    (unAstNoSimplify . f . AstNoSimplify)
  ttletPrimal u f = AstNoSimplify
                    $ astLetFunNoSimplify (unAstNoSimplify u)
                                          (unAstNoSimplify . f . AstNoSimplify)
  ttletPlain u f = AstNoSimplify
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
    AstNoSimplify $ AstCond (unAstNoSimplify b)
                            (unAstNoSimplify u) (unAstNoSimplify v)
  tdualPart _ t = dualPart $ unAstNoSimplify t
  tfromDual t = AstNoSimplify $ fromDual t

  -- All the following implementations piggy-back on AstRaw implementations.
  -- Ranked ops
  rshape = rshape . wunAstNoSimplify
  trsum = wAstNoSimplify . trsum . wunAstNoSimplify
  trreplicate k = wAstNoSimplify . trreplicate k . wunAstNoSimplify
  trconcrete = wAstNoSimplify . trconcrete
  trfloor = wAstNoSimplify . trfloor . wunAstNoSimplify
  trfromIntegral = wAstNoSimplify . trfromIntegral . wunAstNoSimplify
  trcast = wAstNoSimplify . trcast . wunAstNoSimplify
  trindex v ix =
    wAstNoSimplify $ trindex (wunAstNoSimplify v) (wunAstNoSimplify <$> ix)
  trindex0 a ix = kfromR $ trindex a ix
  trscatter sh t f =
    wAstNoSimplify $ trscatter sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  trgather sh t f =
    wAstNoSimplify $ trgather sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
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
  tsreplicate snat sh = wAstNoSimplify . tsreplicate snat sh . wunAstNoSimplify
  tsconcrete = wAstNoSimplify . tsconcrete
  tsfloor = wAstNoSimplify . tsfloor . wunAstNoSimplify
  tsfromIntegral = wAstNoSimplify . tsfromIntegral . wunAstNoSimplify
  tscast = wAstNoSimplify . tscast . wunAstNoSimplify
  tsindex v ix =
    wAstNoSimplify $ tsindex (wunAstNoSimplify v) (wunAstNoSimplify <$> ix)
  tsindex0 @sh a ix | Refl <- lemAppNil @sh = kfromS $ tsindex a ix
  tsscatter @_ @shm @shn @shp t f =
    wAstNoSimplify $ tsscatter @_ @_ @shm @shn @shp (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  tsgather @_ @shm @shn @shp t f =
    wAstNoSimplify $ tsgather @_ @_ @shm @shn @shp (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  tsminIndex = wAstNoSimplify . tsminIndex . wunAstNoSimplify
  tsmaxIndex = wAstNoSimplify . tsmaxIndex . wunAstNoSimplify
  tsiota = wAstNoSimplify tsiota
  tsappend u v =
    wAstNoSimplify $ tsappend (wunAstNoSimplify u) (wunAstNoSimplify v)
  tsslice i n k = wAstNoSimplify . tsslice i n k . wunAstNoSimplify
  tsreverse = wAstNoSimplify . tsreverse . wunAstNoSimplify
  tstranspose perm =
    wAstNoSimplify . tstranspose perm . wunAstNoSimplify
  tsreshape sh = wAstNoSimplify . tsreshape sh . wunAstNoSimplify

  -- Mixed ops
  xshape = xshape . wunAstNoSimplify
  txsum = wAstNoSimplify . txsum . wunAstNoSimplify
  txreplicate snat sh = wAstNoSimplify . txreplicate snat sh . wunAstNoSimplify
  txconcrete = wAstNoSimplify . txconcrete
  txfloor = wAstNoSimplify . txfloor . wunAstNoSimplify
  txfromIntegral = wAstNoSimplify . txfromIntegral . wunAstNoSimplify
  txcast = wAstNoSimplify . txcast . wunAstNoSimplify
  txindex v ix =
    wAstNoSimplify $ txindex (wunAstNoSimplify v) (wunAstNoSimplify <$> ix)
  txindex0 @sh a ix | Refl <- lemAppNil @sh = kfromX $ txindex a ix
  txscatter @_ @shm @shn @shp sh t f =
    wAstNoSimplify $ txscatter @_ @_ @shm @shn @shp sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  txgather @_ @shm @shn @shp sh t f =
    wAstNoSimplify $ txgather @_ @_ @shm @shn @shp sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
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
  tpair t1 t2 =
    wAstNoSimplify $ tpair (wunAstNoSimplify t1) (wunAstNoSimplify t2)
  tproject1 t = wAstNoSimplify $ tproject1 $ wunAstNoSimplify t
  tproject2 t = wAstNoSimplify $ tproject2 $ wunAstNoSimplify t
  tconcrete ftk a = wAstNoSimplify $ tconcrete ftk a
  tfromVector k stk =
    wAstNoSimplify . tfromVector k stk . V.map wunAstNoSimplify
  tmapAccumRDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    wAstNoSimplify $ tmapAccumRDer Proxy k accftk bftk eftk f df rf
                       (wunAstNoSimplify acc0) (wunAstNoSimplify es)
  tmapAccumLDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    wAstNoSimplify $ tmapAccumLDer Proxy k accftk bftk eftk f df rf
                       (wunAstNoSimplify acc0) (wunAstNoSimplify es)
  tapply t ll = wAstNoSimplify $ tapply t (wunAstNoSimplify ll)
  tlambda = tlambda @(AstRaw s)
  tgrad = tgrad @(AstRaw s)
  tvjp = tvjp @(AstRaw s)
  tjvp = tjvp @(AstRaw s)

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

  tprimalPart t = wAstNoSimplify $ tprimalPart $ wunAstNoSimplify t
  tplainPart t = wAstNoSimplify $ tplainPart $ wunAstNoSimplify t
  tfromPrimal stk t = wAstNoSimplify $ tfromPrimal stk $ wunAstNoSimplify t
  tfromPlain stk t = wAstNoSimplify $ tfromPlain stk $ wunAstNoSimplify t

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
  tconvert c astk = wAstNoSimplify . tconvert c astk . wunAstNoSimplify

  rfromX = wAstNoSimplify . rfromX . wunAstNoSimplify
  xfromR = wAstNoSimplify . xfromR . wunAstNoSimplify

  sfromR = wAstNoSimplify . sfromR . wunAstNoSimplify
  sfromX = wAstNoSimplify . sfromX . wunAstNoSimplify
  xfromS = wAstNoSimplify . xfromS . wunAstNoSimplify

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
