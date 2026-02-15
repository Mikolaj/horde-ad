{-# LANGUAGE CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,12,1,0)
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
#endif
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

import Data.Coerce (Coercible, coerce)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import GHC.TypeLits (OrderingI (..), cmpNat, type (+), type (-), type (<=?))
import System.IO.Unsafe (unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Nested (Replicate, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert
  (ixrFromIxS, ixsFromIxR, ixsFromIxX', withShsFromShR, withShsFromShX)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (Init, fromSNat', snatPlus, unsafeCoerceRefl)
import Data.Array.Nested.Permutation (DropLen, TakeLen)

import HordeAd.Core.Ast
import HordeAd.Core.AstEngine
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

forwardPassByInterpretation
  :: forall x z.
     (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw FullSpan))
  -> AstTensor AstMethodShare FullSpan x
  -> AstVarName '(FullSpan, x)
  -> AstTensor AstMethodLet FullSpan x
  -> ADVal (AstRaw FullSpan) z
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
  -> (AstTensor AstMethodShare FullSpan x
      -> AstVarName '(FullSpan, x)
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw FullSpan) z)
  -> FullShapeTK x
  -> (AstArtifactRev x z, Delta (AstRaw FullSpan) z)
-- Break the inline chain to prevent false positives in inspection testing
-- and protect the unsafePerformIO.
{-# NOINLINE revArtifactFromForwardPass #-}
revArtifactFromForwardPass cotangentHandling
                           forwardPass xftk = unsafePerformIO $ do
  -- IO and bangs and the compound function to fix the numbering of variables
  -- for pretty-printing and prevent sharing the impure values
  -- in tests that reset the impure counters.
  (!astVarPrimal, var, astVar0) <- funToAstRevIO xftk
  -- Evaluate completely after terms constructed, to free memory
  -- before gradientFromDelta allocates new memory and new FFI is started.
  let !(D primalBody delta) = forwardPass astVarPrimal var astVar0
  let zftk = ftkAst $ unAstRaw primalBody
      (!varDt, astDt) = funToAst (adFTK zftk) id
  let oneAtF = treplTarget 1 $ adFTK zftk
      !dt = case cotangentHandling of
        UseIncomingCotangent -> AstRaw astDt
        IgnoreIncomingCotangent -> oneAtF
  let !gradient = gradientFromDelta xftk dt delta
      !unGradient = unshareAstTensor $ unAstRaw gradient
      unPrimal = unshareAstTensor $ unAstRaw primalBody
  return (AstArtifactRev varDt var unGradient unPrimal, delta)

revProduceArtifact
  :: forall x z. TKAllNum (ADTensorKind z)
  => IncomingCotangentHandling
  -> (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw FullSpan))
  -> FullShapeTK x
  -> AstArtifactRev x z
{-# INLINE revProduceArtifact #-}
revProduceArtifact cotangentHandling g envInit xftk =
  fst $ revArtifactFromForwardPass
          cotangentHandling (forwardPassByInterpretation g envInit) xftk

-- These two functions are as above, but the dt must be provided and so,
-- due to technical reasons, the type is less constrained.
revArtifactFromForwardPassDt
  :: forall x z.
     (AstTensor AstMethodShare FullSpan x
      -> AstVarName '(FullSpan, x)
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw FullSpan) z)
  -> FullShapeTK x
  -> (AstArtifactRev x z, Delta (AstRaw FullSpan) z)
-- Break the inline chain to prevent false positives in inspection testing
-- and protect the unsafePerformIO.
{-# NOINLINE revArtifactFromForwardPassDt #-}
revArtifactFromForwardPassDt forwardPass xftk = unsafePerformIO $ do
  -- IO and bangs and the compound function to fix the numbering of variables
  -- for pretty-printing and prevent sharing the impure values
  -- in tests that reset the impure counters.
  (!astVarPrimal, var, astVar0) <- funToAstRevIO xftk
  -- Evaluate completely after terms constructed, to free memory
  -- before gradientFromDelta allocates new memory and new FFI is started.
  let !(D primalBody delta) = forwardPass astVarPrimal var astVar0
  let zftk = ftkAst $ unAstRaw primalBody
      (!varDt, !dt) = funToAst (adFTK zftk) id
  let !gradient = gradientFromDelta xftk (AstRaw dt) delta
      !unGradient = unshareAstTensor $ unAstRaw gradient
      unPrimal = unshareAstTensor $ unAstRaw primalBody
  return (AstArtifactRev varDt var unGradient unPrimal, delta)

revProduceArtifactDt
  :: forall x z.
     (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw FullSpan))
  -> FullShapeTK x
  -> AstArtifactRev x z
{-# INLINE revProduceArtifactDt #-}
revProduceArtifactDt g envInit xftk =
  fst $ revArtifactFromForwardPassDt
          (forwardPassByInterpretation g envInit) xftk

fwdArtifactFromForwardPass
  :: forall x z.
     (AstTensor AstMethodShare FullSpan x
      -> AstVarName '(FullSpan, x)
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw FullSpan) z)
  -> FullShapeTK x
  -> (AstArtifactFwd x z, Delta (AstRaw FullSpan) z)
-- Break the inline chain to prevent false positives in inspection testing
-- and protect the unsafePerformIO.
{-# NOINLINE fwdArtifactFromForwardPass #-}
fwdArtifactFromForwardPass forwardPass xftk = unsafePerformIO $ do
  (!varPrimalD, astVarD, astVarPrimal, var, astVar0) <- funToAstFwdIO xftk
  let !(D primalBody delta) = forwardPass astVarPrimal var astVar0
  let !derivative =
        derivativeFromDelta (Proxy @x) delta (adFTK xftk) (AstRaw astVarD)
      !unDerivative = unshareAstTensor $ unAstRaw derivative
      unPrimal = unshareAstTensor $ unAstRaw primalBody
  return (AstArtifactFwd varPrimalD var unDerivative unPrimal, delta)

fwdProduceArtifact
  :: forall x z.
     (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw FullSpan))
  -> FullShapeTK x
  -> AstArtifactFwd x z
{-# INLINE fwdProduceArtifact #-}
fwdProduceArtifact f envInit xftk =
  fst $ fwdArtifactFromForwardPass
          (forwardPassByInterpretation f envInit) xftk


-- * AstTensor instances

-- | This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast tensor instances are defined, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize
  :: KnownSpan s
  => SNat k -> SingletonTK y
  -> (AstInt AstMethodLet -> AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s (BuildTensorKind k y)
{-# NOINLINE astBuild1Vectorize #-}
astBuild1Vectorize k stk f = unsafePerformIO $ do
  varx <- funToAstIntIO (0, fromSNat' k - 1) f
  build1Vectorize k stk varx

instance KnownSpan s => LetTensor (AstTensor AstMethodLet s) where
  ttlet = astLetFun
  ttletPrimal = astLetFun
  ttletPlain = astLetFun
  toShare t = AstRaw $ AstToShare t
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for FullSpan.
  tunshare =
    case knownSpan @s of
      SFullSpan -> unshareAstTensor . unAstRaw
      _ -> error "tunshare: used not at FullSpan"

-- | The checks and error messages in these functions result in complete
-- shape-checking of the ranked and mixed user code (shaped is already
-- fully checked by the Haskell type system).
--
-- Them methods are listed in ranked, shaped, mixed order to keep
-- similar code transformations together.
instance KnownSpan s => BaseTensor (AstTensor AstMethodLet s) where
  isConcreteInstance = False
  -- Ranked ops
  rshape t = case ftkAst t of
    FTKR sh _ -> sh
  trsum v = withSNat (rwidth v) $ \snat -> astSum snat knownSTK v
  trreplicate k = withSNat k $ \snat -> astReplicate snat knownSTK
  trconcrete a = tconcrete (FTKR (Nested.rshape a) FTKScalar) (Concrete a)
  trfloor @_ @r2 a = case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        astConvUp @(TKS sh r2) (FTKR sh' FTKScalar)
        . fromPlain . astFloorS . astPlainPart
        . astConvDownSFromR sh FTKScalar $ a
  trfromIntegral @_ @r2 a = case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        astConvUp @(TKS sh r2) (FTKR sh' FTKScalar)
        . fromPlain . astFromIntegralS . astPlainPart
        . astConvDownSFromR sh FTKScalar $ a
  trcast @_ @r2 a = case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        astConvUp @(TKS sh r2) (FTKR sh' FTKScalar)
        . astCastS . astConvDownSFromR sh FTKScalar $ a
  trindex @m @n a ix = case ftkAst a of
    FTKR @_ @x shmshn x ->
      withShsFromShR shmshn $ \(sh :: ShS sh) ->
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        astConvUp @(TKS2 (Drop m sh) x) (FTKR (shrDrop @m shmshn) x)
        $ astIndexS @(Take m sh) @(Drop m sh)
                    (shsDrop @m sh) (astConvDownSFromR sh x a)
                    (ixsFromIxR ix)
  trindex0 a ix | SNat <- shrRank (rshape a) =
    kfromR $ trindex a ix
  trscatter @m shp0 t f = case ftkAst t of
    FTKR shmshn0 x ->
      withShsFromShR shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShR shp0 $ \(shp :: ShS shp) ->
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        astConvUp (FTKR (shp0 `shrAppend` shrDrop @m shmshn0) x)
        $ funToVarsIxS (shsTake @m shmshn) $ \vars ix ->
            let !ix2 = ixsFromIxR . f . ixrFromIxS $ ix
            in astScatterS (shsTake @m shmshn)
                           (shsDrop @m shmshn)
                           shp
                           (astConvDownSFromR shmshn x t) (vars, ix2)
            -- this introduces new variable names
  trgather @_ @_ @p shm0 t f = case ftkAst t of
    FTKR shpshn0 x ->
      withShsFromShR shm0 $ \(shm :: ShS shm) ->
      withShsFromShR shpshn0 $ \(shpshn :: ShS shpshn) ->
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop p shpshn :~: shpshn) $
        astConvUp (FTKR (shm0 `shrAppend` shrDrop @p shpshn0) x)
        $ funToVarsIxS shm $ \vars ix ->
            let !ix2 = ixsFromIxR . f . ixrFromIxS $ ix
            in astGatherS shm
                          (shsDrop @p shpshn)
                          (shsTake @p shpshn)
                          (astConvDownSFromR shpshn x t) (vars, ix2)
            -- this introduces new variable names
  -- Depite the warning, the pattern match is exhaustive and if a dummy
  -- pattern is added, GHC 9.14.1 complains about that, in turn.
  trargMin a = case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ _ ->
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astConvUp @(TKS (Init sh) Int) (FTKR (shrInit sh') FTKScalar)
          . fromPlain . AstArgMinS . astPlainPart . astConvDownSFromR sh x $ a
  trargMax a = case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astConvUp @(TKS (Init sh) Int) (FTKR (shrInit sh') FTKScalar)
          . fromPlain . AstArgMaxS . astPlainPart . astConvDownSFromR sh x $ a
  triota @r n =
    withSNat n $ \(SNat @n) ->
      astConvUp (FTKR (n :$: ZSR) FTKScalar)
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
                    astConvUp (FTKR shu' x)
                    $ astAppendS (astConvDownSFromR shu x u)
                                 (astConvDownSFromR shv x v)
                  _ -> error $ "rappend: shapes don't match: "
                               ++ show (restu, restv)
  trslice i n a = case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh -> case sh of
        msnat@(SNat @m) :$$ _ ->
          withSNat i $ \isnat@(SNat @i) -> withSNat n $ \nsnat@(SNat @n) ->
            case cmpNat (snatPlus isnat nsnat) msnat of
              GTI -> error $ "rslice: argument tensor too narrow: "
                             ++ show (i, n, fromSNat' msnat)
              EQI ->
                astConvUp (FTKR sh' x)
                . astSliceS isnat nsnat (SNat @(m - (i + n)))
                . astConvDownSFromR sh x $ a
              LTI ->
                astConvUp (FTKR sh' x)
                . astSliceS isnat nsnat (SNat @(m - (i + n)))
                . astConvDownSFromR sh x $ a
  trreverse a = case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh -> case sh of
        _ :$$ _ ->
          astConvUp (FTKR sh' x)
          . astReverseS . astConvDownSFromR sh x $ a
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
                $ astConvUp (FTKR (shrPermutePrefix permr sh') x)
                  . astTransposeS perm . astConvDownSFromR sh x $ a
          in case (Permutation.permRank perm, shsRank sh) of
            (psnat@SNat, shsnat@SNat) ->
              case cmpNat psnat shsnat of
                GTI -> error $ "rtranspose: rank mismatch: "
                               ++ show (fromSNat' psnat, fromSNat' shsnat)
                EQI -> result
                LTI -> result
  trreshape sh2' a = case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh ->
      withShsFromShR sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl -> astConvUp (FTKR sh2' x)
                       . astReshapeS sh2 . astConvDownSFromR sh x $ a
          _ -> error $ "rreshape: tensor size mismatch: "
                       ++ show ( fromSNat' (shsProduct sh)
                               , fromSNat' (shsProduct sh2) )
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
  tsindex0 @sh a ix | Refl <- lemAppNil @sh =
    withKnownShS (sshape a) $
    kfromS $ tsindex a ix
  tsscatter @shm @shn @shp t f =
    funToVarsIxS knownShS $ \vars ix ->
      let !ix2 = f ix
      in astScatterS (knownShS @shm) (knownShS @shn) (knownShS @shp)
                     t (vars, ix2)
      -- this introduces new variable names
  tsgather @shm @shn @shp t f =
    funToVarsIxS knownShS $ \vars ix ->
      let !ix2 = f ix
      in astGatherS (knownShS @shm) (knownShS @shn) (knownShS @shp)
                    t (vars, ix2)
      -- this introduces new variable names
  tsargMin = fromPlain . AstArgMinS . astPlainPart
  tsargMax = fromPlain . AstArgMaxS . astPlainPart
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
  txfloor @_ @r2 a = case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        astConvUp @(TKS sh r2) (FTKX sh' FTKScalar)
        . fromPlain . astFloorS . astPlainPart
        . astConvDownSFromX sh FTKScalar $ a
  txfromIntegral @_ @r2 a = case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        astConvUp @(TKS sh r2) (FTKX sh' FTKScalar)
        . fromPlain . astFromIntegralS
        . astPlainPart . astConvDownSFromX sh FTKScalar $ a
  txcast @_ @r2 a = case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        astConvUp @(TKS sh r2) (FTKX sh' FTKScalar)
        . astCastS . astConvDownSFromX sh FTKScalar $ a
  txindex @sh1 @sh2 a ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 x | SNat <- ssxRank (knownShX @sh1) ->
      withShsFromShX sh1sh2 $ \(sh :: ShS sh) ->
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) sh1sh2 :~: sh2) $
        withKnownShS (shsTake @(Rank sh1) sh) $
        astConvUp @(TKS2 (Drop (Rank sh1) sh) x)
                  (FTKX (shxDrop @(Rank sh1) sh1sh2) x)
        $ astIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (shsDrop @(Rank sh1) sh)
                    (astConvDownSFromX sh x a)
                    (ixsFromIxX' knownShS ix)
  txindex0 @sh a ix | Refl <- lemAppNil @sh =
    withKnownShX (ssxFromShX $ xshape a) $
    kfromX $ txindex a ix
  txscatter @shm @shn @shp shp0 t f = case ftkAst t of
    FTKX shmshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withShsFromShX shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShX shp0 $ \(shp :: ShS shp2) ->
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        astConvUp (FTKX (shp0 `shxAppend` shxDropSSX @_ @shn
                                                     (knownShX @shm) shmshn0) x)
        $ funToVarsIxS (shsTake @(Rank shm) shmshn) $ \vars ix ->
            let !ix2 = ixsFromIxX' shp
                       . f . ixxCast knownShX . ixxFromIxS $ ix
            in astScatterS (shsTake @(Rank shm) shmshn)
                           (shsDrop @(Rank shm) shmshn)
                           shp
                           (astConvDownSFromX shmshn x t) (vars, ix2)
            -- this introduces new variable names
  txgather @shm @shn @shp shm0 t f = case ftkAst t of
    FTKX shpshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withShsFromShX shm0 $ \(shm :: ShS shm2) ->
      withShsFromShX shpshn0 $ \(shpshn :: ShS shpshn) ->
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        astConvUp (FTKX (shm0 `shxAppend` shxDropSSX @_ @shn
                                                     (knownShX @shp) shpshn0) x)
        $ funToVarsIxS shm $ \vars ix ->
            let !ix2 = ixsFromIxX' (shsTake @(Rank shp) shpshn)
                       . f . ixxCast knownShX . ixxFromIxS $ ix
            in astGatherS shm
                          (shsDrop @(Rank shp) shpshn)
                          (shsTake @(Rank shp) shpshn)
                          (astConvDownSFromX shpshn x t) (vars, ix2)
            -- this introduces new variable names
  txargMin a = case ftkAst a of
    FTKX @sh' sh' x ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astConvUp @(TKS (Init sh) Int) (FTKX (shxInit sh') FTKScalar)
          . fromPlain . AstArgMinS @n @rest
          . astPlainPart . astConvDownSFromX sh x $ a
  txargMax a = case ftkAst a of
    FTKX @sh' sh' x ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astConvUp @(TKS (Init sh) Int) (FTKX (shxInit sh') FTKScalar)
          . fromPlain . AstArgMaxS @n @rest
          . astPlainPart . astConvDownSFromX sh x $ a
  txiota @n @r = astConvUp (FTKX (SKnown (SNat @n) :$% ZSX) FTKScalar)
                 $ fromPlain $ AstIotaS @n @r SNat
  txappend u v = case ftkAst u of
    FTKX (m' :$% shu') x -> case ftkAst v of
      FTKX (n' :$% shv') _ ->
        withSNat (fromSMayNat' m') $ \m ->
        withSNat (fromSMayNat' n') $ \n ->
        withShsFromShX shu' $ \(shu :: ShS shu) ->
        withShsFromShX shv' $ \(shv :: ShS shv) ->
          case shxEqual shu' shv' of
            Just Refl ->
              gcastWith (unsafeCoerceRefl :: shu :~: shv) $
              astConvUp (FTKX (smnAddMaybe m' n' :$% shu') x)
              $ astAppendS (astConvDownSFromX (m :$$ shu) x u)
                           (astConvDownSFromX (n :$$ shv) x v)
            _ -> error $ "xappend: shapes don't match: "
                         ++ show (shu', shv')
  txslice i' n' k' a = case ftkAst a of
    FTKX sh'@(_ :$% sh2') x ->
      withSNat (fromSMayNat' i') $ \i ->
      withSNat (fromSMayNat' n') $ \n ->
      withSNat (fromSMayNat' k') $ \k ->
      withShsFromShX sh' $ \sh@(msnat :$$ _) ->
        case testEquality (snatPlus (snatPlus i n) k) msnat of
          Just Refl ->
            astConvUp (FTKX (n' :$% sh2') x)
            . astSliceS i n k . astConvDownSFromX sh x $ a
          _ -> error $ "xslice: argument tensor has a wrong width: "
                       ++ show ( fromSNat' i, fromSNat' n, fromSNat' k
                               , fromSNat' msnat )
  txreverse a = case ftkAst a of
    FTKX sh' x ->
      withShsFromShX sh' $ \(sh@(_ :$$ _) :: ShS sh) ->
        astConvUp (FTKX sh' x)
        . astReverseS . astConvDownSFromX sh x $ a
  txtranspose perm a = case ftkAst a of
    FTKX sh' x ->
      let sh2' = shxPermutePrefix perm sh'
      in withShsFromShX sh' $ \sh ->
           astConvUp (FTKX sh2' x)
           . astTransposeS perm . astConvDownSFromX sh x $ a
  txreshape sh2' a = case ftkAst a of
    FTKX sh' x ->
      withShsFromShX sh' $ \sh ->
      withShsFromShX sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl ->
            astConvUp (FTKX sh2' x)
            . astReshapeS sh2 . astConvDownSFromX sh x $ a
          _ -> error $ "xreshape: tensor size mismatch: "
                       ++ show ( fromSNat' (shsProduct sh)
                               , fromSNat' (shsProduct sh2) )
  txbuild1 @k @sh @x =
    astBuild1Vectorize (SNat @k) (STKX (knownShX @sh) (knownSTK @x))

  -- Scalar ops
  tkconcrete = fromPlain . AstConcreteK
  tkfloor = fromPlain . astFloorK . astPlainPart
  tkfromIntegral = fromPlain . astFromIntegralK . astPlainPart
  tkcast = astCastK
  tkargMin = fromPlain . AstArgMinK . astPlainPart
  tkargMax = fromPlain . AstArgMaxK . astPlainPart
  tkbuild1 @k = astBuild1Vectorize (SNat @k) STKScalar

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk = ftkAst
  tpair = astPair
  tproject1 = astProject1
  tproject2 = astProject2
  tcond _ !b !u !v = astCond b u v
  tconcrete ftk a = fromPlain $ astConcrete ftk a
  tfromVector = astFromVector
  tmapAccumR proxy !k !accftk !bftk !eftk f acc0 es =
    ttlet (tmapAccumL proxy k accftk bftk eftk f acc0
                      (treverse k (ftkToSTK eftk) es)) $ \ !res ->
      tpair (tproject1 res) (treverse k (ftkToSTK bftk) $ tproject2 res)
  tmapAccumRDer proxy !k !accftk !bftk !eftk f df rf acc0 es =
    ttlet (tmapAccumLDer proxy k accftk bftk eftk f df rf acc0
                         (treverse k (ftkToSTK eftk) es)) $ \ !res ->
      tpair (tproject1 res) (treverse k (ftkToSTK bftk) $ tproject2 res)
  tmapAccumLDer _ !k _ !bftk !eftk f df rf acc0 es =
    astMapAccumLDer k bftk eftk f df rf acc0 es
  tapply = astApply
  tlambda ftk f =
    let (var, ast) = funToAst ftk $ unHFun f
    in AstLambda var ast
  tgrad @_ @r xftk f | Dict0 <- lemTKScalarAllNumAD (Proxy @r) =
    -- We don't have an AST constructor to hold it, so we compute outright.
    --
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    gcastWith (unsafeCoerceRefl
               :: SpanTargetFam (AstTensor AstMethodLet FullSpan) s
                  :~: AstTensor AstMethodLet s) $
    let -- No bangs here, because this goes under lambda and should not be
        -- evaluated too early (which at some point was even incorrect
        -- and triggered error "tunshare: used not at FullSpan"; maybe this
        -- is related to terms getting spans converted when interpreted)
        AstArtifactRev{..} =
          revProduceArtifact
            IgnoreIncomingCotangent (simplifyUserCode . unHFun f) emptyEnv xftk
        -- A new variable is created to give it the right span as opposed
        -- to the fixed FullSpan that artVarDomainRev has.
        (varP, ast) = funToAst xftk $ \ !astP ->
          simplifyUserCode
          $ fromFullSpan (knownSpan @s)
          $ substituteAst (toFullSpan (ftkToSTK xftk) (knownSpan @s) astP)
                          artVarDomainRev
                          artDerivativeRev
    in AstLambda varP ast
  tvjp ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    gcastWith (unsafeCoerceRefl
               :: SpanTargetFam (AstTensor AstMethodLet FullSpan) s
                  :~: AstTensor AstMethodLet s) $
    let AstArtifactRev{..} =
          revProduceArtifactDt
            (simplifyUserCode . unHFun f) emptyEnv ftkx
        ftkz = varNameToFTK artVarDtRev
        ftk2 = FTKProduct ftkz ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          simplifyUserCode
          $ fromFullSpan (knownSpan @s)
          $ substituteAst
              (toFullSpan (ftkToSTK ftkx) (knownSpan @s) (astProject2 astP))
              artVarDomainRev
          $ substituteAst
              (toFullSpan (ftkToSTK ftkz) (knownSpan @s) (astProject1 astP))
              artVarDtRev
              artDerivativeRev
    in AstLambda varP ast
  tjvp ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    gcastWith (unsafeCoerceRefl
               :: SpanTargetFam (AstTensor AstMethodLet FullSpan) s
                  :~: AstTensor AstMethodLet s) $
    let AstArtifactFwd{..} =
          fwdProduceArtifact (simplifyUserCode . unHFun f) emptyEnv ftkx
        ftk2 = FTKProduct (adFTK ftkx) ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          simplifyUserCode
          $ fromFullSpan (knownSpan @s)
          $ substituteAst
              (toFullSpan (ftkToSTK ftkx) (knownSpan @s) (astProject2 astP))
              artVarDomainFwd
          $ substituteAst
              (toFullSpan (ftkToSTK (adFTK ftkx)) (knownSpan @s)
                          (astProject1 astP))
              artVarDsFwd
              artDerivativeFwd
    in AstLambda varP ast

  {-# INLINE tsum #-}
  tsum snat@SNat stk u = case stk of
    STKScalar -> kfromS $ tssum u
    STKR SNat x | Dict <- lemKnownSTK x -> trsum u
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ tssum u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ txsum u
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (tsum snat stk1 (tproject1 u3))
              (tsum snat stk2 (tproject2 u3))
  {-# INLINE treplicate #-}
  treplicate snat@SNat stk u = case stk of
    STKScalar -> tsreplicate snat ZSS $ sfromK u
    STKR SNat x | Dict <- lemKnownSTK x -> trreplicate (fromSNat' snat) u
    STKS sh x | Dict <- lemKnownSTK x -> tsreplicate snat sh u
    STKX sh x | Dict <- lemKnownSTK x -> txreplicate snat sh u
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (treplicate snat stk1 (tproject1 u3))
              (treplicate snat stk2 (tproject2 u3))
  {-# INLINE treverse #-}
  treverse snat stk u = case stk of
    STKScalar -> tsreverse u
    STKR _ x | Dict <- lemKnownSTK x -> trreverse u
    STKS _ x | Dict <- lemKnownSTK x -> tsreverse u
    STKX _ x | Dict <- lemKnownSTK x -> txreverse u
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (treverse snat stk1 (tproject1 u3))
              (treverse snat stk2 (tproject2 u3))
  {-# INLINE tindexBuild #-}
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

  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target


-- * AstRaw instances

fmapAstRaw :: Coercible (f (AstTensor AstMethodShare s y)) (f (AstRaw s y))
           => f (AstTensor AstMethodShare s y) -> f (AstRaw s y)
fmapAstRaw = coerce

fmapUnAstRaw :: Coercible (f (AstRaw s y)) (f (AstTensor AstMethodShare s y))
             => f (AstRaw s y) -> f (AstTensor AstMethodShare s y)
fmapUnAstRaw = coerce

instance KnownSpan s => LetTensor (AstRaw s) where
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

instance KnownSpan s => ShareTensor (AstRaw s) where
  tshare t = AstRaw $ astShareNoSimplify $ unAstRaw t
  tunpair (AstRaw (AstPair t1 t2)) = (AstRaw t1, AstRaw t2)
  tunpair t = let tShared = tshare t
              in (tproject1 tShared, tproject2 tShared)

instance KnownSpan s => BaseTensor (AstRaw s) where
  isConcreteInstance = False
  -- Ranked ops
  rshape t = case ftkAst $ unAstRaw t of
    FTKR sh _ -> sh
  trsum v = withSNat (rwidth v) $ \snat ->
              AstRaw . AstSum snat knownSTK . unAstRaw $ v
  trreplicate k = withSNat k $ \snat ->
    AstRaw . AstReplicate snat knownSTK . unAstRaw
  trconcrete a = tconcrete (FTKR (Nested.rshape a) FTKScalar) (Concrete a)
  trfloor (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        cAstConvUpRFromS sh STKScalar
        . fromPlain . AstFloorS . plainPart
        . cAstConvDownSFromR sh FTKScalar $ a
  trfromIntegral (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        cAstConvUpRFromS sh STKScalar
        . fromPlain . AstFromIntegralS . plainPart
        . cAstConvDownSFromR sh FTKScalar $ a
  trcast (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' FTKScalar ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        cAstConvUpRFromS sh STKScalar
        . AstCastS . cAstConvDownSFromR sh FTKScalar $ a
  trindex @m @n (AstRaw a) ix = AstRaw $ case ftkAst a of
    FTKR shmshn x ->
      withShsFromShR shmshn $ \(sh :: ShS sh) ->
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        cAstConvUpRFromS (shsDrop @m sh) (ftkToSTK x)
        $ AstIndexS @(Take m sh) @(Drop m sh)
                    (shsDrop @m sh) (cAstConvDownSFromR sh x a)
                    (ixsFromIxR (fmapUnAstRaw ix))
  trindex0 a ix | SNat <- shrRank (rshape a) =
    kfromR $ trindex a ix
  trscatter @m @n shp0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR shmshn0 x ->
      withShsFromShR shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShR shp0 $ \(shp :: ShS shp) ->
        gcastWith (unsafeCoerceRefl :: Rank (Take m shmshn) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m shmshn) :~: n) $
        gcastWith (unsafeCoerceRefl
                   :: Take m shmshn ++ Drop m shmshn :~: shmshn) $
        gcastWith (unsafeCoerceRefl
                   :: Rank (shp ++ Drop m shmshn)
                      :~: Rank shp + Rank (Drop m shmshn)) $
        cAstConvUpRFromS (shp `shsAppend` shsDrop @m shmshn) (ftkToSTK x)
        $ funToVarsIxS (shsTake @m shmshn) $ \vars ix ->
            let !ix2 = fmapUnAstRaw . ixsFromIxR
                       . f . ixrFromIxS . fmapAstRaw $ ix
            in AstScatterS (shsTake @m shmshn)
                           (shsDrop @m shmshn)
                           shp
                           (cAstConvDownSFromR shmshn x t) (vars, ix2)
            -- this introduces new variable names
  trgather @_ @n @p shm0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKR shpshn0 x ->
      withShsFromShR shm0 $ \(shm :: ShS shm) ->
      withShsFromShR shpshn0 $ \(shpshn :: ShS shpshn) ->
        gcastWith (unsafeCoerceRefl :: Rank (Take p shpshn) :~: p) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop p shpshn) :~: n) $
        gcastWith (unsafeCoerceRefl
                   :: Take p shpshn ++ Drop p shpshn :~: shpshn) $
        gcastWith (unsafeCoerceRefl
                   :: Rank (shm ++ Drop p shpshn)
                      :~: Rank shm + Rank (Drop p shpshn)) $
        cAstConvUpRFromS (shm `shsAppend` shsDrop @p shpshn) (ftkToSTK x)
        $ funToVarsIxS shm $ \vars ix ->
            let !ix2 = fmapUnAstRaw . ixsFromIxR
                       . f . ixrFromIxS . fmapAstRaw $ ix
            in AstGatherS shm
                          (shsDrop @p shpshn)
                          (shsTake @p shpshn)
                          (cAstConvDownSFromR shpshn x t) (vars, ix2)
            -- this introduces new variable names
  trargMin (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ _ ->
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          cAstConvUpRFromS (shsInit sh) STKScalar
          . fromPlain . AstArgMinS . plainPart . cAstConvDownSFromR sh x $ a
  trargMax (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          cAstConvUpRFromS (shsInit sh) STKScalar
          . fromPlain . AstArgMaxS . plainPart . cAstConvDownSFromR sh x $ a
  triota @r n =
    AstRaw
    $ withSNat n $ \snat@(SNat @n) ->
        cAstConvUpRFromS (snat :$$ ZSS) STKScalar
        $ fromPlain $ AstIotaS @n @r SNat
  trappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKR shu' x -> case ftkAst v of
      FTKR shv' _ ->
        withShsFromShR shu' $ \shu -> case shu of
          usnat :$$ restu ->
            withShsFromShR shv' $ \shv -> case shv of
              vsnat :$$ restv ->
                case testEquality restu restv of
                  Just Refl ->
                    cAstConvUpRFromS (snatPlus usnat vsnat :$$ restu)
                                     (ftkToSTK x)
                    $ AstAppendS (cAstConvDownSFromR shu x u)
                                 (cAstConvDownSFromR shv x v)
                  _ -> error $ "rappend: shapes don't match: "
                               ++ show (restu, restv)
  trslice i n (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh@(_ :$$ shRest) -> case sh of
        msnat@(SNat @m) :$$ _ ->
          withSNat i $ \isnat@(SNat @i) -> withSNat n $ \nsnat@(SNat @n) ->
            case cmpNat (snatPlus isnat nsnat) msnat of
              GTI -> error $ "rslice: argument tensor too narrow: "
                             ++ show (i, n, fromSNat' msnat)
              EQI ->
                cAstConvUpRFromS (nsnat :$$ shRest) (ftkToSTK x)
                . AstSliceS isnat nsnat (SNat @(m - (i + n)))
                . cAstConvDownSFromR sh x $ a
              LTI ->
                cAstConvUpRFromS (nsnat :$$ shRest) (ftkToSTK x)
                . AstSliceS isnat nsnat (SNat @(m - (i + n)))
                . cAstConvDownSFromR sh x $ a
  trreverse (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh -> case sh of
        _ :$$ _ ->
          cAstConvUpRFromS sh (ftkToSTK x)
          . AstReverseS . cAstConvDownSFromR sh x $ a
  trtranspose @n @r permr (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        Permutation.permFromListCont permr $ \(perm :: Permutation.Perm perm) ->
          let result :: AstTensor AstMethodShare s (TKR2 n r)
              result =
                -- A noble lie, verified down below.
                gcastWith (unsafeCoerceRefl
                           :: (Rank perm <=? Rank sh) :~: True) $
                gcastWith (unsafeCoerceRefl
                           :: Rank (Permutation.PermutePrefix perm sh)
                              :~: Rank sh) $
                gcastWith (unsafeCoerceRefl
                           :: Permutation.Permute perm (TakeLen perm sh)
                              ++ DropLen perm sh
                              :~: sh) $
                fromMaybe (error "rtranspose: impossible non-permutation")
                $ Permutation.permCheckPermutation perm
                $ cAstConvUpRFromS sh (ftkToSTK x)
                  . AstTransposeS perm . cAstConvDownSFromR sh x $ a
          in case (Permutation.permRank perm, shsRank sh) of
            (psnat@SNat, shsnat@SNat) ->
              case cmpNat psnat shsnat of
                GTI -> error $ "rtranspose: rank mismatch: "
                               ++ show (fromSNat' psnat, fromSNat' shsnat)
                EQI -> result
                LTI -> result
  trreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withShsFromShR sh' $ \sh ->
      withShsFromShR sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl -> cAstConvUpRFromS sh2 (ftkToSTK x)
                       . AstReshapeS sh2 . cAstConvDownSFromR sh x $ a
          _ -> error $ "rreshape: tensor size mismatch: "
                       ++ show ( fromSNat' (shsProduct sh)
                               , fromSNat' (shsProduct sh2) )
  trbuild1 k f = withSNat k $ \snat ->
    AstRaw $ AstBuild1 snat knownSTK
    $ funToAstInt (0, k - 1)
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
  tsindex v ix = AstRaw $ AstIndexS knownShS (unAstRaw v) (fmapUnAstRaw ix)
  tsindex0 @sh a ix | Refl <- lemAppNil @sh =
    withKnownShS (sshape a) $
    kfromS $ tsindex a ix
  tsscatter @shm @shn @shp t f = AstRaw $
    funToVarsIxS knownShS $ \vars ix ->
      let !ix2 = fmapUnAstRaw . f . fmapAstRaw $ ix
      in AstScatterS (knownShS @shm) (knownShS @shn) (knownShS @shp)
                     (unAstRaw t) (vars, ix2)
      -- this introduces new variable names
  tsgather @shm @shn @shp t f = AstRaw $
    funToVarsIxS knownShS $ \vars ix ->
      let !ix2 = fmapUnAstRaw . f . fmapAstRaw $ ix
      in AstGatherS (knownShS @shm) (knownShS @shn) (knownShS @shp)
                    (unAstRaw t) (vars, ix2)
  tsargMin = AstRaw . fromPlain . AstArgMinS . plainPart . unAstRaw
  tsargMax = AstRaw . fromPlain . AstArgMaxS . plainPart . unAstRaw
  tsiota = AstRaw . fromPlain $ AstIotaS SNat
  tsappend u v = AstRaw $ AstAppendS (unAstRaw u) (unAstRaw v)
  tsslice i n k = AstRaw . AstSliceS i n k . unAstRaw
  tsreverse = AstRaw . AstReverseS . unAstRaw
  tstranspose perm = AstRaw . AstTransposeS perm . unAstRaw
  tsreshape sh = AstRaw . AstReshapeS sh . unAstRaw
  tsbuild1 @k f = AstRaw $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstInt (0, valueOf @k - 1)
                      -- this introduces new variable names
                  $ unAstRaw . f . AstRaw

  -- Mixed ops
  xshape t = case ftkAst $ unAstRaw t of
    FTKX sh _ -> sh
  txsum = AstRaw . AstSum SNat knownSTK . unAstRaw
  txreplicate snat sh = AstRaw . AstReplicate snat (STKX sh knownSTK) . unAstRaw
  txconcrete a = tconcrete (FTKX (Nested.mshape a) FTKScalar) (Concrete a)
  txfloor (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        cAstConvUpXFromS sh' FTKScalar
        . fromPlain . AstFloorS . plainPart
        . cAstConvDownSFromX sh FTKScalar $ a
  txfromIntegral (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        cAstConvUpXFromS sh' FTKScalar
        . fromPlain . AstFromIntegralS
        . plainPart . cAstConvDownSFromX sh FTKScalar $ a
  txcast (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' FTKScalar ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        cAstConvUpXFromS sh' FTKScalar
        . AstCastS . cAstConvDownSFromX sh FTKScalar $ a
  txindex @sh1 @sh2 (AstRaw a) ix = case ftkAst a of
    FTKX @sh1sh2 sh1sh2 x | SNat <- ssxRank (knownShX @sh1) ->
      withShsFromShX sh1sh2 $ \(sh :: ShS sh) ->
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        gcastWith (unsafeCoerceRefl :: Drop (Rank sh1) sh1sh2 :~: sh2) $
        withKnownShS (shsTake @(Rank sh1) sh) $
        AstRaw $ cAstConvUpXFromS (shxDrop @(Rank sh1) sh1sh2) x
        $ AstIndexS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                    (shsDrop @(Rank sh1) sh)
                    (cAstConvDownSFromX sh x a)
                    (ixsFromIxX' knownShS (fmapUnAstRaw ix))
  txindex0 @sh a ix | Refl <- lemAppNil @sh =
    withKnownShX (ssxFromShX $ xshape a) $
    kfromX $ txindex a ix
  txscatter @shm @shn @shp shp0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shmshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withShsFromShX shmshn0 $ \(shmshn :: ShS shmshn) ->
      withShsFromShX shp0 $ \(shp :: ShS shp2) ->
        gcastWith (unsafeCoerceRefl
                   :: Rank (shp2 ++ Drop (Rank shm) shmshn)
                      :~: Rank (shp ++ shn)) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shm) shmshn ++ Drop (Rank shm) shmshn
                      :~: shmshn) $
        cAstConvUpXFromS (shp0 `shxAppend` shxDropSSX @_ @shn
                                             (knownShX @shm) shmshn0) x
        $ funToVarsIxS (shsTake @(Rank shm) shmshn) $ \vars ix ->
            let !ix2 = fmapUnAstRaw . ixsFromIxX' shp
                       . f . ixxCast knownShX . ixxFromIxS . fmapAstRaw $ ix
            in AstScatterS (shsTake @(Rank shm) shmshn)
                           (shsDrop @(Rank shm) shmshn)
                           shp
                           (cAstConvDownSFromX shmshn x t) (vars, ix2)
            -- this introduces new variable names
  txgather @shm @shn @shp shm0 (AstRaw t) f = AstRaw $ case ftkAst t of
    FTKX shpshn0 x | SNat <- ssxRank (knownShX @shm)
                   , SNat <- ssxRank (knownShX @shp) ->
      withShsFromShX shm0 $ \(shm :: ShS shm2) ->
      withShsFromShX shpshn0 $ \(shpshn :: ShS shpshn) ->
        gcastWith (unsafeCoerceRefl
                   :: Rank (shm2 ++ Drop (Rank shp) shpshn)
                      :~: Rank (shm ++ shn)) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank shp) shpshn ++ Drop (Rank shp) shpshn
                      :~: shpshn) $
        cAstConvUpXFromS (shm0 `shxAppend` shxDropSSX @_ @shn
                                             (knownShX @shp) shpshn0) x
        $ funToVarsIxS shm $ \vars ix ->
            let !ix2 = fmapUnAstRaw . ixsFromIxX' (shsTake @(Rank shp) shpshn)
                       . f . ixxCast knownShX . ixxFromIxS . fmapAstRaw $ ix
            in AstGatherS shm
                          (shsDrop @(Rank shp) shpshn)
                          (shsTake @(Rank shp) shpshn)
                          (cAstConvDownSFromX shpshn x t) (vars, ix2)
            -- this introduces new variable names
  txargMin (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' x ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          cAstConvUpXFromS (shxInit sh') FTKScalar
          . fromPlain . AstArgMinS @n @rest
          . plainPart . cAstConvDownSFromX sh x $ a
  txargMax (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' x ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          cAstConvUpXFromS (shxInit sh') FTKScalar
          . fromPlain . AstArgMaxS @n @rest
          . plainPart . cAstConvDownSFromX sh x $ a
  txiota @n @r = AstRaw $ cAstConvUpXFromS (SKnown (SNat @n) :$% ZSX) FTKScalar
                 $ fromPlain $ AstIotaS @n @r SNat
  txappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKX (m' :$% shu') x -> case ftkAst v of
      FTKX (n' :$% shv') _ ->
        withSNat (fromSMayNat' m') $ \m ->
        withSNat (fromSMayNat' n') $ \n ->
        withShsFromShX shu' $ \(shu :: ShS shu) ->
        withShsFromShX shv' $ \(shv :: ShS shv) ->
          case shxEqual shu' shv' of
            Just Refl ->
              gcastWith (unsafeCoerceRefl :: shu :~: shv) $
              cAstConvUpXFromS (smnAddMaybe m' n' :$% shu') x
              $ AstAppendS (cAstConvDownSFromX (m :$$ shu) x u)
                           (cAstConvDownSFromX (n :$$ shv) x v)
            _ -> error $ "xappend: shapes don't match: "
                         ++ show (shu', shv')
  txslice i' n' k' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh'@(_ :$% sh2') x ->
      withSNat (fromSMayNat' i') $ \i ->
      withSNat (fromSMayNat' n') $ \n ->
      withSNat (fromSMayNat' k') $ \k ->
      withShsFromShX sh' $ \sh@(msnat :$$ _) ->
        case testEquality (snatPlus (snatPlus i n) k) msnat of
          Just Refl ->
            cAstConvUpXFromS (n' :$% sh2') x
            . AstSliceS i n k . cAstConvDownSFromX sh x $ a
          _ -> error $ "xslice: argument tensor has a wrong width: "
                       ++ show ( fromSNat' i, fromSNat' n, fromSNat' k
                               , fromSNat' msnat )
  txreverse (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      withShsFromShX sh' $ \(sh@(_ :$$ _) :: ShS sh) ->
        cAstConvUpXFromS sh' x
        . AstReverseS . cAstConvDownSFromX sh x $ a
  txtranspose @perm perm (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' x ->
      let sh2' = shxPermutePrefix perm sh'
      in withShsFromShX sh' $ \(sh :: ShS sh) ->
           gcastWith (unsafeCoerceRefl
                      :: Rank (Permutation.PermutePrefix perm sh')
                         :~: Rank sh') $
           gcastWith (unsafeCoerceRefl
                      :: Rank (Permutation.PermutePrefix perm sh)
                         :~: Rank sh) $
           cAstConvUpXFromS sh2' x
           . AstTransposeS perm
           . cAstConvDownSFromX sh x $ a
  txreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      withShsFromShX sh' $ \sh ->
      withShsFromShX sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl ->
            cAstConvUpXFromS sh2' x
            . AstReshapeS sh2 . cAstConvDownSFromX sh x $ a
          _ -> error $ "xreshape: tensor size mismatch: "
                       ++ show ( fromSNat' (shsProduct sh)
                               , fromSNat' (shsProduct sh2) )
  txbuild1 @k f = AstRaw $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstInt (0, valueOf @k - 1)
                      -- this introduces new variable names
                  $ unAstRaw . f . AstRaw

  -- Scalar ops
  tkconcrete = AstRaw . fromPlain . AstConcreteK
  tkfloor = AstRaw . fromPlain . AstFloorK . plainPart . unAstRaw
  tkfromIntegral = AstRaw . fromPlain . AstFromIntegralK
                   . plainPart . unAstRaw
  tkcast = AstRaw . AstCastK . unAstRaw
  tkargMin = AstRaw . fromPlain . AstArgMinK . plainPart . unAstRaw
  tkargMax = AstRaw . fromPlain . AstArgMaxK . plainPart . unAstRaw
  tkbuild1 @k f = AstRaw $ AstBuild1 (SNat @k) STKScalar
                  $ funToAstInt (0, valueOf @k - 1)
                      -- this introduces new variable names
                  $ unAstRaw . f . AstRaw

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk = ftkAst . unAstRaw
  tpair t1 t2 = AstRaw $ AstPair (unAstRaw t1) (unAstRaw t2)
  tproject1 t = AstRaw $ AstProject1 $ unAstRaw t
  tproject2 t = AstRaw $ AstProject2 $ unAstRaw t
  tcond _ !b !u !v = AstRaw $ AstCond (unAstRaw b) (unAstRaw u) (unAstRaw v)
  tconcrete ftk a = AstRaw $ fromPlain $ unAstRaw $ astConcreteRaw ftk a
  tfromVector k stk =
    AstRaw . AstFromVector k stk . fmapUnAstRaw
  tmapAccumLDer _ !k _ !bftk !eftk f df rf acc0 es =
    AstRaw $ AstMapAccumLDer k bftk eftk f df rf (unAstRaw acc0) (unAstRaw es)
  tapply f t = AstRaw $ AstApply f (unAstRaw t)
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

  taddTarget = addTarget
  tmultTarget = multTarget
  tsum0Target = sum0Target
  tdot0Target = dot0Target

instance KnownSpan s => ConvertTensor (AstRaw s) where
  tconvert c _astk = AstRaw . cAstConvert c . unAstRaw

  -- These two are somewhat faster than their default implementations.
  kfromS = AstRaw . cAstConvDownKFromS . unAstRaw
  sfromK = AstRaw . cAstConvUpSFromK . unAstRaw

  rfromS (AstRaw a) = AstRaw $ cAstConvUpRFromS knownShS knownSTK a
  rfromX (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        cAstConvUpRFromS sh (ftkToSTK x) $ cAstConvDownSFromX sh x a
  xfromR (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR shr x ->
      withShsFromShR shr $ \(sh :: ShS sh) ->
        cAstConvUpXFromS (shCastSX knownShX sh) x
        $ cAstConvDownSFromR sh x a
  sfromR (AstRaw t) = AstRaw $ case ftkAst t of
    FTKR _ x -> cAstConvDownSFromR knownShS x t
  sfromX (AstRaw t) = AstRaw $ case ftkAst t of
    FTKX _ x -> cAstConvDownSFromX knownShS x t
  xfromS (AstRaw t) = AstRaw $ case ftkAst t of
    FTKS sh x -> cAstConvUpXFromS (shCastSX knownShX sh) x t

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
  FTKR ZSR FTKScalar ->
    AstRaw $ AstConvert (ConvCmp (ConvXR STKScalar) (Conv0X STKScalar))
    $ AstConcreteK $ Nested.runScalar $ unConcrete v
  FTKR sh' FTKScalar -> AstRaw $
    withShsFromShR sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      cAstConvUpRFromS sh STKScalar
      $ AstConcreteS $ unConcrete $ sfromR @_ @sh v
  FTKS ZSS FTKScalar ->
    AstRaw $ AstConvert (ConvCmp ConvXS (Conv0X STKScalar))
    $ AstConcreteK $ Nested.sunScalar $ unConcrete v
  FTKS _ FTKScalar -> AstRaw $ AstConcreteS $ unConcrete v
  FTKX ZSX FTKScalar ->
    AstRaw $ AstConvert (Conv0X STKScalar)
    $ AstConcreteK $ Nested.munScalar $ unConcrete v
  FTKX sh' FTKScalar -> AstRaw $
    withShsFromShX sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      cAstConvUpXFromS sh' FTKScalar
      $ AstConcreteS $ unConcrete $ sfromX @_ @sh v
  FTKProduct ftk1 ftk2 -> AstRaw $
    AstPair (unAstRaw $ astConcreteRaw ftk1 (tproject1 v))
            (unAstRaw $ astConcreteRaw ftk2 (tproject2 v))
  _ -> concreteTarget
         (tkconcrete . unConcrete) (tsconcrete . unConcrete)
         (\sh (AstRaw t) -> AstRaw $ cAstConvUpRFromS sh STKScalar t)
         (\sh' (AstRaw t) -> AstRaw $ cAstConvUpXFromS sh' FTKScalar t)
         (ftkToSTK ftk) v


-- * AstNoVectorize instances

fmapAstNoVectorize
  :: Coercible (f (AstTensor AstMethodLet s y)) (f (AstNoVectorize s y))
  => f (AstTensor AstMethodLet s y) -> f (AstNoVectorize s y)
fmapAstNoVectorize = coerce

fmapUnAstNoVectorize
  :: Coercible (f (AstNoVectorize s y)) (f (AstTensor AstMethodLet s y))
  => f (AstNoVectorize s y) -> f (AstTensor AstMethodLet s y)
fmapUnAstNoVectorize = coerce

instance KnownSpan s => LetTensor (AstNoVectorize s) where
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

instance KnownSpan s => BaseTensor (AstNoVectorize s) where
  isConcreteInstance = False
  -- Ranked ops
  rshape = rshape . unAstNoVectorize
  trsum = AstNoVectorize . trsum . unAstNoVectorize
  trreplicate k = AstNoVectorize . trreplicate k . unAstNoVectorize
  trconcrete = AstNoVectorize . trconcrete
  trfloor = AstNoVectorize . trfloor . unAstNoVectorize
  trfromIntegral = AstNoVectorize . trfromIntegral . unAstNoVectorize
  trcast = AstNoVectorize . trcast . unAstNoVectorize
  trindex v ix =
    AstNoVectorize $ trindex (unAstNoVectorize v) (fmapUnAstNoVectorize ix)
  trindex0 a ix | SNat <- shrRank (rshape a) =
    kfromR $ trindex a ix
  trscatter sh t f =
    AstNoVectorize $ trscatter sh (unAstNoVectorize t)
                   $ fmapUnAstNoVectorize . f . fmapAstNoVectorize
  trgather sh t f =
    AstNoVectorize $ trgather sh (unAstNoVectorize t)
                   $ fmapUnAstNoVectorize . f . fmapAstNoVectorize
  trargMin = AstNoVectorize . trargMin . unAstNoVectorize
  trargMax = AstNoVectorize . trargMax . unAstNoVectorize
  triota = AstNoVectorize . triota
  trappend u v =
    AstNoVectorize $ trappend (unAstNoVectorize u) (unAstNoVectorize v)
  trslice i n = AstNoVectorize . trslice i n . unAstNoVectorize
  trreverse = AstNoVectorize . trreverse . unAstNoVectorize
  trtranspose perm = AstNoVectorize . trtranspose perm . unAstNoVectorize
  trreshape sh = AstNoVectorize . trreshape sh . unAstNoVectorize
  trbuild1 k f = withSNat k $ \snat ->
    AstNoVectorize $ AstBuild1 snat knownSTK
    $ funToAstInt (0, k - 1)
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
    AstNoVectorize $ tsindex (unAstNoVectorize v) (fmapUnAstNoVectorize ix)
  tsindex0 @sh a ix | Refl <- lemAppNil @sh =
    withKnownShS (sshape a) $
    kfromS $ tsindex a ix
  tsscatter @_ @shm @shn @shp t f =
    AstNoVectorize $ tsscatter @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmapUnAstNoVectorize . f . fmapAstNoVectorize
  tsgather @_ @shm @shn @shp t f =
    AstNoVectorize $ tsgather @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmapUnAstNoVectorize . f . fmapAstNoVectorize
  tsargMin = AstNoVectorize . tsargMin . unAstNoVectorize
  tsargMax = AstNoVectorize . tsargMax . unAstNoVectorize
  tsiota = AstNoVectorize tsiota
  tsappend u v =
    AstNoVectorize $ tsappend (unAstNoVectorize u) (unAstNoVectorize v)
  tsslice i n k = AstNoVectorize . tsslice i n k . unAstNoVectorize
  tsreverse = AstNoVectorize . tsreverse . unAstNoVectorize
  tstranspose perm =
    AstNoVectorize . tstranspose perm . unAstNoVectorize
  tsreshape sh = AstNoVectorize . tsreshape sh . unAstNoVectorize
  tsbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstInt (0, valueOf @k - 1)
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
    AstNoVectorize $ txindex (unAstNoVectorize v) (fmapUnAstNoVectorize ix)
  txindex0 @sh a ix | Refl <- lemAppNil @sh =
    withKnownShX (ssxFromShX $ xshape a) $
    kfromX $ txindex a ix
  txscatter @_ @shm @shn @shp sh t f =
    AstNoVectorize $ txscatter @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmapUnAstNoVectorize . f . fmapAstNoVectorize
  txgather @_ @shm @shn @shp sh t f =
    AstNoVectorize $ txgather @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmapUnAstNoVectorize . f . fmapAstNoVectorize
  txargMin = AstNoVectorize . txargMin . unAstNoVectorize
  txargMax = AstNoVectorize . txargMax . unAstNoVectorize
  txiota @n = AstNoVectorize $ txiota @_ @n
  txappend u v =
    AstNoVectorize $ txappend (unAstNoVectorize u) (unAstNoVectorize v)
  txslice i n k = AstNoVectorize . txslice i n k . unAstNoVectorize
  txreverse = AstNoVectorize . txreverse . unAstNoVectorize
  txtranspose perm = AstNoVectorize . txtranspose perm . unAstNoVectorize
  txreshape sh = AstNoVectorize . txreshape sh . unAstNoVectorize
  txbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k) knownSTK
                  $ funToAstInt (0, valueOf @k - 1)
                      -- this introduces new variable names
                  $ unAstNoVectorize . f . AstNoVectorize

  -- Scalar ops
  tkconcrete = AstNoVectorize . tkconcrete
  tkfloor = AstNoVectorize . tkfloor . unAstNoVectorize
  tkfromIntegral = AstNoVectorize . tkfromIntegral . unAstNoVectorize
  tkcast = AstNoVectorize . tkcast . unAstNoVectorize
  tkargMin = AstNoVectorize . tkargMin . unAstNoVectorize
  tkargMax = AstNoVectorize . tkargMax . unAstNoVectorize
  tkbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k) STKScalar
                  $ funToAstInt (0, valueOf @k - 1)
                      -- this introduces new variable names
                  $ unAstNoVectorize . f . AstNoVectorize

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
    AstNoVectorize . tfromVector k stk . fmapUnAstNoVectorize
  tmapAccumR _ !k !accftk !bftk !eftk f acc0 es =
    AstNoVectorize $ tmapAccumR Proxy k accftk bftk eftk f
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  tmapAccumRDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    AstNoVectorize $ tmapAccumRDer Proxy k accftk bftk eftk f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  tmapAccumLDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    AstNoVectorize $ tmapAccumLDer Proxy k accftk bftk eftk f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  tapply f t = AstNoVectorize $ tapply f (unAstNoVectorize t)
  tlambda = tlambda @(AstTensor AstMethodLet s)
  tgrad = tgrad @(AstTensor AstMethodLet s)
  tvjp = tvjp @(AstTensor AstMethodLet s)
  tjvp = tjvp @(AstTensor AstMethodLet s)

  tsum k stk =
    AstNoVectorize . tsum k stk . unAstNoVectorize
  treplicate k stk =
    AstNoVectorize . treplicate k stk . unAstNoVectorize
  treverse k stk =
    AstNoVectorize . treverse k stk . unAstNoVectorize
  tindexBuild k stk u i =
    AstNoVectorize $ tindexBuild k stk (unAstNoVectorize u) (unAstNoVectorize i)

  tprimalPart t = AstNoVectorize $ tprimalPart $ unAstNoVectorize t
  tdualPart stk t = tdualPart stk $ unAstNoVectorize t
  tplainPart t = AstNoVectorize $ tplainPart $ unAstNoVectorize t
  tfromPrimal stk t = AstNoVectorize $ tfromPrimal stk $ unAstNoVectorize t
  tfromDual t = AstNoVectorize $ tfromDual t
  tfromPlain stk t = AstNoVectorize $ tfromPlain stk $ unAstNoVectorize t

  taddTarget stk a b = AstNoVectorize $ taddTarget stk (unAstNoVectorize a)
                                                       (unAstNoVectorize b)
  tmultTarget stk a b = AstNoVectorize $ tmultTarget stk (unAstNoVectorize a)
                                                         (unAstNoVectorize b)
  tsum0Target stk a = AstNoVectorize $ tsum0Target stk (unAstNoVectorize a)
  tdot0Target stk a b = AstNoVectorize $ tdot0Target stk (unAstNoVectorize a)
                                                         (unAstNoVectorize b)

instance KnownSpan s => ConvertTensor (AstNoVectorize s) where
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

instance KnownSpan s => LetTensor (AstNoSimplify s) where
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

fmapwAstNoSimplify
  :: f (AstRaw s y) -> f (AstNoSimplify s y)
fmapwAstNoSimplify = unsafeCoerce

fmapwUnAstNoSimplify
  :: f (AstNoSimplify s y) -> f (AstRaw s y)
fmapwUnAstNoSimplify = unsafeCoerce

instance KnownSpan s => BaseTensor (AstNoSimplify s) where
  isConcreteInstance = False
  -- The implementation of these methods differs from the AstRaw instance:
  tkbuild1 @k f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @k) STKScalar
                         (unAstNoSimplify . f . AstNoSimplify)
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
  tmapAccumR _ !k !accftk !bftk !eftk f acc0 es =
    AstNoSimplify $ tmapAccumR Proxy k accftk bftk eftk f
                      (unAstNoSimplify acc0) (unAstNoSimplify es)
  tmapAccumRDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    AstNoSimplify $ tmapAccumRDer Proxy k accftk bftk eftk f df rf
                      (unAstNoSimplify acc0) (unAstNoSimplify es)
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
    wAstNoSimplify $ trindex (wunAstNoSimplify v) (fmapwUnAstNoSimplify ix)
  trindex0 a ix | SNat <- shrRank (rshape a) =
    kfromR $ trindex a ix
  trscatter sh t f =
    wAstNoSimplify $ trscatter sh (wunAstNoSimplify t)
                   $ fmapwUnAstNoSimplify . f . fmapwAstNoSimplify
  trgather sh t f =
    wAstNoSimplify $ trgather sh (wunAstNoSimplify t)
                   $ fmapwUnAstNoSimplify . f . fmapwAstNoSimplify
  trargMin = wAstNoSimplify . trargMin . wunAstNoSimplify
  trargMax = wAstNoSimplify . trargMax . wunAstNoSimplify
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
    wAstNoSimplify $ tsindex (wunAstNoSimplify v) (fmapwUnAstNoSimplify ix)
  tsindex0 @sh a ix | Refl <- lemAppNil @sh =
    withKnownShS (sshape a) $
    kfromS $ tsindex a ix
  tsscatter @_ @shm @shn @shp t f =
    wAstNoSimplify $ tsscatter @_ @_ @shm @shn @shp (wunAstNoSimplify t)
                   $ fmapwUnAstNoSimplify . f . fmapwAstNoSimplify
  tsgather @_ @shm @shn @shp t f =
    wAstNoSimplify $ tsgather @_ @_ @shm @shn @shp (wunAstNoSimplify t)
                   $ fmapwUnAstNoSimplify . f . fmapwAstNoSimplify
  tsargMin = wAstNoSimplify . tsargMin . wunAstNoSimplify
  tsargMax = wAstNoSimplify . tsargMax . wunAstNoSimplify
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
    wAstNoSimplify $ txindex (wunAstNoSimplify v) (fmapwUnAstNoSimplify ix)
  txindex0 @sh a ix | Refl <- lemAppNil @sh =
    withKnownShX (ssxFromShX $ xshape a) $
    kfromX $ txindex a ix
  txscatter @_ @shm @shn @shp sh t f =
    wAstNoSimplify $ txscatter @_ @_ @shm @shn @shp sh (wunAstNoSimplify t)
                   $ fmapwUnAstNoSimplify . f . fmapwAstNoSimplify
  txgather @_ @shm @shn @shp sh t f =
    wAstNoSimplify $ txgather @_ @_ @shm @shn @shp sh (wunAstNoSimplify t)
                   $ fmapwUnAstNoSimplify . f . fmapwAstNoSimplify
  txargMin = wAstNoSimplify . txargMin . wunAstNoSimplify
  txargMax = wAstNoSimplify . txargMax . wunAstNoSimplify
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
  tkargMin = wAstNoSimplify . tkargMin . wunAstNoSimplify
  tkargMax = wAstNoSimplify . tkargMax . wunAstNoSimplify

  -- General operations that don't require LetTensor nor ShareTensor
  tftk stk = tftk stk . wunAstNoSimplify
  tpair t1 t2 =
    wAstNoSimplify $ tpair (wunAstNoSimplify t1) (wunAstNoSimplify t2)
  tproject1 t = wAstNoSimplify $ tproject1 $ wunAstNoSimplify t
  tproject2 t = wAstNoSimplify $ tproject2 $ wunAstNoSimplify t
  tconcrete ftk a = wAstNoSimplify $ tconcrete ftk a
  tfromVector k stk =
    wAstNoSimplify . tfromVector k stk . fmapwUnAstNoSimplify
  tmapAccumLDer _ !k !accftk !bftk !eftk f df rf acc0 es =
    wAstNoSimplify $ tmapAccumLDer Proxy k accftk bftk eftk f df rf
                       (wunAstNoSimplify acc0) (wunAstNoSimplify es)
  tapply f t = wAstNoSimplify $ tapply f (wunAstNoSimplify t)
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
    STKR SNat x | Dict <- lemKnownSTK x -> trreplicate (fromSNat' snat) u
    STKS sh x | Dict <- lemKnownSTK x -> tsreplicate snat sh u
    STKX sh x | Dict <- lemKnownSTK x -> txreplicate snat sh u
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (treplicate snat stk1 (tproject1 u3))
              (treplicate snat stk2 (tproject2 u3))
  treverse snat stk u = case stk of
    STKScalar -> tsreverse u
    STKR _ x | Dict <- lemKnownSTK x -> trreverse u
    STKS _ x | Dict <- lemKnownSTK x -> tsreverse u
    STKX _ x | Dict <- lemKnownSTK x -> txreverse u
    STKProduct stk1 stk2 ->
      ttlet u $ \ !u3 ->
        tpair (treverse snat stk1 (tproject1 u3))
              (treverse snat stk2 (tproject2 u3))
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

  taddTarget stk a b = wAstNoSimplify $ taddTarget stk (wunAstNoSimplify a)
                                                       (wunAstNoSimplify b)
  tmultTarget stk a b = wAstNoSimplify $ tmultTarget stk (wunAstNoSimplify a)
                                                         (wunAstNoSimplify b)
  tsum0Target stk a = wAstNoSimplify $ tsum0Target stk (wunAstNoSimplify a)
  tdot0Target stk a b = wAstNoSimplify $ tdot0Target stk (wunAstNoSimplify a)
                                                         (wunAstNoSimplify b)

instance KnownSpan s => ConvertTensor (AstNoSimplify s) where
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
