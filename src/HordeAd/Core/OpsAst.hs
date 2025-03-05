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
import GHC.TypeLits (cmpNat, OrderingI (..), type (+), type (-), type (<=?))
import Data.Type.Equality (gcastWith)
import Unsafe.Coerce (unsafeCoerce)
import Data.Maybe (fromMaybe)

import Data.Array.Nested (StaticShX(..), type (++), Rank, KnownShS (..), KnownShX (..), ShX (..), ShS (..), IxR (..), IxS (..), IxX (..))
import Data.Array.Mixed.Types (snatPlus, Init, unsafeCoerceRefl)
import Data.Array.Mixed.Shape (withKnownShX, shxInit, shxEqual, ssxAppend, ssxReplicate, ssxFromShape)
import Data.Array.Nested.Internal.Shape (shCvtSX, shsProduct, shsRank, shrRank, withKnownShS)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Nested qualified as Nested

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
  :: forall x z.
     (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> AstTensor AstMethodShare PrimalSpan x
  -> AstVarName FullSpan x
  -> AstTensor AstMethodLet FullSpan x
  -> ADVal (AstRaw PrimalSpan) z
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit hVectorPrimal var hVector =
  let deltaInputs = generateDeltaInputs $ varNameToFTK var
      varInputs = dDnotShared (AstRaw hVectorPrimal) deltaInputs
      ast = g hVector
      env = extendEnv var varInputs envInit
  in interpretAst env ast

revArtifactFromForwardPass
  :: forall x z.
     Bool
  -> (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullTensorKind x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
-- Break the inline chain to prevent false positives in inspection testing.
-- {-# INLINE revArtifactFromForwardPass #-}
revArtifactFromForwardPass hasDt forwardPass xftk =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varPrimal, hVectorPrimal, var, hVector) = funToAstRev xftk in
  let -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D primalBody delta) = forwardPass hVectorPrimal var hVector in
  let zftk = ftkAst $ unAstRaw primalBody
      (!varDt, astDt) = funToAst (adFTK zftk) id in
  let oneAtF = constantTarget 1 $ adFTK zftk
      !dt = if hasDt then AstRaw astDt else oneAtF in
  let !gradient = gradientFromDelta xftk zftk dt delta
      !unGradient = unshareAstTensor $ unAstRaw gradient
      !unPrimal = unshareAstTensor $ unAstRaw primalBody
  in ( AstArtifactRev varDt varPrimal unGradient unPrimal
     , delta )

revProduceArtifact
  :: forall x z.
     Bool
  -> (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullTensorKind x
  -> (AstArtifactRev x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE revProduceArtifact #-}
revProduceArtifact hasDt g envInit xftk =
  revArtifactFromForwardPass
    hasDt (forwardPassByInterpretation g envInit) xftk

fwdArtifactFromForwardPass
  :: forall x z.
     (AstTensor AstMethodShare PrimalSpan x
      -> AstVarName FullSpan x
      -> AstTensor AstMethodLet FullSpan x
      -> ADVal (AstRaw PrimalSpan) z)
  -> FullTensorKind x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
-- Break the inline chain to prevent false positives in inspection testing.
-- {-# INLINE fwdArtifactFromForwardPass #-}
fwdArtifactFromForwardPass forwardPass xftk =
  let !(!varPrimalD, hVectorD, varPrimal, hVectorPrimal, var, hVector) =
        funToAstFwd xftk in
  let !(D primalBody delta) = forwardPass hVectorPrimal var hVector in
  let !derivative = derivativeFromDelta @x delta (adFTK xftk) (AstRaw hVectorD)
      !unDerivative = unshareAstTensor $ unAstRaw derivative
      !unPrimal = unshareAstTensor $ unAstRaw primalBody
  in ( AstArtifactFwd varPrimalD varPrimal unDerivative unPrimal
     , delta )

fwdProduceArtifact
  :: forall x z.
     (AstTensor AstMethodLet FullSpan x
      -> AstTensor AstMethodLet FullSpan z)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> FullTensorKind x
  -> (AstArtifactFwd x z, Delta (AstRaw PrimalSpan) z)
{-# INLINE fwdProduceArtifact #-}
fwdProduceArtifact f envInit xftk =
  fwdArtifactFromForwardPass (forwardPassByInterpretation f envInit) xftk


-- * AstTensor instances

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize
  :: AstSpan s
  => SNat k -> STensorKind y
  -> (AstInt AstMethodLet -> AstTensor AstMethodLet s y)
  -> AstTensor AstMethodLet s (BuildTensorKind k y)
astBuild1Vectorize k stk f = build1Vectorize k stk $ funToAstI f

instance AstSpan s => LetTensor (AstTensor AstMethodLet s) where
  ttlet u f = astLetFun u f
  toShare t = AstRaw $ AstToShare t
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  tunshare =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> unshareAstTensor . unAstRaw
      _ -> error "tunshare: used not at PrimalSpan"

-- The checks and error messages in these function result in complete
-- shape-checking of the ranked and mixed user code (shaped is already
-- fully checked by Haskell).
instance AstSpan s => BaseTensor (AstTensor AstMethodLet s) where
  tconstantTarget = constantTarget
  taddTarget = addTarget

  -- Ranked ops
  rshape t = case ftkAst t of
    FTKR sh _ -> sh
  rsum v = withSNat (rlength v) $ \snat -> astSum snat knownSTK v
  rreplicate k = withSNat k $ \snat -> astReplicate snat knownSTK
  rindex @_ @m @n a ix = case ftkAst a of
    FTKR @_ @x shmshn _ ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        astFromS @(TKS2 (Drop m sh) x) (knownSTK @(TKR2 n x))
        $ astIndexStepS @(Take m sh) @(Drop m sh)
                        (dropShS @m sh) (astSFromR @sh sh a) (ixrToIxs ix)
  rscatter @_ @m @_ @p shpshn0 t f = case ftkAst t of
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
  rgather @_ @m @_ @p shmshn0 t f = case ftkAst t of
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
            $ astGatherStepS @(Take m shmshn) @(Drop m shmshn) @(Take p shpshn)
                             knownShS (astSFromR shpshn t)
            $ funToAstIxS knownShS (ixrToIxs . f . ixsToIxr)
                -- this introduces new variable names
          _ -> error $ "rgather: shapes don't match: "
                       ++ show (dropShS @p shpshn, dropShS @m shmshn)
  trconcrete a = tconcrete (FTKR (Nested.rshape a) FTKScalar) (RepN a)
  rfloor @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKR (shrRank sh') knownSTK)
        . fromPrimal . AstFloorS . primalPart . astSFromR @sh sh $ a
  rfromIntegral @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKR (shrRank sh') knownSTK)
        . fromPrimal . astFromIntegralS . primalPart . astSFromR @sh sh $ a
  rcast @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKR (shsRank sh) STKScalar)
        . astCastS . astSFromR sh $ a
  rminIndex @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) (STKR (shsRank rest) STKScalar)
          . fromPrimal . AstMinIndexS . primalPart . astSFromR @sh sh $ a
        ZSS -> error "rminIndex: impossible empty shape"
  rmaxIndex @_ @r2 a = case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2) (STKR (shsRank rest) STKScalar)
          . fromPrimal . AstMaxIndexS . primalPart . astSFromR @sh sh $ a
        ZSS -> error "rmaxIndex: impossible empty shape"
  riota @r n =
    withSNat n $ \(SNat @n) ->
      astFromS (knownSTK @(TKR 1 r)) $ fromPrimal $ AstIotaS @n @r SNat
  rappend u v = case ftkAst u of
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
  rslice i n a = case ftkAst a of
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
  rreverse a = case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh -> case sh of
        _ :$$ _ ->
          astFromS (STKR (shrRank sh') (ftkToSTK x))
          . astReverseS . astSFromR sh $ a
        ZSS -> error "xreverse: impossible shape"
  rtranspose @r @n permr a = case ftkAst a of
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
              -- TODO: why is the above needed? define cmpSNat?
              case cmpNat (Permutation.permRank perm) (shsRank sh) of
                GTI -> error $ "rtranspose: rank mismatch: "
                               ++ show (sNatValue psnat, sNatValue shsnat)
                EQI -> result
                LTI -> result
  rreshape sh2' a = case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh ->
      withCastRS sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl -> astFromS (STKR (shrRank sh2') (ftkToSTK x))
                       . astReshapeS sh2 . astSFromR sh $ a
          _ -> error $ "rreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  rbuild1 @x @n k f = withSNat k $ \snat ->
                        astBuild1Vectorize snat (STKR (SNat @n) (knownSTK @x)) f

  -- Shaped ops
  sshape t = case ftkAst t of
    FTKS sh _ -> sh
  ssum = astSum SNat knownSTK
  sindex v ix = astIndexStepS knownShS v ix
  sscatter @_ @shm @shn @shp t f =
    astScatterS @shm @shn @shp knownShS t
    $ funToAstIxS knownShS f  -- this introduces new variable names
  sgather @_ @shm @shn @shp t f =
    astGatherStepS @shm @shn @shp knownShS t
    $ funToAstIxS knownShS f  -- this introduces new variable names
  tsconcrete = fromPrimal . AstConcreteS
  sfloor = fromPrimal . AstFloorS . primalPart
  sfromIntegral = fromPrimal . astFromIntegralS . primalPart
  scast = astCastS
  sminIndex = fromPrimal . AstMinIndexS . primalPart
  smaxIndex = fromPrimal . AstMaxIndexS . primalPart
  siota = fromPrimal $ AstIotaS SNat
  sappend u v = astAppendS u v
  sslice i n k = astSliceS i n k
  sreverse = astReverseS
  sbuild1 @k @sh @x f =
    astBuild1Vectorize (SNat @k) (STKS (knownShS @sh) (knownSTK @x)) f

  -- Mixed ops
  xshape t = case ftkAst t of
    FTKX sh _ -> sh
  xsum = astSum SNat knownSTK
  xreplicate = astReplicate SNat knownSTK
  xindex @_ @sh1 @sh2 a ix = case ftkAst a of
    FTKX @sh1sh2 @x sh1sh2 _ | SNat <- ssxRank (knownShX @sh1) ->
      withCastXS sh1sh2 $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Drop (Rank sh1) sh) :~: Rank sh2) $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1) sh ++ Drop (Rank sh1) sh :~: sh) $
        withKnownShS (takeShS @(Rank sh1) sh) $
        astFromS @(TKS2 (Drop (Rank sh1) sh) x) (knownSTK @(TKX2 sh2 x))
        $ astIndexStepS @(Take (Rank sh1) sh) @(Drop (Rank sh1) sh)
                        (dropShS @(Rank sh1) sh) (astSFromX @sh @sh1sh2 sh a) (ixxToIxs ix)
  xscatter @_ @shm @_ @shp shpshn0 t f = case ftkAst t of
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
            astFromS (STKX (ssxFromShape shpshn0) (ftkToSTK x))
            $ astScatterS @(Take (Rank shm) shmshn)
                          @(Drop (Rank shm) shmshn)
                          @(Take (Rank shp) shpshn) knownShS (astSFromX shmshn t)
            $ funToAstIxS knownShS (ixxToIxs . f . ixsToIxx)
                -- this introduces new variable names
          _ -> error $ "xscatter: shapes don't match: "
                       ++ show ( dropShS @(Rank shp) shpshn
                               , dropShS @(Rank shm) shmshn )
  xgather @_ @shm @_ @shp shmshn0 t f = case ftkAst t of
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
            astFromS (STKX (ssxFromShape shmshn0) (ftkToSTK x))
            $ astGatherStepS @(Take (Rank shm) shmshn)
                             @(Drop (Rank shm) shmshn)
                             @(Take (Rank shp) shpshn) knownShS (astSFromX shpshn t)
            $ funToAstIxS knownShS (ixxToIxs . f . ixsToIxx)
                -- this introduces new variable names
          _ -> error $ "xgather: shapes don't match: "
                       ++ show ( dropShS @(Rank shp) shpshn
                               , dropShS @(Rank shm) shmshn )
  txconcrete a = tconcrete (FTKX (Nested.mshape a) FTKScalar) (RepN a)
  xfloor @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKX (ssxFromShape sh') knownSTK)
        . fromPrimal . AstFloorS . primalPart . astSFromX @sh @sh' sh $ a
  xfromIntegral @_ @r2 @sh' a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKX (ssxFromShape sh') knownSTK)
        . fromPrimal . astFromIntegralS
        . primalPart . astSFromX @sh @sh' sh $ a
  xcast @_ @r2 a = case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        astFromS @(TKS sh r2) (STKX (ssxFromShape sh') STKScalar)
        . astCastS . astSFromX sh $ a
  xminIndex @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2)
                   (STKX (ssxFromShape $ shxInit sh') STKScalar)
          . fromPrimal . AstMinIndexS @n @rest
          . primalPart . astSFromX @sh @sh' sh $ a
  xmaxIndex @_ @r2 a = case ftkAst a of
    FTKX @sh' sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          astFromS @(TKS (Init sh) r2)
                   (STKX (ssxFromShape $ shxInit sh') STKScalar)
          . fromPrimal . AstMaxIndexS @n @rest
          . primalPart . astSFromX @sh @sh' sh $ a
  xiota @n @r = astFromS (knownSTK @(TKX '[Just n] r))
                $ fromPrimal $ AstIotaS @n @r SNat
  xappend u v = case ftkAst u of
    FTKX (Nested.SKnown m@SNat :$% shu') x -> case ftkAst v of
      FTKX (Nested.SKnown n@SNat :$% shv') _ ->
        withCastXS shu' $ \(shu :: ShS shu) ->
          withCastXS shv' $ \(shv :: ShS shv) ->
            case shxEqual shu' shv' of
              Just Refl ->
                gcastWith (unsafeCoerceRefl :: shu :~: shv) $
                astFromS (STKX (Nested.SKnown (snatPlus m n)
                                :!% ssxFromShape shu')
                               (ftkToSTK x))
                $ astAppendS (astSFromX (m :$$ shu) u)
                             (astSFromX (n :$$ shv) v)
              _ -> error $ "xappend: shapes don't match: "
                           ++ show (shu', shv')
  xslice i n@SNat k a = case ftkAst a of
    FTKX sh'@(_ :$% sh2') x ->
      withCastXS sh' $ \sh@(msnat :$$ _) ->
        case testEquality (snatPlus i (snatPlus n k)) msnat of
          Just Refl ->
            astFromS (STKX (Nested.SKnown n :!% ssxFromShape sh2')
                           (ftkToSTK x))
            . astSliceS i n k . astSFromX sh $ a
          _ -> error $ "xslice: argument tensor too narrow: "
                       ++ show ( sNatValue i, sNatValue n, sNatValue k
                               , sNatValue msnat )
  xreverse a = case ftkAst a of
    FTKX sh' x ->
      withCastXS sh' $ \(sh@(_ :$$ _) :: ShS sh) ->
        astFromS (STKX (ssxFromShape sh') (ftkToSTK x))
        . astReverseS . astSFromX @sh sh $ a
  xtranspose @perm a = case ftkAst a of
    FTKX sh' x ->
      let sh2' = shxPermutePrefix (Permutation.makePerm @perm) sh'
      in withCastXS sh' $ \sh ->
           astFromS (STKX (ssxFromShape sh2') (ftkToSTK x))
           . astTransposeS (Permutation.makePerm @perm)
           . astSFromX sh $ a
  xreshape sh2' a = case ftkAst a of
    FTKX sh' x ->
      withCastXS sh' $ \sh ->
      withCastXS sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl ->
            astFromS (STKX (ssxFromShape sh2') (ftkToSTK x))
            . astReshapeS sh2 . astSFromX sh $ a
          _ -> error $ "xreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  xbuild1 @k @sh @x f =
    astBuild1Vectorize (SNat @k) (STKX (knownShX @sh) (knownSTK @x)) f

  -- Scalar ops
  tkconcrete = fromPrimal . AstConcreteK
  kfloor = fromPrimal . AstFloorK . primalPart
  kfromIntegral = fromPrimal . astFromIntegralK . primalPart
  kcast = astCastK

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk = ftkAst
  tconcrete ftk a = fromPrimal $ astConcrete ftk a
  tpair t1 t2 = astPair t1 t2
  tproject1 = astProject1
  tproject2 = astProject2
  tsreplicate sh = astReplicate SNat (STKS sh knownSTK)
  stranspose @perm = tstranspose (Permutation.makePerm @perm)
    -- this is needed only to help GHC 9.10 compile the instance
  tstranspose perm = astTransposeS perm
  tsreshape sh = astReshapeS sh
  tmapAccumRDer _ !k _ !bShs !eShs f df rf acc0 es =
    astMapAccumRDer k bShs eShs f df rf acc0 es
  tmapAccumLDer _ !k _ !bShs !eShs f df rf acc0 es =
    astMapAccumLDer k bShs eShs f df rf acc0 es
  tApply t ll = astApply t ll
  tlambda ftk f =
    let (var, ast) = funToAst ftk $ unHFun f
    in AstLambda var ast
  tcond _ !b !u !v = astCond b u v
  tprimalPart t = primalPart t
  tdualPart _ t = dualPart t
  tfromPrimal _ t = fromPrimal t
  tfromDual t = fromDual t
  -- TODO: (still) relevant?
  -- In this instance, these three ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  trev xftk f =
    -- we don't have an AST constructor to hold it, so we compute
    --
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let -- No bangs here, because this goes under lambda and may be unneeded
        -- or even incorrect (and so, e.g., trigger
        -- `error "tunshare: used not at PrimalSpan"`, because no derivative
        -- should be taken of spans other than PrimalSpan)
        (AstArtifactRev{..}, _delta) =
          revProduceArtifact False (unHFun f) emptyEnv xftk
    in AstLambda artVarDomainRev (simplifyInline artDerivativeRev)
  trevDt ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactRev{..}, _delta) =
          revProduceArtifact True (unHFun f) emptyEnv ftkx
        ftkz = varNameToFTK artVarDtRev
        ftk2 = FTKProduct ftkz ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          astLet artVarDtRev (astProject1 astP)
          $ astLet artVarDomainRev (astProject2 astP)
          $ simplifyInline artDerivativeRev
    in AstLambda varP ast
  tfwd ftkx f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let (AstArtifactFwd{..}, _delta) =
          fwdProduceArtifact (unHFun f) emptyEnv ftkx
        ftk2 = FTKProduct (adFTK ftkx) ftkx
        (varP, ast) = funToAst ftk2 $ \ !astP ->
          astLet artVarDsFwd (astProject1 astP)
          $ astLet artVarDomainFwd (astProject2 astP)
          $ simplifyInline artDerivativeFwd
    in AstLambda varP ast

  tfromVector = astFromVector
  tsum snat@SNat stk u = case stk of
    STKScalar -> kfromS $ ssum u
    STKR SNat x | Dict <- lemKnownSTK x -> rsum u
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ ssum u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xsum u
    STKProduct stk1 stk2 ->
      tlet u $ \ !u3 ->
        tpair (tsum snat stk1 (tproject1 u3))
              (tsum snat stk2 (tproject2 u3))
  treplicate snat@SNat stk u = case stk of
    STKScalar -> tsreplicate ZSS $ sfromK u
    STKR SNat x | Dict <- lemKnownSTK x -> rreplicate (sNatValue snat) u
    STKS sh x | Dict <- lemKnownSTK x -> tsreplicate sh u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xreplicate u
    STKProduct stk1 stk2 ->
      tlet u $ \ !u3 ->
        tpair (treplicate snat stk1 (tproject1 u3))
              (treplicate snat stk2 (tproject2 u3))
  tindexBuild snat@SNat stk u i = case stk of
    STKScalar -> kfromS $ sindex u (i :.$ ZIS)
    STKR SNat x | Dict <- lemKnownSTK x -> rindex u (i :.: ZIR)
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ sindex u (i :.$ ZIS)
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xindex u (i :.% ZIX)
    STKProduct stk1 stk2 ->
      tlet u $ \ !u3 ->
        tpair (tindexBuild snat stk1 (tproject1 u3) i)
              (tindexBuild snat stk2 (tproject2 u3) i)


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
    u -> AstRaw $ fun1ToAst (ftkAst u) $ \ !var -> AstShare var u
  tunpair (AstRaw (AstPair t1 t2)) = (AstRaw t1, AstRaw t2)
  tunpair t = let tShared = tshare t
              in (tproject1 tShared, tproject2 tShared)

instance AstSpan s => BaseTensor (AstRaw s) where
  tconstantTarget = constantTarget
  taddTarget = addTarget

  -- Ranked ops
  rshape t = case ftkAst $ unAstRaw t of
    FTKR sh _ -> sh
  rsum v = withSNat (rlength v) $ \snat ->
             AstRaw . AstSum snat knownSTK . unAstRaw $ v
  rreplicate k = withSNat k $ \snat ->
    AstRaw . AstReplicate snat knownSTK . unAstRaw
  rindex @_ @m @n (AstRaw a) ix = AstRaw $ case ftkAst a of
    FTKR @_ @x shmshn _ ->
      withCastRS shmshn $ \(sh :: ShS sh) ->
        withKnownShS sh $
        gcastWith (unsafeCoerceRefl :: Rank (Take m sh) :~: m) $
        gcastWith (unsafeCoerceRefl :: Rank (Drop m sh) :~: n) $
        gcastWith (unsafeCoerceRefl :: Take m sh ++ Drop m sh :~: sh) $
        withKnownShS (takeShS @m sh) $
        AstFromS @(TKS2 (Drop m sh) x) (knownSTK @(TKR2 n x))
        $ AstIndexS @(Take m sh) @(Drop m sh)
                    (dropShS @m sh) (AstSFromR @sh sh a) (ixrToIxs (unAstRaw <$> ix))
  rscatter @_ @m @_ @p shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
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
  rgather @_ @m @_ @p shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
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
  trconcrete a = tconcrete (FTKR (Nested.rshape a) FTKScalar) (RepN a)
  rfloor @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKR (shrRank sh') knownSTK)
        . fromPrimal . AstFloorS . primalPart . AstSFromR @sh sh $ a
  rfromIntegral @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKR (shrRank sh') knownSTK)
        . fromPrimal . AstFromIntegralS . primalPart . AstSFromR @sh sh $ a
  rcast @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKR (shsRank sh) STKScalar)
        . AstCastS . AstSFromR sh $ a
  rminIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          -- unfortunately, this is not enough:
          -- gcastWith (unsafeCoerceRefl :: Rank sh :~: 1 + Rank (Init sh)) $
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (STKR (shsRank rest) STKScalar)
          . fromPrimal . AstMinIndexS . primalPart . AstSFromR @sh sh $ a
        ZSS -> error "rminIndex: impossible shape"
  rmaxIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' _ ->
      withCastRS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @_ @rest _ rest ->
          gcastWith (unsafeCoerceRefl :: Rank rest :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2) (STKR (shsRank rest) STKScalar)
          . fromPrimal . AstMaxIndexS . primalPart . AstSFromR @sh sh $ a
        ZSS -> error "rmaxIndex: impossible shape"
  riota @r n =
    AstRaw
    $ withSNat n $ \(SNat @n) ->
        AstFromS (knownSTK @(TKR 1 r)) $ fromPrimal $ AstIotaS @n @r SNat
  rappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
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
  rslice i n (AstRaw a) = AstRaw $ case ftkAst a of
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
  rreverse (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh -> case sh of
        _ :$$ _ ->
          AstFromS (STKR (shrRank sh') (ftkToSTK x))
          . AstReverseS . AstSFromR sh $ a
        ZSS -> error "xreverse: impossible shape"
  rtranspose @r @n permr (AstRaw a) = AstRaw $ case ftkAst a of
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
              -- TODO: why is the above needed? define cmpSNat?
              case cmpNat (Permutation.permRank perm) (shsRank sh) of
                GTI -> error $ "rtranspose: rank mismatch: "
                               ++ show (sNatValue psnat, sNatValue shsnat)
                EQI -> result
                LTI -> result
  rreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' x ->
      withCastRS sh' $ \sh ->
      withCastRS sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl -> AstFromS (STKR (shrRank sh2') (ftkToSTK x))
                       . AstReshapeS sh2 . AstSFromR sh $ a
          _ -> error $ "rreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  rbuild1 k f = withSNat k $ \snat ->
    AstRaw $ AstBuild1 snat knownSTK
    $ funToAstI  -- this introduces new variable names
    $ unAstRaw . f . AstRaw

  -- Shaped ops
  sshape t = case ftkAst $ unAstRaw t of
    FTKS sh _ -> sh
  ssum = AstRaw . AstSum SNat knownSTK . unAstRaw
  sindex v ix = AstRaw $ AstIndexS knownShS (unAstRaw v) (unAstRaw <$> ix)
  sscatter @_ @shm @shn @shp t f =
    AstRaw $ AstScatterS @shm @shn @shp knownShS (unAstRaw t)
           $ funToAstIxS knownShS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  sgather @_ @shm @shn @shp t f =
    AstRaw $ AstGatherS @shm @shn @shp knownShS (unAstRaw t)
           $ funToAstIxS knownShS (fmap unAstRaw . f . fmap AstRaw)
               -- this introduces new variable names
  tsconcrete = AstRaw . fromPrimal . AstConcreteS
  sfloor = AstRaw . fromPrimal . AstFloorS . primalPart . unAstRaw
  sfromIntegral =
    AstRaw . fromPrimal . AstFromIntegralS . primalPart . unAstRaw
  scast = AstRaw . AstCastS . unAstRaw
  sminIndex a = AstRaw . fromPrimal . AstMinIndexS . primalPart . unAstRaw $ a
  smaxIndex a = AstRaw . fromPrimal . AstMaxIndexS . primalPart . unAstRaw $ a
  siota = AstRaw . fromPrimal $ AstIotaS SNat
  sappend u v = AstRaw $ AstAppendS (unAstRaw u) (unAstRaw v)
  sslice i n k = AstRaw . AstSliceS i n k . unAstRaw
  sreverse = AstRaw . AstReverseS . unAstRaw
  sbuild1 @k f = AstRaw $ AstBuild1 (SNat @k) knownSTK
                 $ funToAstI  -- this introduces new variable names
                 $ unAstRaw . f . AstRaw

  -- Mixed ops
  xshape t = case ftkAst $ unAstRaw t of
    FTKX sh _ -> sh
  xsum = AstRaw . AstSum SNat knownSTK . unAstRaw
  xreplicate = AstRaw . AstReplicate SNat knownSTK . unAstRaw
  xindex @_ @sh1 @sh2 (AstRaw a) ix = case ftkAst a of
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
  xscatter @_ @shm @_ @shp shpshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
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
            AstFromS (STKX (ssxFromShape shpshn0) (ftkToSTK x))
            $ AstScatterS @(Take (Rank shm) shmshn)
                          @(Drop (Rank shm) shmshn)
                          @(Take (Rank shp) shpshn) knownShS (AstSFromX shmshn t)
            $ funToAstIxS knownShS (fmap unAstRaw . ixxToIxs . f . ixsToIxx
                           . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "xscatter: shapes don't match: "
                       ++ show ( dropShS @(Rank shp) shpshn
                               , dropShS @(Rank shm) shmshn )
  xgather @_ @shm @_ @shp shmshn0 (AstRaw t) f = AstRaw $ case ftkAst t of
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
            AstFromS (STKX (ssxFromShape shmshn0) (ftkToSTK x))
            $ AstGatherS @(Take (Rank shm) shmshn)
                         @(Drop (Rank shm) shmshn)
                         @(Take (Rank shp) shpshn) knownShS (AstSFromX shpshn t)
            $ funToAstIxS knownShS (fmap unAstRaw . ixxToIxs . f . ixsToIxx
                           . fmap AstRaw)
                -- this introduces new variable names
          _ -> error $ "xgather: shapes don't match: "
                       ++ show ( dropShS @(Rank shp) shpshn
                               , dropShS @(Rank shm) shmshn )
  txconcrete a = tconcrete (FTKX (Nested.mshape a) FTKScalar) (RepN a)
  xfloor @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKX (ssxFromShape sh') knownSTK)
        . fromPrimal . AstFloorS . primalPart . AstSFromX @sh @sh' sh $ a
  xfromIntegral @_ @r2 @sh' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKX (ssxFromShape sh') knownSTK)
        . fromPrimal . AstFromIntegralS
        . primalPart . AstSFromX @sh @sh' sh $ a
  xcast @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        AstFromS @(TKS sh r2) (STKX (ssxFromShape sh') STKScalar)
        . AstCastS . AstSFromX sh $ a
  xminIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2)
                   (STKX (ssxFromShape $ shxInit sh') STKScalar)
          . fromPrimal . AstMinIndexS @n @rest
          . primalPart . AstSFromX @sh @sh' sh $ a
  xmaxIndex @_ @r2 (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX @sh' sh' _ ->
      withCastXS sh' $ \(sh :: ShS sh) -> case sh of
        (:$$) @n @rest _ _ ->
          gcastWith (unsafeCoerceRefl :: Rank (Init sh') :~: Rank (Init sh)) $
          AstFromS @(TKS (Init sh) r2)
                   (STKX (ssxFromShape $ shxInit sh') STKScalar)
          . fromPrimal . AstMaxIndexS @n @rest
          . primalPart . AstSFromX @sh @sh' sh $ a
  xiota @n @r = AstRaw $ AstFromS (knownSTK @(TKX '[Just n] r))
                $ fromPrimal $ AstIotaS @n @r SNat
  xappend (AstRaw u) (AstRaw v) = AstRaw $ case ftkAst u of
    FTKX (Nested.SKnown m@SNat :$% shu') x -> case ftkAst v of
      FTKX (Nested.SKnown n@SNat :$% shv') _ ->
        withCastXS shu' $ \(shu :: ShS shu) ->
          withCastXS shv' $ \(shv :: ShS shv) ->
            case shxEqual shu' shv' of
              Just Refl ->
                gcastWith (unsafeCoerceRefl :: shu :~: shv) $
                AstFromS (STKX (Nested.SKnown (snatPlus m n)
                                :!% ssxFromShape shu')
                               (ftkToSTK x))
                $ AstAppendS (AstSFromX (m :$$ shu) u)
                             (AstSFromX (n :$$ shv) v)
              _ -> error $ "xappend: shapes don't match: "
                           ++ show (shu', shv')
  xslice i n@SNat k (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh'@(_ :$% sh2') x ->
      withCastXS sh' $ \sh@(msnat :$$ _) ->
        case testEquality (snatPlus i (snatPlus n k)) msnat of
          Just Refl ->
            AstFromS (STKX (Nested.SKnown n :!% ssxFromShape sh2')
                           (ftkToSTK x))
            . AstSliceS i n k . AstSFromX sh $ a
          _ -> error $ "xslice: argument tensor too narrow: "
                       ++ show ( sNatValue i, sNatValue n, sNatValue k
                               , sNatValue msnat )
  xreverse (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      withCastXS sh' $ \(sh@(_ :$$ _) :: ShS sh) ->
        AstFromS (STKX (ssxFromShape sh') (ftkToSTK x))
        . AstReverseS . AstSFromX @sh sh $ a
  xtranspose @perm (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      let sh2' = shxPermutePrefix (Permutation.makePerm @perm) sh'
      in withCastXS sh' $ \sh ->
           AstFromS (STKX (ssxFromShape sh2') (ftkToSTK x))
           . AstTransposeS (Permutation.makePerm @perm)
           . AstSFromX sh $ a
  xreshape sh2' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh' x ->
      withCastXS sh' $ \sh ->
      withCastXS sh2' $ \sh2 ->
        case testEquality (shsProduct sh) (shsProduct sh2) of
          Just Refl ->
            AstFromS (STKX (ssxFromShape sh2') (ftkToSTK x))
            . AstReshapeS sh2 . AstSFromX sh $ a
          _ -> error $ "xreshape: tensor size mismatch: "
                       ++ show ( sNatValue (shsProduct sh)
                               , sNatValue (shsProduct sh2) )
  xbuild1 @k f = AstRaw $ AstBuild1 (SNat @k) knownSTK
                 $ funToAstI  -- this introduces new variable names
                 $ unAstRaw . f . AstRaw

  -- Scalar ops
  tkconcrete = AstRaw . fromPrimal . AstConcreteK
  kfloor = AstRaw . fromPrimal . AstFloorK . primalPart . unAstRaw
  kfromIntegral = AstRaw . fromPrimal . AstFromIntegralK
                  . primalPart . unAstRaw
  kcast = AstRaw . AstCastK . unAstRaw

  -- General operations that don't require LetTensor nor ShareTensor
  tftk _stk = ftkAst . unAstRaw
  tconcrete ftk a = AstRaw $ fromPrimal $ unAstRaw $ astConcreteRaw ftk a
  tpair t1 t2 = AstRaw $ AstPair (unAstRaw t1) (unAstRaw t2)
  tproject1 t = AstRaw $ AstProject1 $ unAstRaw t
  tproject2 t = AstRaw $ AstProject2 $ unAstRaw t
  tsreplicate sh = AstRaw . AstReplicate SNat (STKS sh knownSTK) . unAstRaw
  stranspose @perm = tstranspose (Permutation.makePerm @perm)
    -- this is needed only to help GHC 9.10 compile the instance
  tstranspose perm = AstRaw . AstTransposeS perm . unAstRaw
  tsreshape sh = AstRaw . AstReshapeS sh . unAstRaw
  tmapAccumRDer _ !k _ !bShs !eShs f df rf acc0 es =
      AstRaw $ AstMapAccumRDer k bShs eShs f df rf (unAstRaw acc0) (unAstRaw es)
  tmapAccumLDer _ !k _ !bShs !eShs f df rf acc0 es =
      AstRaw $ AstMapAccumLDer k bShs eShs f df rf (unAstRaw acc0) (unAstRaw es)
  tApply t ll = AstRaw $ AstApply t (unAstRaw ll)
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tcond _ !b !u !v = AstRaw $ AstCond b (unAstRaw u) (unAstRaw v)
  tprimalPart t = AstRaw $ primalPart $ unAstRaw t
  tdualPart _ t = dualPart $ unAstRaw t
  tfromPrimal _ t = AstRaw $ fromPrimal $ unAstRaw t
  tfromDual t = AstRaw $ fromDual t
  -- TODO: (still) relevant?
  -- In this instance, these two ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  --
  -- TODO: dupe?
  -- These three methods are called at this type in delta evaluation via
  -- tmapAccumR and tmapAccumL, they have to work. We could refrain from
  -- simplifying the resulting terms, but it's not clear that's more consistent.
  trev = trev @(AstTensor AstMethodLet PrimalSpan)
  trevDt = trevDt @(AstTensor AstMethodLet PrimalSpan)
  tfwd = tfwd @(AstTensor AstMethodLet PrimalSpan)

  tfromVector k stk =
    AstRaw . AstFromVector k stk . V.map unAstRaw

instance AstSpan s => ConvertTensor (AstRaw s) where
  rzip @y @z (AstRaw a) = AstRaw $ case ftkAst a of
    FTKProduct (FTKR sh' y) (FTKR _ z) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        let (a31, a32) = tunpair $ AstRaw a
        in AstFromS @(TKS2 sh (TKProduct y z))
                      (STKR (shrRank sh')
                            (STKProduct (ftkToSTK y) (ftkToSTK z)))
           $ AstZipS $ AstPair (AstSFromR @sh sh $ unAstRaw a31)
                               (AstSFromR @sh sh $ unAstRaw a32)
  runzip @y @z (AstRaw a) = AstRaw $ case ftkAst a of
    FTKR sh' (FTKProduct y z) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        let b3 = AstUnzipS $ AstSFromR @sh sh a
            (b31, b32) = tunpair $ AstRaw b3
        in AstPair (AstFromS @(TKS2 sh y) (STKR (shrRank sh') (ftkToSTK y))
                    $ unAstRaw b31)
                   (AstFromS @(TKS2 sh z) (STKR (shrRank sh') (ftkToSTK z))
                    $ unAstRaw b32)
  szip = AstRaw . AstZipS . unAstRaw
  sunzip = AstRaw . AstUnzipS . unAstRaw
  xzip @y @z @sh' (AstRaw a) = case ftkAst a of
    FTKProduct (FTKX sh' y) (FTKX _ z) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        AstRaw
        $ let (a31, a32) = tunpair $ AstRaw a
          in AstFromS @(TKS2 sh (TKProduct y z))
                      (STKX (ssxFromShape sh')
                            (STKProduct (ftkToSTK y) (ftkToSTK z)))
             $ AstZipS $ AstPair (AstSFromX @sh @sh' sh $ unAstRaw a31)
                                 (AstSFromX @sh @sh' sh $ unAstRaw a32)
  xunzip @y @z @sh' (AstRaw a) = case ftkAst a of
    FTKX sh' (FTKProduct y z) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        AstRaw
        $ let b3 = AstRaw $ AstUnzipS $ AstSFromX @sh @sh' sh a
              (b31, b32) = tunpair b3
          in AstPair (AstFromS @(TKS2 sh y)
                               (STKX (ssxFromShape sh') (ftkToSTK y))
                      $ unAstRaw b31)
                     (AstFromS @(TKS2 sh z)
                               (STKX (ssxFromShape sh') (ftkToSTK z))
                      $ unAstRaw b32)

  tfromS _ zstk (AstRaw a) = AstRaw $ AstFromS zstk a
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

  xnestR @sh1' @m @x sh1' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1sh2' x | SNat <- ssxRank sh1' ->
      withCastXS sh1sh2' $ \(sh1sh2 :: ShS sh1sh2) ->
        withKnownShS sh1sh2 $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1') sh1sh2 ++ Drop (Rank sh1') sh1sh2
                      :~: sh1sh2) $
        (unsafeCoerce
           :: AstTensor AstMethodShare s
                (TKX2 sh1' (TKS2 (Drop (Rank sh1') sh1sh2) x))
           -> AstTensor AstMethodShare s (TKX2 sh1' (TKR2 m x)))
        $ AstFromS @(TKS2 (Take (Rank sh1') sh1sh2)
                          (TKS2 (Drop (Rank sh1') sh1sh2) x))
                   (STKX sh1' (STKS (dropShS @(Rank sh1') sh1sh2) (ftkToSTK x)))
        $ AstNestS (takeShS @(Rank sh1') sh1sh2) (dropShS @(Rank sh1') sh1sh2)
        $ AstSFromX @sh1sh2 sh1sh2 a
  xnestS @sh1' @sh2 @x sh1' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1sh2' x | SNat <- ssxRank sh1' ->
      withCastXS sh1sh2' $ \(sh1sh2 :: ShS sh1sh2) ->
        withKnownShS sh1sh2 $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1') sh1sh2 ++ sh2
                      :~: sh1sh2) $
        AstFromS @(TKS2 (Take (Rank sh1') sh1sh2) (TKS2 sh2 x))
                 (STKX sh1' (STKS knownShS (ftkToSTK x)))
        $ AstNestS @_ @sh2 (takeShS @(Rank sh1') sh1sh2) knownShS
        $ AstSFromX @sh1sh2 sh1sh2 a
  xnest @sh1' @sh2' @x sh1' (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1sh2' x | SNat <- ssxRank sh1' ->
      withCastXS sh1sh2' $ \(sh1sh2 :: ShS sh1sh2) ->
        withKnownShS sh1sh2 $
        gcastWith (unsafeCoerceRefl
                   :: Take (Rank sh1') sh1sh2 ++ Drop (Rank sh1') sh1sh2
                      :~: sh1sh2) $
        (unsafeCoerce
           :: AstTensor AstMethodShare s
                (TKX2 sh1' (TKS2 (Drop (Rank sh1') sh1sh2) x))
           -> AstTensor AstMethodShare s (TKX2 sh1' (TKX2 sh2' x)))
        $ AstFromS @(TKS2 (Take (Rank sh1') sh1sh2)
                          (TKS2 (Drop (Rank sh1') sh1sh2) x))
                   (STKX sh1' (STKS (dropShS @(Rank sh1') sh1sh2) (ftkToSTK x)))
        $ AstNestS (takeShS @(Rank sh1') sh1sh2) (dropShS @(Rank sh1') sh1sh2)
        $ AstSFromX @sh1sh2 sh1sh2 a
  xunNestR @sh1' @m @x (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1' y -> case y of
      FTKR sh2' x ->
        withCastXS sh1' $ \(sh1 :: ShS sh1) ->
        withCastRS sh2' $ \(_ :: ShS sh2) ->
          AstFromS @(TKS2 (sh1 ++ sh2) x)
                   (STKX (ssxFromShape sh1' `ssxAppend` ssxReplicate (SNat @m))
                         (ftkToSTK x))
          $ AstUnNestS @sh1 @sh2
          $ AstSFromX @sh1 sh1
          $ (unsafeCoerce
             :: AstTensor AstMethodShare s (TKX2 sh1' (TKR2 m x))
             -> AstTensor AstMethodShare s (TKX2 sh1' (TKS2 sh2 x)))
            a
  xunNestS @_ @sh2 @x (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1' y -> case y of
      FTKS _ x ->
        withCastXS sh1' $ \(sh1 :: ShS sh1) ->
          AstFromS @(TKS2 (sh1 ++ sh2) x)
                   (STKX (ssxFromShape sh1'
                          `ssxAppend` ssxFromShape (shCvtSX (knownShS @sh2)))
                         (ftkToSTK x))
          $ AstUnNestS @sh1 @sh2
          $ AstSFromX @sh1 sh1 a
  xunNest @sh1' @sh2' @x (AstRaw a) = AstRaw $ case ftkAst a of
    FTKX sh1' y -> case y of
      FTKX sh2' x ->
        withCastXS sh1' $ \(sh1 :: ShS sh1) ->
        withCastXS sh2' $ \(_ :: ShS sh2) ->
          AstFromS @(TKS2 (sh1 ++ sh2) x)
                   (STKX (ssxFromShape sh1' `ssxAppend` (knownShX @sh2'))
                         (ftkToSTK x))
          $ AstUnNestS @sh1 @sh2
          $ AstSFromX @sh1 sh1
          $ (unsafeCoerce
             :: AstTensor AstMethodShare s (TKX2 sh1' (TKX2 sh2' x))
             -> AstTensor AstMethodShare s (TKX2 sh1' (TKS2 sh2 x)))
            a

-- All but the last case are shortcuts for common forms.
astConcreteRaw :: FullTensorKind y -> RepN y
               -> AstRaw PrimalSpan y
astConcreteRaw ftk v = case ftk of
  FTKScalar -> AstRaw $ AstConcreteK $ unRepN v
  FTKR sh' FTKScalar -> AstRaw $
    withCastRS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS (ftkToSTK ftk) $ AstConcreteS (unRepN $ sfromR @_ @sh v)
  FTKS _ FTKScalar -> AstRaw $ AstConcreteS $ unRepN v
  FTKX sh' FTKScalar -> AstRaw $
    withCastXS sh' $ \(sh :: ShS sh) ->
      withKnownShS sh $
      AstFromS (ftkToSTK ftk) $ AstConcreteS (unRepN $ sfromX @_ @sh v)
  FTKProduct ftk1 ftk2 -> AstRaw $
    AstPair (unAstRaw $ astConcreteRaw ftk1 (tproject1 v))
                (unAstRaw $ astConcreteRaw ftk2 (tproject2 v))
  _ -> concreteTarget (tkconcrete . unRepN) (tsconcrete . unRepN)
                      (\stk a -> AstRaw $ AstFromS stk $ unAstRaw a)
                      (ftkToSTK ftk) v


-- * AstNoVectorize instances

instance AstSpan s => LetTensor (AstNoVectorize s) where
  ttlet u f = AstNoVectorize
              $ ttlet (unAstNoVectorize u)
                      (unAstNoVectorize . f . AstNoVectorize)
  toShare t = toShare $ unAstNoVectorize t

instance AstSpan s => BaseTensor (AstNoVectorize s) where
  tconstantTarget r ftk = AstNoVectorize $ tconstantTarget r ftk
  taddTarget stk a b = AstNoVectorize $ taddTarget stk (unAstNoVectorize a)
                                                       (unAstNoVectorize b)

  -- Ranked ops
  rshape = rshape . unAstNoVectorize
  rsum = AstNoVectorize . rsum . unAstNoVectorize
  rreplicate k = AstNoVectorize . rreplicate k . unAstNoVectorize
  rindex v ix =
    AstNoVectorize $ rindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  rscatter sh t f =
    AstNoVectorize $ rscatter sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  rgather sh t f =
    AstNoVectorize $ rgather sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  trconcrete = AstNoVectorize . trconcrete
  rfloor = AstNoVectorize . rfloor . unAstNoVectorize
  rfromIntegral = AstNoVectorize . rfromIntegral . unAstNoVectorize
  rcast = AstNoVectorize . rcast . unAstNoVectorize
  rminIndex = AstNoVectorize . rminIndex . unAstNoVectorize
  rmaxIndex = AstNoVectorize . rmaxIndex . unAstNoVectorize
  riota = AstNoVectorize . riota
  rappend u v =
    AstNoVectorize $ rappend (unAstNoVectorize u) (unAstNoVectorize v)
  rslice i n = AstNoVectorize . rslice i n . unAstNoVectorize
  rreverse = AstNoVectorize . rreverse . unAstNoVectorize
  rtranspose perm = AstNoVectorize . rtranspose perm . unAstNoVectorize
  rreshape sh = AstNoVectorize . rreshape sh . unAstNoVectorize
  rbuild1 k f = withSNat k $ \snat ->
    AstNoVectorize $ AstBuild1 snat knownSTK
    $ funToAstI  -- this introduces new variable names
    $ unAstNoVectorize . f . AstNoVectorize

  -- Shaped ops
  sshape = sshape . unAstNoVectorize
  ssum = AstNoVectorize . ssum . unAstNoVectorize
  sindex v ix =
    AstNoVectorize $ sindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  sscatter @_ @shm @shn @shp t f =
    AstNoVectorize $ sscatter @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  sgather @_ @shm @shn @shp t f =
    AstNoVectorize $ sgather @_ @_ @shm @shn @shp (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  tsconcrete = AstNoVectorize . tsconcrete
  sfloor = AstNoVectorize . sfloor . unAstNoVectorize
  sfromIntegral = AstNoVectorize . sfromIntegral . unAstNoVectorize
  scast = AstNoVectorize . scast . unAstNoVectorize
  sminIndex = AstNoVectorize . sminIndex . unAstNoVectorize
  smaxIndex = AstNoVectorize . smaxIndex . unAstNoVectorize
  siota = AstNoVectorize siota
  sappend u v =
    AstNoVectorize $ sappend (unAstNoVectorize u) (unAstNoVectorize v)
  sslice i n k = AstNoVectorize . sslice i n k . unAstNoVectorize
  sreverse = AstNoVectorize . sreverse . unAstNoVectorize
  sbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k) knownSTK
                 $ funToAstI  -- this introduces new variable names
                 $ unAstNoVectorize . f . AstNoVectorize

  -- Mixed ops
  xshape = xshape . unAstNoVectorize
  xsum = AstNoVectorize . xsum . unAstNoVectorize
  xreplicate = AstNoVectorize . xreplicate . unAstNoVectorize
  xindex v ix =
    AstNoVectorize $ xindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  xscatter @_ @shm @shn @shp sh t f =
    AstNoVectorize $ xscatter @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  xgather @_ @shm @shn @shp sh t f =
    AstNoVectorize $ xgather @_ @_ @shm @shn @shp sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  txconcrete = AstNoVectorize . txconcrete
  xfloor = AstNoVectorize . xfloor . unAstNoVectorize
  xfromIntegral = AstNoVectorize . xfromIntegral . unAstNoVectorize
  xcast = AstNoVectorize . xcast . unAstNoVectorize
  xminIndex = AstNoVectorize . xminIndex . unAstNoVectorize
  xmaxIndex = AstNoVectorize . xmaxIndex . unAstNoVectorize
  xiota @n = AstNoVectorize $ xiota @_ @n
  xappend u v =
    AstNoVectorize $ xappend (unAstNoVectorize u) (unAstNoVectorize v)
  xslice i n k = AstNoVectorize . xslice i n k . unAstNoVectorize
  xreverse = AstNoVectorize . xreverse . unAstNoVectorize
  xtranspose @perm =
    AstNoVectorize . xtranspose @_ @perm . unAstNoVectorize
  xreshape sh = AstNoVectorize . xreshape sh . unAstNoVectorize
  xbuild1 @k f = AstNoVectorize $ AstBuild1 (SNat @k) knownSTK
                 $ funToAstI  -- this introduces new variable names
                 $ unAstNoVectorize . f . AstNoVectorize

  -- Scalar ops
  tkconcrete = AstNoVectorize . tkconcrete
  kfloor = AstNoVectorize . kfloor . unAstNoVectorize
  kfromIntegral = AstNoVectorize . kfromIntegral . unAstNoVectorize
  kcast = AstNoVectorize . kcast . unAstNoVectorize

  -- General operations that don't require LetTensor nor ShareTensor
  tftk stk = tftk stk . unAstNoVectorize
  tconcrete ftk a = AstNoVectorize $ tconcrete ftk a
  tpair t1 t2 =
    AstNoVectorize $ tpair (unAstNoVectorize t1) (unAstNoVectorize t2)
  tproject1 t = AstNoVectorize $ tproject1 $ unAstNoVectorize t
  tproject2 t = AstNoVectorize $ tproject2 $ unAstNoVectorize t
  tsreplicate sh = AstNoVectorize . tsreplicate sh. unAstNoVectorize
  stranspose @perm = tstranspose (Permutation.makePerm @perm)
    -- this is needed only to help GHC 9.10 compile the instance
  tstranspose perm =
    AstNoVectorize . tstranspose perm . unAstNoVectorize
  tsreshape sh = AstNoVectorize . tsreshape sh . unAstNoVectorize
  tmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstNoVectorize $ tmapAccumRDer Proxy k accShs bShs eShs f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  tmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstNoVectorize $ tmapAccumLDer Proxy k accShs bShs eShs f df rf
                       (unAstNoVectorize acc0) (unAstNoVectorize es)
  tApply t ll = AstNoVectorize $ tApply t (unAstNoVectorize ll)
  tlambda = tlambda @(AstTensor AstMethodLet PrimalSpan)
  tcond !stk !b !u !v =
    AstNoVectorize $ tcond stk b (unAstNoVectorize u) (unAstNoVectorize v)
  tprimalPart t = AstNoVectorize $ tprimalPart $ unAstNoVectorize t
  tdualPart stk t = tdualPart stk $ unAstNoVectorize t
  tfromPrimal stk t = AstNoVectorize $ tfromPrimal stk $ unAstNoVectorize t
  tfromDual t = AstNoVectorize $ tfromDual t
  trev = trev @(AstTensor AstMethodLet PrimalSpan)
  trevDt = trevDt @(AstTensor AstMethodLet PrimalSpan)
  tfwd = tfwd @(AstTensor AstMethodLet PrimalSpan)

  tfromVector k stk =
    AstNoVectorize . tfromVector k stk . V.map unAstNoVectorize
  tsum k stk =
    AstNoVectorize . tsum k stk . unAstNoVectorize
  treplicate k stk =
    AstNoVectorize . treplicate k stk . unAstNoVectorize
  tindexBuild k stk u i =
    AstNoVectorize $ tindexBuild k stk (unAstNoVectorize u) (unAstNoVectorize i)

instance AstSpan s => ConvertTensor (AstNoVectorize s) where
  tunpairDup a = let (b, c) = tunpairDup $ unAstNoVectorize a
                 in (AstNoVectorize b, AstNoVectorize c)

  rzip = AstNoVectorize . rzip . unAstNoVectorize
  runzip = AstNoVectorize . runzip . unAstNoVectorize
  szip = AstNoVectorize . szip . unAstNoVectorize
  sunzip = AstNoVectorize . sunzip . unAstNoVectorize
  xzip = AstNoVectorize . xzip . unAstNoVectorize
  xunzip = AstNoVectorize . xunzip . unAstNoVectorize

  tfromS ystk zstk = AstNoVectorize . tfromS ystk zstk . unAstNoVectorize
  rfromX = AstNoVectorize . rfromX . unAstNoVectorize
  xfromR = AstNoVectorize . xfromR . unAstNoVectorize

  sfromK = AstNoVectorize . sfromK . unAstNoVectorize
  sfromR = AstNoVectorize . sfromR . unAstNoVectorize
  sfromX = AstNoVectorize . sfromX . unAstNoVectorize

  xnestR sh = AstNoVectorize . xnestR sh . unAstNoVectorize
  xnestS sh = AstNoVectorize . xnestS sh . unAstNoVectorize
  xnest sh = AstNoVectorize . xnest sh . unAstNoVectorize
  xunNestR = AstNoVectorize . xunNestR . unAstNoVectorize
  xunNestS = AstNoVectorize . xunNestS . unAstNoVectorize
  xunNest = AstNoVectorize . xunNest . unAstNoVectorize


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
    let (var, ast) = funToAst (ftkAst v) (f . AstFromS @y2 stkz)
    in AstLet var v ast
  AstFromPrimal (AstFromS @y2 stkz vRaw) ->
    let v = AstFromPrimal vRaw
        (var, ast) = funToAst (ftkAst v) (f . AstFromS @y2 stkz)
    in AstLet var v ast
  _ -> case ftkAst a of
    ftk@(FTKR @_ @x2 sh' x) ->
      withCastRS sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst (FTKS sh x) (f . AstFromS @(TKS2 sh x2) (ftkToSTK ftk))
        in AstLet var (AstSFromR @sh sh a) ast
             -- safe, because subsitution ruled out above
    ftk@(FTKX @_ @x sh' x) ->
      withCastXS sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst (FTKS sh x) (f . AstFromS @(TKS2 sh x) (ftkToSTK ftk))
        in AstLet var (AstSFromX @sh sh a) ast
    -- TODO: also recursively product, though may be not worth it
    ftk -> let (var, ast) = funToAst ftk f
           in AstLet var a ast

instance AstSpan s => LetTensor (AstNoSimplify s) where
  ttlet u f = AstNoSimplify
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
  rbuild1 @x @n k f = withSNat k $ \snat ->
    AstNoSimplify
    $ astBuild1Vectorize snat (STKR (SNat @n) (knownSTK @x))
                         (unAstNoSimplify . f . AstNoSimplify)
  sbuild1 @k @sh @x f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @k) (STKS (knownShS @sh) (knownSTK @x))
                         (unAstNoSimplify . f . AstNoSimplify)
  xbuild1 @k @sh @x f =
    AstNoSimplify
    $ astBuild1Vectorize (SNat @k) (STKX (knownShX @sh) (knownSTK @x))
                         (unAstNoSimplify . f . AstNoSimplify)
  -- These three have tricky types, so we repaat the AstRaw definitions:
  tcond _ !b !u !v =
    AstNoSimplify $ AstCond b (unAstNoSimplify u) (unAstNoSimplify v)
  tdualPart _ t = dualPart $ unAstNoSimplify t
  tfromDual t = AstNoSimplify $ fromDual t

  -- All the following implementations piggy-back on AstRaw implementations.
  tconstantTarget r ftk = wAstNoSimplify $ tconstantTarget r ftk
  taddTarget stk a b = wAstNoSimplify $ taddTarget stk (wunAstNoSimplify a)
                                                       (wunAstNoSimplify b)

  -- Ranked ops
  rshape = rshape . wunAstNoSimplify
  rsum = wAstNoSimplify . rsum . wunAstNoSimplify
  rreplicate k = wAstNoSimplify . rreplicate k . wunAstNoSimplify
  rindex v ix =
    wAstNoSimplify $ rindex (wunAstNoSimplify v) (wunAstNoSimplify <$> ix)
  rscatter sh t f =
    wAstNoSimplify $ rscatter sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  rgather sh t f =
    wAstNoSimplify $ rgather sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  trconcrete = wAstNoSimplify . trconcrete
  rfloor = wAstNoSimplify . rfloor . wunAstNoSimplify
  rfromIntegral = wAstNoSimplify . rfromIntegral . wunAstNoSimplify
  rcast = wAstNoSimplify . rcast . wunAstNoSimplify
  rminIndex = wAstNoSimplify . rminIndex . wunAstNoSimplify
  rmaxIndex = wAstNoSimplify . rmaxIndex . wunAstNoSimplify
  riota = wAstNoSimplify . riota
  rappend u v =
    wAstNoSimplify $ rappend (wunAstNoSimplify u) (wunAstNoSimplify v)
  rslice i n = wAstNoSimplify . rslice i n . wunAstNoSimplify
  rreverse = wAstNoSimplify . rreverse . wunAstNoSimplify
  rtranspose perm = wAstNoSimplify . rtranspose perm . wunAstNoSimplify
  rreshape sh = wAstNoSimplify . rreshape sh . wunAstNoSimplify

  -- Shaped ops
  sshape = sshape . wunAstNoSimplify
  ssum = wAstNoSimplify . ssum . wunAstNoSimplify
  sindex v ix =
    wAstNoSimplify $ sindex (wunAstNoSimplify v) (wunAstNoSimplify <$> ix)
  sscatter @_ @shm @shn @shp t f =
    wAstNoSimplify $ sscatter @_ @_ @shm @shn @shp (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  sgather @_ @shm @shn @shp t f =
    wAstNoSimplify $ sgather @_ @_ @shm @shn @shp (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  tsconcrete = wAstNoSimplify . tsconcrete
  sfloor = wAstNoSimplify . sfloor . wunAstNoSimplify
  sfromIntegral = wAstNoSimplify . sfromIntegral . wunAstNoSimplify
  scast = wAstNoSimplify . scast . wunAstNoSimplify
  sminIndex = wAstNoSimplify . sminIndex . wunAstNoSimplify
  smaxIndex = wAstNoSimplify . smaxIndex . wunAstNoSimplify
  siota = wAstNoSimplify siota
  sappend u v =
    wAstNoSimplify $ sappend (wunAstNoSimplify u) (wunAstNoSimplify v)
  sslice i n k = wAstNoSimplify . sslice i n k . wunAstNoSimplify
  sreverse = wAstNoSimplify . sreverse . wunAstNoSimplify

  -- Mixed ops
  xshape = xshape . wunAstNoSimplify
  xsum = wAstNoSimplify . xsum . wunAstNoSimplify
  xreplicate = wAstNoSimplify . xreplicate . wunAstNoSimplify
  xindex v ix =
    wAstNoSimplify $ xindex (wunAstNoSimplify v) (wunAstNoSimplify <$> ix)
  xscatter @_ @shm @shn @shp sh t f =
    wAstNoSimplify $ xscatter @_ @_ @shm @shn @shp sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  xgather @_ @shm @shn @shp sh t f =
    wAstNoSimplify $ xgather @_ @_ @shm @shn @shp sh (wunAstNoSimplify t)
                   $ fmap wunAstNoSimplify . f . fmap wAstNoSimplify
  txconcrete = wAstNoSimplify . txconcrete
  xfloor = wAstNoSimplify . xfloor . wunAstNoSimplify
  xfromIntegral = wAstNoSimplify . xfromIntegral . wunAstNoSimplify
  xcast = wAstNoSimplify . xcast . wunAstNoSimplify
  xminIndex = wAstNoSimplify . xminIndex . wunAstNoSimplify
  xmaxIndex = wAstNoSimplify . xmaxIndex . wunAstNoSimplify
  xiota @n = wAstNoSimplify $ xiota @_ @n
  xappend u v =
    wAstNoSimplify $ xappend (wunAstNoSimplify u) (wunAstNoSimplify v)
  xslice i n k = wAstNoSimplify . xslice i n k . wunAstNoSimplify
  xreverse = wAstNoSimplify . xreverse . wunAstNoSimplify
  xtranspose @perm =
    wAstNoSimplify . xtranspose @_ @perm . wunAstNoSimplify
  xreshape sh = wAstNoSimplify . xreshape sh . wunAstNoSimplify

  -- Scalar ops
  tkconcrete = wAstNoSimplify . tkconcrete
  kfloor = wAstNoSimplify . kfloor . wunAstNoSimplify
  kfromIntegral = wAstNoSimplify . kfromIntegral . wunAstNoSimplify
  kcast = wAstNoSimplify . kcast . wunAstNoSimplify

  -- General operations that don't require LetTensor nor ShareTensor
  tftk stk = tftk stk . wunAstNoSimplify
  tconcrete ftk a = wAstNoSimplify $ tconcrete ftk a
  tpair t1 t2 =
    wAstNoSimplify $ tpair (wunAstNoSimplify t1) (wunAstNoSimplify t2)
  tproject1 t = wAstNoSimplify $ tproject1 $ wunAstNoSimplify t
  tproject2 t = wAstNoSimplify $ tproject2 $ wunAstNoSimplify t
  tsreplicate sh = wAstNoSimplify . tsreplicate sh . wunAstNoSimplify
  stranspose @perm = tstranspose (Permutation.makePerm @perm)
    -- this is needed only to help GHC 9.10 compile the instance
  tstranspose perm =
    wAstNoSimplify . tstranspose perm . wunAstNoSimplify
  tsreshape sh = wAstNoSimplify . tsreshape sh . wunAstNoSimplify
  tmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    wAstNoSimplify $ tmapAccumRDer Proxy k accShs bShs eShs f df rf
                       (wunAstNoSimplify acc0) (wunAstNoSimplify es)
  tmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    wAstNoSimplify $ tmapAccumLDer Proxy k accShs bShs eShs f df rf
                       (wunAstNoSimplify acc0) (wunAstNoSimplify es)
  tApply t ll = wAstNoSimplify $ tApply t (wunAstNoSimplify ll)
  tlambda = tlambda @(AstRaw PrimalSpan)
  tprimalPart t = wAstNoSimplify $ tprimalPart $ wunAstNoSimplify t
  tfromPrimal stk t = wAstNoSimplify $ tfromPrimal stk $ wunAstNoSimplify t
  trev = trev @(AstRaw PrimalSpan)
  trevDt = trevDt @(AstRaw PrimalSpan)
  tfwd = tfwd @(AstRaw PrimalSpan)

  tfromVector k stk =
    wAstNoSimplify . tfromVector k stk . V.map wunAstNoSimplify
  tsum snat@SNat stk u = case stk of
    STKScalar -> kfromS $ ssum u
    STKR SNat x | Dict <- lemKnownSTK x -> rsum u
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ ssum u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xsum u
    STKProduct stk1 stk2 ->
      tlet u $ \ !u3 ->
        tpair (tsum snat stk1 (tproject1 u3))
              (tsum snat stk2 (tproject2 u3))
  treplicate snat@SNat stk u = case stk of
    STKScalar -> tsreplicate ZSS $ sfromK u
    STKR SNat x | Dict <- lemKnownSTK x -> rreplicate (sNatValue snat) u
    STKS sh x | Dict <- lemKnownSTK x -> tsreplicate sh u
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xreplicate u
    STKProduct stk1 stk2 ->
      tlet u $ \ !u3 ->
        tpair (treplicate snat stk1 (tproject1 u3))
              (treplicate snat stk2 (tproject2 u3))
  tindexBuild snat@SNat stk u i = case stk of
    STKScalar -> kfromS $ sindex u (i :.$ ZIS)
    STKR SNat x | Dict <- lemKnownSTK x -> rindex u (i :.: ZIR)
    STKS sh x | Dict <- lemKnownSTK x -> withKnownShS sh $ sindex u (i :.$ ZIS)
    STKX sh x | Dict <- lemKnownSTK x -> withKnownShX sh $ xindex u (i :.% ZIX)
    STKProduct stk1 stk2 ->
      tlet u $ \ !u3 ->
        tpair (tindexBuild snat stk1 (tproject1 u3) i)
              (tindexBuild snat stk2 (tproject2 u3) i)

instance AstSpan s => ConvertTensor (AstNoSimplify s) where
  tunpairDup (AstNoSimplify (AstPair t1 t2)) =  -- a tiny bit of simplification
    (AstNoSimplify t1, AstNoSimplify t2)
  tunpairDup t = (tproject1 t, tproject2 t)

  rzip = wAstNoSimplify . rzip . wunAstNoSimplify
  runzip = wAstNoSimplify . runzip . wunAstNoSimplify
  szip = wAstNoSimplify . szip . wunAstNoSimplify
  sunzip = wAstNoSimplify . sunzip . wunAstNoSimplify
  xzip = wAstNoSimplify . xzip . wunAstNoSimplify
  xunzip = wAstNoSimplify . xunzip . wunAstNoSimplify

  tfromS _ zstk = AstNoSimplify . AstFromS zstk . unAstNoSimplify
  rfromX = wAstNoSimplify . rfromX . wunAstNoSimplify
  xfromR = wAstNoSimplify . xfromR . wunAstNoSimplify

  sfromK = wAstNoSimplify . sfromK . wunAstNoSimplify
  sfromR = wAstNoSimplify . sfromR . wunAstNoSimplify
  sfromX = wAstNoSimplify . sfromX . wunAstNoSimplify

  xnestR sh = wAstNoSimplify . xnestR sh . wunAstNoSimplify
  xnestS sh = wAstNoSimplify . xnestS sh . wunAstNoSimplify
  xnest sh = wAstNoSimplify . xnest sh . wunAstNoSimplify
  xunNestR = wAstNoSimplify . xunNestR . wunAstNoSimplify
  xunNestS = wAstNoSimplify . xunNestS . wunAstNoSimplify
  xunNest = wAstNoSimplify . xunNest . wunAstNoSimplify
