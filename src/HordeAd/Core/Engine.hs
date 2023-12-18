{-# OPTIONS_GHC -Wno-orphans #-}
-- | The implementation of reverse derivative and (forward) derivative
-- calculation for an objective function on values of complicated
-- types (e.g., with tuple domains) expressed using the tensor classes.
-- Together with "HordeAd.Core.TensorClass", this forms the basic
-- high-level API of the horde-ad library. Optimizers are add-ons.
module HordeAd.Core.Engine
  ( -- * Reverse derivative adaptors
    rev, revDt, revArtifactAdapt, revProduceArtifactWithoutInterpretation
    -- * Forward derivative adaptors
  , fwd, fwdArtifactAdapt
    -- * Reverse and forward derivative stages class
  , forwardPassByApplication
    -- * Old gradient adaptors
  , crev, crevDt
    -- * Old derivative adaptors
  , cfwd
    -- * Additional common mechanisms
  , shapedToRanked
    -- * Re-exported for tests
  , interpretAst
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Const
import           Data.Int (Int64)
import           Data.Maybe (isJust)
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import           GHC.TypeLits (KnownNat, Nat)
import           Type.Reflection (Typeable)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstInterpret
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.TensorADVal ()
import HordeAd.Core.TensorAst ()
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

-- * Reverse derivative adaptors

-- VJP (vector-jacobian product) or Lop (left operations) are alternative
-- names to @rev@, but newcomers may have trouble understanding them.

{- TODO: this is temporarily replaced by a workaround needed for the SPECIALIZE
   to work, #23798.
-- | These work for any @g@ of DerivativeStages class.
rev
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> g r y) -> vals -> vals
rev f vals = revDtMaybe f vals Nothing
{- TODO: RULE left-hand side too complicated to desugar
{-# SPECIALIZE rev
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> AstRanked FullSpan Double y) -> vals
  -> vals #-}
-}

-- | This version additionally takes the sensitivity parameter.
revDt
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> g r y) -> vals -> ConcreteOf g r y -> vals
revDt f vals dt = revDtMaybe f vals (Just dt)
{- TODO: RULE left-hand side too complicated to desugar
{-# SPECIALIZE revDt
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> AstRanked FullSpan Double y) -> vals -> Flip OR.Array Double y
  -> vals #-}
-}

revDtMaybe
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals, Value vals ~ vals )
  => (astvals -> g r y) -> vals -> Maybe (ConcreteOf g) r y) -> vals
{-# INLINE revDtMaybe #-}
revDtMaybe f vals mdt =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
      artifact = fst $ revProduceArtifact (isJust mdt) g EM.empty domainsOD
  in parseDomains vals
     $ fst $ revEvalArtifact artifact domainsOD mdt
-}

-- | These work for any @g@ of DerivativeStages class.
rev
  :: forall r y g astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => (astvals -> g r y) -> Value astvals -> Value astvals
rev f vals = revDtMaybe f vals Nothing
{-# SPECIALIZE rev
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => (astvals -> AstRanked FullSpan Double y) -> Value astvals
  -> Value astvals #-}

-- | This version additionally takes the sensitivity parameter.
revDt
  :: forall r y g astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => (astvals -> g r y) -> Value astvals -> ConcreteOf g r y
  -> Value astvals
revDt f vals dt = revDtMaybe f vals (Just dt)
{-# SPECIALIZE revDt
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => (astvals -> AstRanked FullSpan Double y) -> Value astvals
  -> Flip OR.Array Double y
  -> Value astvals #-}

revDtMaybe
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g r y) -> vals -> Maybe (ConcreteOf g r y) -> vals
{-# INLINE revDtMaybe #-}
revDtMaybe f vals mdt =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
      artifact = fst $ revProduceArtifact (isJust mdt) g EM.empty domainsOD
  in gcastWith (unsafeCoerce Refl :: Value vals :~: vals) $  -- !!!
     parseDomains vals
     $ fst $ revEvalArtifact artifact domainsOD mdt

revArtifactAdapt
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => Bool -> (astvals -> g r y) -> vals
  -> (AstArtifactRev (PrimalOf g) r y, Dual (PrimalOf g) r y)
revArtifactAdapt hasDt f vals =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
  in revProduceArtifact hasDt g EM.empty domainsOD
{-# SPECIALIZE revArtifactAdapt
  :: ( HasSingletonDict y
     , AdaptableDomains (AstDynamic FullSpan) astvals
     , AdaptableDomains OD.Array (Value astvals) )
  => Bool -> (astvals -> AstRanked FullSpan Double y) -> Value astvals
  -> ( AstArtifactRev (AstRanked PrimalSpan) Double y
     , Dual (AstRanked PrimalSpan) Double y ) #-}

revProduceArtifactWithoutInterpretation
  :: forall g r y.
     ( g ~ AstRanked FullSpan  -- needed, because PrimalOf not injective
     , DerivativeStages g, GoodScalar r, HasSingletonDict y )
  => Bool
  -> (Domains (DynamicOf (ADVal (PrimalOf g)))
      -> ADVal (PrimalOf g) r y)
  -> DomainsOD
  -> (AstArtifactRev (PrimalOf g) r y, Dual (PrimalOf g) r y)
{-# INLINE revProduceArtifactWithoutInterpretation #-}
revProduceArtifactWithoutInterpretation hasDt g =
  revArtifactFromForwardPass @Nat @g hasDt (forwardPassByApplication g)

-- The commented out version is more general, but less performant.
forwardPassByApplication
  :: forall g r y dynamic.
     ( -- dynamic ~ DynamicOf (PrimalOf g)
       -- , ConvertTensor (PrimalOf g) (ShapedOf (PrimalOf g))
       dynamic ~ AstDynamic PrimalSpan  -- needed for generateDeltaInputsAst
     , Dual (Clown dynamic)
       ~ DeltaD (Clown dynamic) (PrimalOf g) (ShapedOf (PrimalOf g)) )
  => (Domains (DynamicOf (ADVal (PrimalOf g)))
      -> ADVal (PrimalOf g) r y)
  -> Domains (DynamicOf (PrimalOf g))
  -> [AstDynamicVarName g]
  -> Domains (DynamicOf g)
  -> ADVal (PrimalOf g) r y
{-# INLINE forwardPassByApplication #-}
forwardPassByApplication g domainsPrimal _ _ =
--  let deltaInputs = generateDeltaInputsOD @(PrimalOf g) domainsPrimal
  let deltaInputs = generateDeltaInputsAst domainsPrimal
      varInputs = makeADInputs domainsPrimal deltaInputs
  in g varInputs


-- * Forward derivative adaptors

-- | This takes the sensitivity parameter, by convention.
-- It uses the same delta expressions as for gradients.
--
-- Warning: this fails often with ranked tensor due to inability
-- to determine tensor shapes, see test testBarReluMax3Fwd.
-- Shaped tensors work fine.
fwd
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g r y) -> vals -> vals -> ConcreteOf g r y
fwd f x ds =
  let g domains = f $ parseDomains x domains
      domainsOD = toDomains x
      artifact = fst $ fwdProduceArtifact g EM.empty domainsOD
  in fst $ fwdEvalArtifact artifact domainsOD (toDomains ds)

fwdArtifactAdapt
  :: forall r y g vals astvals.
     ( DerivativeStages g, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf g) astvals
     , AdaptableDomains OD.Array vals
     , vals ~ Value astvals )
  => (astvals -> g r y) -> vals
  -> (AstArtifactFwd (PrimalOf g) r y, Dual (PrimalOf g) r y)
fwdArtifactAdapt f vals =
  let g domains = f $ parseDomains vals domains
      domainsOD = toDomains vals
  in fwdProduceArtifact g EM.empty domainsOD


-- * Old gradient adaptors, with constant and fixed inputs and dt

{- TODO: this is temporarily replaced by a workaround needed for the SPECIALIZE
   to work, #23798.
-- | The old versions that use the fixed input and @dt@ to compute gradient
-- only at these values, both transposing and evaluating at the same time.
--
-- These work for @f@ both ranked and shaped.
crev
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals, Value vals ~ vals )
  => (advals -> ADVal f r y) -> vals -> vals
crev f vals = crevDtMaybe f vals Nothing

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals, Value vals ~ vals )
  => (advals -> ADVal f r y) -> vals -> f r y -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals, Value vals ~ vals )
  => (advals -> ADVal f r y) -> vals -> Maybe (f r y) -> vals
{-# INLINE crevDtMaybe #-}
crevDtMaybe f vals mdt =
  let g inputs = f $ parseDomains vals inputs
  in parseDomains vals $ fst $ crevOnDomains mdt g (toDomains vals)
-}

-- | The old versions that use the fixed input and @dt@ to compute gradient
-- only at these values, both transposing and evaluating at the same time.
--
-- These work for @f@ both ranked and shaped.
crev
  :: forall r y f advals.
     ( DualPart f, UnletGradient f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , DomainsOf f ~ Domains (DynamicOf f)
     , RankedOf f ~ Flip OR.Array, ShapedOf f ~ Flip OS.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array (Value advals) )
  => (advals -> ADVal f r y) -> Value advals -> Value advals
crev f vals = crevDtMaybe f vals Nothing
{-# SPECIALIZE crev
  :: ( HasSingletonDict y
     , AdaptableDomains (DynamicOf (ADVal (Flip OR.Array))) advals
     , AdaptableDomains OD.Array (Value advals) )
  => (advals -> ADVal (Flip OR.Array) Double y)
  -> Value advals
  -> Value advals #-}

-- | This version additionally takes the sensitivity parameter.
crevDt
  :: forall r y f advals.
     ( DynamicOf f ~ DynamicOf (RankedOf f)
     , ConvertTensor (RankedOf f) (ShapedOf f)
     , Dual (Clown (DynamicOf f))
       ~ DeltaD (Clown (DynamicOf f)) (RankedOf f) (ShapedOf f)
     , DomainsOf f ~ Domains (DynamicOf f)
     , DualPart f, UnletGradient f, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains (DynamicOf f) (Value advals) )
  => (advals -> ADVal f r y) -> Value advals -> f r y -> Value advals
crevDt f vals dt = crevDtMaybe f vals (Just dt)
{-# SPECIALIZE crevDt
  :: ( HasSingletonDict y
     , AdaptableDomains (DynamicOf (ADVal (Flip OR.Array))) advals
     , AdaptableDomains OD.Array (Value advals) )
  => (advals -> ADVal (Flip OR.Array) Double y)
  -> Value advals
  -> Flip OR.Array Double y
  -> Value advals #-}

crevDtMaybe
  :: forall r y f vals advals.
     ( DynamicOf f ~ DynamicOf (RankedOf f)
     , ConvertTensor (RankedOf f) (ShapedOf f)
     , Dual (Clown (DynamicOf f))
       ~ DeltaD (Clown (DynamicOf f)) (RankedOf f) (ShapedOf f)
     , DomainsOf f ~ Domains (DynamicOf f)
     , DualPart f, UnletGradient f, GoodScalar r, HasSingletonDict y
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains (DynamicOf f) vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> Maybe (f r y) -> vals
{-# INLINE crevDtMaybe #-}
crevDtMaybe f vals mdt =
  gcastWith (unsafeCoerce Refl :: Value vals :~: vals) $  -- !!!
  let g inputs = f $ parseDomains vals inputs
  in parseDomains vals $ fst $ crevOnDomains mdt g (toDomains vals)

{-# SPECIALIZE crevOnDomains
  :: HasSingletonDict y
  => Maybe (Flip OR.Array Double y)
  -> (Domains (DynamicOf (ADVal (Flip OR.Array)))
      -> ADVal (Flip OR.Array) Double y)
  -> DomainsOD
  -> (DomainsOD, Flip OR.Array Double y) #-}

{-# SPECIALIZE crevOnADInputs
  :: HasSingletonDict y
  => Maybe (Flip OR.Array Double y)
  -> (Domains (DynamicOf (ADVal (Flip OR.Array)))
      -> ADVal (Flip OR.Array) Double y)
  -> Domains (DynamicOf (ADVal (Flip OR.Array)))
  -> (DomainsOD, Flip OR.Array Double y) #-}


-- * Old derivative adaptors, with constant and fixed inputs

-- | This takes the sensitivity parameter, by convention.
cfwd
  :: forall r y f vals advals.
     ( DualPart f, GoodScalar r, HasSingletonDict y
     , DynamicOf f ~ OD.Array
     , RankedOf f ~ Flip OR.Array, ShapedOf f ~ Flip OS.Array
     , AdaptableDomains (DynamicOf (ADVal f)) advals
     , AdaptableDomains OD.Array vals
     , vals ~ Value advals )
  => (advals -> ADVal f r y) -> vals -> vals
  -> f r y
cfwd f x ds =
  let g inputs = f $ parseDomains ds inputs
  in fst $ cfwdOnDomains (toDomains x) g (toDomains ds)


-- * Additional common mechanisms

shapedToRanked
  :: forall vals svals dynamic.
     ( dynamic ~ OD.Array, NoShape svals ~ vals, Value vals ~ vals
     , AdaptableDomains dynamic vals
     , AdaptableDomains dynamic svals, ForgetShape svals )
  => svals -> vals
shapedToRanked svals =
  parseDomains @dynamic (forgetShape svals) $ toDomains @dynamic svals




-- These and all other SPECIALIZE pragmas are needed due to the already
-- mostly fixed issues #21286 and others, because we want to have
-- reasonable performance on GHC 9.2 and 9.4 as well.
-- We need pragmas on shaped operations even for ranked benchmarks,
-- because threading the dictionaries through mutual recursive functions
-- would cause trouble.

{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan r n
  -> AstRanked PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimalRuntimeSpecialized
  :: (KnownNat n, Typeable r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}

{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan r sh
  -> AstShaped PrimalSpan r sh #-}
{-# SPECIALIZE interpretAstPrimalSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}

{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked PrimalSpan Int64 n
  -> Flip OR.Array Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan r n
  -> AstRanked PrimalSpan r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Double n
  -> AstRanked PrimalSpan Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Float n
  -> AstRanked PrimalSpan Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked PrimalSpan Int64 n
  -> AstRanked PrimalSpan Int64 n #-}
{-# SPECIALIZE interpretAstPrimal
  :: (KnownNat n, GoodScalar r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAstPrimal
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked PrimalSpan Int64 n
  -> Flip OR.Array Int64 n #-}

{-# SPECIALIZE interpretAstPrimalS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan Double sh
  -> Flip OS.Array Double sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan Float sh
  -> Flip OS.Array Float sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped PrimalSpan Int64 sh
  -> Flip OS.Array Int64 sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan r sh
  -> AstShaped PrimalSpan r sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan Double sh
  -> AstShaped PrimalSpan Double sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan Float sh
  -> AstShaped PrimalSpan Float sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped PrimalSpan Int64 sh
  -> AstShaped PrimalSpan Int64 sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan Double sh
  -> Flip OS.Array Double sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan Float sh
  -> Flip OS.Array Float sh #-}
{-# SPECIALIZE interpretAstPrimalS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped PrimalSpan Int64 sh
  -> Flip OS.Array Int64 sh #-}

{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan r n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan Double n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan Float n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked DualSpan Int64 n
  -> Product (Clown (Const ADShare)) (DeltaR (Flip OR.Array) (Flip OS.Array)) Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan r n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan Double n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan Float n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked DualSpan Int64 n
  -> Product (Clown (Const ADShare)) (DeltaR (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Int64 n #-}
{-# SPECIALIZE interpretAstDual
  :: (KnownNat n, GoodScalar r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan r n
  -> DummyDual r n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan Double n
  -> DummyDual Double n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan Float n
  -> DummyDual Float n #-}
{-# SPECIALIZE interpretAstDual
  :: KnownNat n
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked DualSpan Int64 n
  -> DummyDual Int64 n #-}

{-# SPECIALIZE interpretAstDualS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped DualSpan r sh
  -> Product (Clown (Const ADShare)) (DeltaS (Flip OR.Array) (Flip OS.Array)) r sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped DualSpan Double sh
  -> Product (Clown (Const ADShare)) (DeltaS (Flip OR.Array) (Flip OS.Array)) Double sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped DualSpan Float sh
  -> Product (Clown (Const ADShare)) (DeltaS (Flip OR.Array) (Flip OS.Array)) Float sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped DualSpan Int64 sh
  -> Product (Clown (Const ADShare)) (DeltaS (Flip OR.Array) (Flip OS.Array)) Int64 sh #-}
{-# SPECIALIZE interpretAstDualS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped DualSpan r sh
  -> Product (Clown (Const ADShare)) (DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan)) r sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped DualSpan Double sh
  -> Product (Clown (Const ADShare)) (DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Double sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped DualSpan Float sh
  -> Product (Clown (Const ADShare)) (DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Float sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped DualSpan Int64 sh
  -> Product (Clown (Const ADShare)) (DeltaS (AstRanked PrimalSpan) (AstShaped PrimalSpan)) Int64 sh #-}
{-# SPECIALIZE interpretAstDualS
  :: (Sh.Shape sh, GoodScalar r)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped DualSpan r sh
  -> DummyDual r sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped DualSpan Double sh
  -> DummyDual Double sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped DualSpan Float sh
  -> DummyDual Float sh #-}
{-# SPECIALIZE interpretAstDualS
  :: Sh.Shape sh
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped DualSpan Int64 sh
  -> DummyDual Int64 sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (KnownNat n, Typeable r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s r n
  -> ADVal (Flip OR.Array) r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (KnownNat n, Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s r n
  -> ADVal (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAstRuntimeSpecialized
  :: (KnownNat n, Typeable r, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s r n
  -> Flip OR.Array r n #-}

{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s r sh
  -> ADVal (Flip OS.Array) r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s r sh
  -> ADVal (AstShaped PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAstSRuntimeSpecialized
  :: (Sh.Shape sh, Typeable r, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s r sh
  -> Flip OS.Array r sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAst
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s r n
  -> ADVal (Flip OR.Array) r n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s Double n
  -> ADVal (Flip OR.Array) Double n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s Float n
  -> ADVal (Flip OR.Array) Float n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstRanked s Int64 n
  -> ADVal (Flip OR.Array) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s r n
  -> ADVal (AstRanked PrimalSpan) r n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s Double n
  -> ADVal (AstRanked PrimalSpan) Double n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s Float n
  -> ADVal (AstRanked PrimalSpan) Float n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstRanked s Int64 n
  -> ADVal (AstRanked PrimalSpan) Int64 n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, GoodScalar r, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s r n
  -> Flip OR.Array r n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s Double n
  -> Flip OR.Array Double n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s Float n
  -> Flip OR.Array Float n #-}
{-# SPECIALIZE interpretAst
  :: (KnownNat n, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstRanked s Int64 n
  -> Flip OR.Array Int64 n #-}

{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s r sh
  -> ADVal (Flip OS.Array) r sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s Double sh
  -> ADVal (Flip OS.Array) Double sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s Float sh
  -> ADVal (Flip OS.Array) Float sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstShaped s Int64 sh
  -> ADVal (Flip OS.Array) Int64 sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s r sh
  -> ADVal (AstShaped PrimalSpan) r sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s Double sh
  -> ADVal (AstShaped PrimalSpan) Double sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s Float sh
  -> ADVal (AstShaped PrimalSpan) Float sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstShaped s Int64 sh
  -> ADVal (AstShaped PrimalSpan) Int64 sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s r sh
  -> Flip OS.Array r sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s Double sh
  -> Flip OS.Array Double sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s Float sh
  -> Flip OS.Array Float sh #-}
{-# SPECIALIZE interpretAstS
  :: (Sh.Shape sh, AstSpan s)
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstShaped s Int64 sh
  -> Flip OS.Array Int64 sh #-}

-- This is needed for all three AstSpan values, to handle recursive calls
-- from interpretAstDual, etc.
{-# SPECIALIZE interpretAstDomains
  :: AstSpan s
  => AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstDomains s
  -> Domains (DynamicOf (ADVal (Flip OR.Array))) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstSpan s
  => AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstDomains s
  -> Domains (DynamicOf (ADVal (AstRanked PrimalSpan))) #-}
{-# SPECIALIZE interpretAstDomains
  :: AstSpan s
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstDomains s
  -> DomainsOD #-}
{-# SPECIALIZE interpretAstDomains
  :: AstSpan s
  => AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstDomains s
  -> DomainsOD #-}

{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (Flip OR.Array)) (ADVal (Flip OS.Array))
  -> AstBool
  -> (ADShare, Bool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (ADVal (AstRanked PrimalSpan)) (ADVal (AstShaped PrimalSpan))
  -> AstBool
  -> (ADShare, AstBool) #-}
{-# SPECIALIZE interpretAstBool
  :: AstEnv (Flip OR.Array) (Flip OS.Array)
  -> AstBool
  -> (ADShare, Bool) #-}
