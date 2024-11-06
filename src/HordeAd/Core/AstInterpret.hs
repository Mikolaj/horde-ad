{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fmax-pmcheck-models=10000 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
-- | Interpretation of AST terms in an aribtrary @RankedTensor@ & Co instance.
-- With the exception of the the interpretation of the sharing mechanisms,
-- the interpretation is the unique homorphism determined by the instance.
-- The sharing mechanisms are translated so as to preserve sharing in case
-- the instance is a term algebra as well.
module HordeAd.Core.AstInterpret
  ( interpretAstPrimal, interpretAst
  -- * Exported only to specialize elsewhere (because transitive specialization may not work, possibly)
  , interpretAstPrimalRuntimeSpecialized, interpretAstPrimalSRuntimeSpecialized
  , interpretAstDual
  , interpretAstRuntimeSpecialized, interpretAstSRuntimeSpecialized
  , interpretAstBool
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Array.Internal (valueOf)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Int (Int64)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Foreign.C (CInt)
import GHC.TypeLits (KnownNat, sameNat)
import Type.Reflection (Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Shape (pattern (:.%), pattern ZIX)
import Data.Array.Nested (Rank, type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (shrRank)

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.ShapedList (Drop, Take, pattern (:.$), pattern ZIS)
import HordeAd.Util.SizedList

interpretAst
  :: forall target s y. (ADReady target, AstSpan s)
  => AstEnv target
  -> AstTensor AstMethodLet s y -> target y
interpretAst !env = \case
  AstBuildHVector1 k (var, v) ->
    {-dmkHVector0 $-} dbuild1 k (interpretLambdaIHVector (\env2 t2 -> dunHVector0 $ interpretAst env2 t2) env (var, v))
