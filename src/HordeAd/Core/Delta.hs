{-# LANGUAGE GADTs, KindSignatures #-}
-- | The second component of dual numbers, @Delta@, with it's evaluation
-- function. Neel Krishnaswami calls that "sparse vector expressions",
-- and indeed the codomain of the evaluation function is a vector,
-- because the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
--
-- The algebraic structure here is an extension of vector space.
-- The crucial extra constructor for variables is used both to represent
-- sharing in order to avoid exponential blowup and to replace the one-hot
-- functionality with something cheaper and more uniform.
module HordeAd.Core.Delta
  ( Delta (..)
  , DeltaId (..)
  , DeltaBinding (..)
  , DeltaState (..)
  , evalBindings
  ) where

import Prelude

import           Control.Monad (unless, zipWithM_)
import           Control.Monad.ST.Strict (ST, runST)
import           Data.Kind (Type)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LinearAlgebra

import HordeAd.Internal.MatrixOuter

-- | This is the grammar of delta-expressions.
-- They have different but inter-related semantics at the level
-- of scalars, vectors and matrices (WIP: and arbitrary tensors).
-- Some make sense only on one of the levels, as expressed by the GADT
-- type constraints (WIP: currently this is broken by conflating
-- level-polymorphism and the polymorphism wrt the underlying scalar type
-- (Float, Double, etc.)).
--
-- In other words, for each choice of the underlying scalar type @r@,
-- we have three primitive differentiable types based on the scalar:
-- the scalar type @r@ itself, @Vector r@ and @Matrix r@.
data Delta :: Type -> Type where
  -- These constructors make sense at all levels: scalars, vectors, matrices,
  -- tensors. All constructors focusing on scalars belong to this group,
  -- that is, they make sense also for vectors, etc., and have more or less
  -- analogous semantics at the non-scalar levels.
  Zero :: Delta a
  Scale :: a -> Delta a -> Delta a
  Add :: Delta a -> Delta a -> Delta a
  Var :: DeltaId a -> Delta a

  -- Constructors related to vectors.
  Dot1 :: Vector r -> Delta (Vector r) -> Delta r
  SumElements1 :: Delta (Vector r) -> Int -> Delta r
  Konst1 :: Delta r -> Delta (Vector r)
  Seq1 :: Data.Vector.Vector (Delta r) -> Delta (Vector r)
  Index1 :: Delta (Vector r) -> Int -> Int -> Delta r
  Append1 :: Delta (Vector r) -> Int -> Delta (Vector r) -> Delta (Vector r)
  Slice1 :: Int -> Int -> Delta (Vector r) -> Int -> Delta (Vector r)

  -- Constructors related to matrices.
  Dot2 :: Matrix r -> Delta (Matrix r) -> Delta (Vector r)
  DotRow2 :: Vector r -> Delta (Matrix r) -> Delta (Vector r)
  AsRow2 :: Delta (Vector r) -> Delta (Matrix r)
  Seq2 :: Data.Vector.Vector (Delta (Vector r)) -> Delta (Matrix r)

newtype DeltaId a = DeltaId Int
  deriving (Show, Eq)

-- The @DeltaId@ components could be computed on the fly when evaluating,
-- but it costs more (they are boxed) than storing them here at the time
-- of binding creation.
data DeltaBinding r =
    DScalar (DeltaId r) (Delta r)
  | DVector (DeltaId (Vector r)) (Delta (Vector r))
  | DMatrix (DeltaId (Matrix r)) (Delta (Matrix r))

data DeltaState r = DeltaState
  { deltaCounter0 :: DeltaId r
  , deltaCounter1 :: DeltaId (Vector r)
  , deltaCounter2 :: DeltaId (Matrix r)
  , deltaBindings :: [DeltaBinding r]
  }

-- | This is the semantics of delta expressions. An expression of type @Delta a@
-- denotes a collection of finite maps from @DeltaId xi@ to @xi@, where
-- @xi@ belong to a finite set of types with the same underlying scalar type
-- as @a@. Each map is represented as a vector, small examples of which
-- are those in the result type of @evalBindings@. Requested lengths
-- of the vectors in the result type are given in the first few arguments.
-- The delta state contains a list of mutually-referencing delta bindings
-- that are to be evaluated, in the given order, starting with the top-level
-- binding of a scalar type provided in the remaining argument.
evalBindings :: (Eq r, Numeric r, Num (Vector r))
             => Int -> Int -> Int -> DeltaState r -> Delta r
             -> ( Vector r
                , Data.Vector.Vector (Vector r)
                , Data.Vector.Vector (Matrix r) )
evalBindings dim0 dim1 dim2 st dTopLevel =
  -- This is morally @V.create@ and so totally safe,
  -- but we can't just call @V.create@ thrice, because it would run
  -- the @ST@ action thrice, so we inline and extend @V.create@ here.
  runST $ do
    (finiteMap0, finiteMap1, finiteMap2) <- buildVectors st dTopLevel
    v0 <- V.unsafeFreeze $ VM.take dim0 finiteMap0
    v1 <- V.unsafeFreeze $ VM.take dim1 finiteMap1
    v2 <- V.unsafeFreeze $ VM.take dim2 finiteMap2
    -- Convert to normal matrices, but only the portion of vector
    -- that is not discarded.
    return (v0, v1, V.map convertMatrixOuterOrNull v2)

buildVectors :: forall s r. (Eq r, Numeric r, Num (Vector r))
             => DeltaState r -> Delta r
             -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                     , Data.Vector.Mutable.MVector s (Vector r)
                     , Data.Vector.Mutable.MVector s (MatrixOuter r) )
buildVectors st dTopLevel = do
  let DeltaId counter0 = deltaCounter0 st
      DeltaId counter1 = deltaCounter1 st
      DeltaId counter2 = deltaCounter2 st
  store0 <- VM.replicate counter0 0  -- correct value
  store1 <- VM.replicate counter1 (V.empty :: Vector r)  -- dummy value
  store2 <- VM.replicate counter2 emptyMatrixOuter  -- dummy value
  let addToVector :: Vector r -> Vector r -> Vector r
      addToVector r = \v -> if V.null v then r else v + r
      addToMatrix :: MatrixOuter r -> MatrixOuter r -> MatrixOuter r
      addToMatrix r = \v -> if nullMatrixOuter v then r else plusMatrixOuter v r
      eval0 :: r -> Delta r -> ST s ()
      eval0 !r = \case
        Zero -> return ()
        Scale k d -> eval0 (k * r) d
        Add d e -> eval0 r d >> eval0 r e
        Var (DeltaId i) -> VM.modify store0 (+ r) i
        Dot1 vr vd -> eval1 (LinearAlgebra.scale r vr) vd
        SumElements1 vd n -> eval1 (LinearAlgebra.konst r n) vd
        Index1 d i k -> eval1 (LinearAlgebra.konst 0 k V.// [(i, r)]) d

        -- Most of the impossible cases will be ruled out by GADT
        -- once the conflation fo parameterizations is cleared.
        Konst1{} -> error "buildVectors: Konst1 can't result in a scalar"
        Seq1{} -> error "buildVectors: Seq1 can't result in a scalar"
        Append1{} -> error "buildVectors: Append1 can't result in a scalar"
        Slice1{} -> error "buildVectors: Slice1 can't result in a scalar"
        Dot2{} -> error "buildVectors: Dot2 can't result in a scalar"
        DotRow2{} -> error "buildVectors: DotRow2 can't result in a scalar"
        AsRow2{} -> error "buildVectors: AsRow2 can't result in a scalar"
        Seq2{} -> error "buildVectors: Seq2 can't result in a scalar"
      eval1 :: Vector r -> Delta (Vector r) -> ST s ()
      eval1 !r = \case
        Zero -> return ()
        Scale k d -> eval1 (k * r) d
        Add d e -> eval1 r d >> eval1 r e
        Var (DeltaId i) -> VM.modify store1 (addToVector r) i
        Konst1 d -> V.mapM_ (`eval0` d) r
        Seq1 vd -> V.imapM_ (\i d -> eval0 (r V.! i) d) vd
        Append1 d k e -> eval1 (V.take k r) d >> eval1 (V.drop k r) e
        Slice1 i n d k -> eval1 (LinearAlgebra.konst 0 i
                                 V.++ r
                                 V.++ LinearAlgebra.konst 0 (k - i - n))
                                d
        Dot2 mr md -> eval2 (MatrixOuter (Just mr) (Just r) Nothing) md
          -- this column vector interacted disastrously with @mr = asRow v@
          -- in @(#>!)@, each causing an allocation of a whole new @n^2@ matrix
          -- and then a third with their outer product;
          -- by expressing the same function at the level of vectors
          -- instead of matrices, we can avoid even a single matrix allocation,
          -- at the cost of many extra delta expressions (per vector,
          -- not per matrix); another solution is just below
        DotRow2 row md -> eval2 (MatrixOuter Nothing (Just r) (Just row)) md
          -- this is a way to alleviate the ephemeral matrices problem,
          -- by polluting the API with the detail about the shape
          -- of the passed array (the replicated row shape),
          -- which eliminates two of the three matrix allocations

        Dot1{} -> error "buildVectors: unboxed vectors of vectors not possible"
        SumElements1{} ->
          error "buildVectors: unboxed vectors of vectors not possible"
        Index1{} ->
          error "buildVectors: unboxed vectors of vectors not possible"
      eval2 :: MatrixOuter r -> Delta (Matrix r) -> ST s ()
      eval2 !r = \case
        Zero -> return ()
        Scale k d -> eval2 (multiplyMatrixNormalAndOuter k r) d
        Add d e -> eval2 r d >> eval2 r e
        Var (DeltaId i) -> VM.modify store2 (addToMatrix r) i
        AsRow2 d -> mapM_ (`eval1` d) (toRowsMatrixOuter r)
        Seq2 md -> zipWithM_ eval1 (toRowsMatrixOuter r) (V.toList md)

        Dot1{} -> error "buildVectors: unboxed vectors of vectors not possible"
        SumElements1{} ->
          error "buildVectors: unboxed vectors of vectors not possible"
        Index1{} ->
          error "buildVectors: unboxed vectors of vectors not possible"
  eval0 1 dTopLevel  -- dt is 1 or hardwired in f
  let evalUnlessZero :: DeltaBinding r -> ST s ()
      evalUnlessZero (DScalar (DeltaId i) d) = do
        r <- store0 `VM.read` i
        unless (r == 0) $  -- we init with exactly 0 so the comparison is OK
          eval0 r d
      evalUnlessZero (DVector (DeltaId i) d) = do
        r <- store1 `VM.read` i
        unless (V.null r) $
          eval1 r d
      evalUnlessZero (DMatrix (DeltaId i) d) = do
        r <- store2 `VM.read` i
        unless (nullMatrixOuter r) $
          eval2 r d
  mapM_ evalUnlessZero (deltaBindings st)
  return (store0, store1, store2)
