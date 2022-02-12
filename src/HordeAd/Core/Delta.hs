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

import           Control.Exception (assert)
import           Control.Monad (foldM, unless, zipWithM_)
import           Control.Monad.ST.Strict (ST, runST)
import           Data.Kind (Type)
import           Data.STRef
import qualified Data.Strict.IntMap as IM
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           Numeric.LinearAlgebra
  (Matrix, Numeric, Vector, fromRows, konst)
import qualified Numeric.LinearAlgebra

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
  Var :: DeltaId -> Delta a

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

newtype DeltaId = DeltaId Int
  deriving (Show, Eq)

data DeltaBinding r =
    DScalar (Delta r)
  | DVector (Delta (Vector r))
  | DMatrix (Delta (Matrix r))

data DeltaState r = DeltaState
  { deltaCounter  :: DeltaId
  , deltaBindings :: [DeltaBinding r]
  }

-- | Semantics of delta expressions.
evalBindings :: forall r. (Eq r, Numeric r, Num (Vector r))
             => Int -> Int -> Int -> DeltaState r -> Delta r
             -> ( Vector r
                , Data.Vector.Vector (Vector r)
                , Data.Vector.Vector (Matrix r) )
evalBindings dim dimV dimL st d0 =
  -- This is morally @V.create@ and so totally safe,
  -- but we can't just call @V.create@ thrice, because it would run
  -- the @ST@ action thrice, so we inline and extend @V.create@ here.
  runST $ do
    (res, resV, resL) <- buildVector dim dimV dimL st d0
    r <- V.unsafeFreeze res
    rV <- V.unsafeFreeze resV
    rL <- V.unsafeFreeze resL
    -- Prevent a crash if a parameter not updated.
    let convertMatrix (MatrixOuter Nothing Nothing Nothing) = fromRows []
        convertMatrix o = convertMatrixOuter o
    return (r, rV, V.map convertMatrix rL)

buildVector :: forall s r. (Eq r, Numeric r, Num (Vector r))
            => Int -> Int -> Int -> DeltaState r -> Delta r
            -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                    , Data.Vector.Mutable.MVector s (Vector r)
                    , Data.Vector.Mutable.MVector s (MatrixOuter r) )
buildVector dim dimV dimL st d0 = do
  let DeltaId storeSize = deltaCounter st
      dimSV = dim + dimV
      dimSVL = dim + dimV + dimL
  -- This is relatively very cheap allocation, so no problem even when most
  -- or all parameters and vars are inside vectors, matrices, etc.
  -- (and vectors and matrices are usually orders of magnitude less numerous
  -- than the sum total of individual parameters):
  store <- VM.replicate storeSize 0  -- correct value
  -- Here, for performance, we partially undo the nice unification
  -- of parameters and delta-variables. Fortunately, this is completely local.
  -- Allocating all these as boxed vectors would be very costly
  -- if most parameters are scalars and so most cells are unused,
  -- so we keep them in a sparse map, except for those that are guaranteed
  -- to be used, because they represent parameters:
  storeV <- VM.replicate dimV (V.empty :: Vector r)  -- dummy value
  storeL <- VM.replicate dimL (MatrixOuter Nothing Nothing Nothing
                               :: MatrixOuter r)  -- dummy value
  intMapV <- newSTRef IM.empty
  intMapL <- newSTRef IM.empty
  -- This is probably not worth optimizing further, e.g., reusing the same
  -- three parameter vectors (only the initial portion of @store@ for scalars)
  -- or updating in-place inside vectors and matrices. Experiments indicate
  -- that allocation and runtime gains of the latter optimization are
  -- a few percent (because the vector and matrix arithmetics
  -- in the forward pass and the adjustment of parameters by gradients
  -- are done immutably anyway), and for both optimizations, any thunk
  -- pointing inside the mutated vectors can easily be catastrophic.
  -- Maintaining this brittle optimization would also make harder any future
  -- parallelization, whether on CPU or GPU.
  --
  -- OTOH, removing @storeV@ and @storeL@ and using the @IntMap@
  -- througout increases GC time for vector-based MNIST500x500 by half,
  -- so let's keep them. Probably CPU manages cache better when vectors
  -- are stored in a (mutable?) vector, not a tree spread all around the heap.
  -- For few but very long vectors this may not matter much, though.
  let addToVector :: Int -> Vector r -> ST s ()
      {-# INLINE addToVector #-}
      addToVector i r = let addToStore v = if V.null v then r else v + r
                            addToIntMap (Just v) = Just $ v + r
                            addToIntMap Nothing = Just r
                        in if i < dimSV
                           then VM.modify storeV addToStore (i - dim)
                           else modifySTRef' intMapV (IM.alter addToIntMap i)
      addToMatrix :: Int -> MatrixOuter r -> ST s ()
      {-# INLINE addToMatrix #-}
      addToMatrix i r = let addToStore v = if nullMatrixOuter v
                                           then r
                                           else plusMatrixOuter v r
                            addToIntMap (Just v) = Just $ plusMatrixOuter v r
                            addToIntMap Nothing = Just r
                        in if i < dimSVL
                           then VM.modify storeL addToStore (i - dimSV)
                           else modifySTRef' intMapL (IM.alter addToIntMap i)
  let eval :: r -> Delta r -> ST s ()
      eval !r = \case
        Zero -> return ()
        Scale k d -> eval (k * r) d
        Add d1 d2 -> eval r d1 >> eval r d2
        Var (DeltaId i) -> VM.modify store (+ r) i
        Dot1 vr vd -> evalV (Numeric.LinearAlgebra.scale r vr) vd
        SumElements1 vd n -> evalV (konst r n) vd
        Index1 d i k -> evalV (konst 0 k V.// [(i, r)]) d

        -- Most of the impossible cases will be ruled out by GADT
        -- once the conflation fo polymorphisms is cleared.
        Konst1{} -> error "buildVector: Konst1 can't result in a scalar"
        Seq1{} -> error "buildVector: Seq1 can't result in a scalar"
        Append1{} -> error "buildVector: Append1 can't result in a scalar"
        Slice1{} -> error "buildVector: Slice1 can't result in a scalar"
        Dot2{} -> error "buildVector: Dot2 can't result in a scalar"
        DotRow2{} -> error "buildVector: DotRow2 can't result in a scalar"
        AsRow2{} -> error "buildVector: AsRow2 can't result in a scalar"
        Seq2{} -> error "buildVector: Seq2 can't result in a scalar"
      evalV :: Vector r -> Delta (Vector r) -> ST s ()
      evalV !r = \case
        Zero -> return ()
        Scale k d -> evalV (k * r) d
        Add d1 d2 -> evalV r d1 >> evalV r d2
        Var (DeltaId i) -> addToVector i r
        Konst1 d -> V.mapM_ (`eval` d) r
        Seq1 vd -> V.imapM_ (\i d -> eval (r V.! i) d) vd
        Append1 d1 k d2 -> evalV (V.take k r) d1 >> evalV (V.drop k r) d2
        Slice1 i n d k -> evalV (konst 0 i V.++ r V.++ konst 0 (k - i - n)) d
        Dot2 mr md -> evalL (MatrixOuter (Just mr) (Just r) Nothing) md
          -- this column vector interacted disastrously with @mr = asRow v@
          -- in @(#>!)@, each causing an allocation of a whole new @n^2@ matrix
          -- and then a third with their outer product;
          -- when doing the same computation by hand using @Vector@
          -- instead of @Matrix@, we can avoid even a single matrix allocation;
          -- the cost for the manual computation is many extra delta
          -- expressions which, however, with square enough matrices,
          -- don't dominate
        DotRow2 row md -> evalL (MatrixOuter Nothing (Just r) (Just row)) md
          -- this is a way to alleviate the ephemeral matrices problem,
          -- by polluting the API with the detail about the shape
          -- of the passed array (the replicated row shape),
          -- which eliminates two of the three matrix allocations

        Dot1{} -> error "buildVector: unboxed vectors of vectors not possible"
        SumElements1{} ->
          error "buildVector: unboxed vectors of vectors not possible"
        Index1{} -> error "buildVector: unboxed vectors of vectors not possible"
      evalL :: MatrixOuter r -> Delta (Matrix r) -> ST s ()
      evalL !r@(MatrixOuter mm mc mr) = \case
        Zero -> return ()
        Scale k d ->
          let !m = maybe k (k *) mm
          in evalL (MatrixOuter (Just m) mc mr) d
        Add d1 d2 -> evalL r d1 >> evalL r d2
        Var (DeltaId i) -> addToMatrix i r
        AsRow2 d -> mapM_ (`evalV` d) (toRowsMatrixOuter r)
        Seq2 md -> zipWithM_ evalV (toRowsMatrixOuter r) (V.toList md)

        Dot1{} -> error "buildVector: unboxed vectors of vectors not possible"
        SumElements1{} ->
          error "buildVector: unboxed vectors of vectors not possible"
        Index1{} -> error "buildVector: unboxed vectors of vectors not possible"
  eval 1 d0  -- dt is 1 or hardwired in f
  let evalUnlessZero :: DeltaId -> DeltaBinding r -> ST s DeltaId
      evalUnlessZero (DeltaId !i) (DScalar d) = do
        r <- store `VM.read` i
        unless (r == 0) $  -- we init with exactly 0 so the comparison is OK
          eval r d
        return $! DeltaId (pred i)
      evalUnlessZero (DeltaId !i) (DVector d) = do
        if i < dimSV then do
          r <- storeV `VM.read` (i - dim)
          unless (V.null r) $
            evalV r d
        else do
          mr <- IM.lookup i <$> readSTRef intMapV
          maybe (pure ()) (`evalV` d) mr
        return $! DeltaId (pred i)
      evalUnlessZero (DeltaId !i) (DMatrix d) = do
        if i < dimSVL then do
          r <- storeL `VM.read` (i - dimSV)
          unless (nullMatrixOuter r) $
            evalL r d
        else do
          mr <- IM.lookup i <$> readSTRef intMapL
          maybe (pure ()) (`evalL` d) mr
        return $! DeltaId (pred i)
  minusOne <- foldM evalUnlessZero (DeltaId $ pred storeSize) (deltaBindings st)
  let _A = assert (minusOne == DeltaId (-1)) ()
  return (VM.slice 0 dim store, storeV, storeL)
