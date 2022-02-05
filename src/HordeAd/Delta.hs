{-# LANGUAGE FlexibleContexts, GADTs, KindSignatures #-}
-- | The second component of dual numbers, @Delta@, with it's evaluation
-- function. Neel Krishnaswami calls that "sparse vector expressions",
-- and indeed the codomain of the evaluation function is a vector,
-- because the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
--
-- The algebraic structure here is an extension of vector space.
-- The crucial extra constructor for variables is used both to represent
-- sharing in order to avoid exponential blowup and to replace the one-hot
-- functionality with something cheaper and more uniform.
module HordeAd.Delta
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
import           Data.Maybe (fromMaybe)
import           Data.STRef
import qualified Data.Strict.IntMap as IM
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           Numeric.LinearAlgebra
  (Matrix, Numeric, Vector, asColumn, fromRows, konst, outer, rows, toRows)
import qualified Numeric.LinearAlgebra

-- | A matrix representation as a product of a basic matrix
-- and an outer product of two vectors.
data MatrixOuter r = MatrixOuter (Maybe (Matrix r))
                                 (Maybe (Vector r, Vector r))

convertMatrixOuter :: (Numeric r, Num (Vector r)) => MatrixOuter r -> Matrix r
convertMatrixOuter (MatrixOuter mm Nothing) =
  fromMaybe (error "convertMatrixOuter: dimensions can't be determined") mm
convertMatrixOuter (MatrixOuter Nothing mcr) =
  maybe (error "convertMatrixOuter: dimensions can't be determined")
        (uncurry outer)
        mcr
convertMatrixOuter (MatrixOuter (Just m) (Just cr)) = m * uncurry outer cr

data Delta :: Type -> Type where
  Zero :: Delta a
  Scale :: a -> Delta a -> Delta a
  Add :: Delta a -> Delta a -> Delta a
  Var :: DeltaId -> Delta a
  Dot :: Vector r -> Delta (Vector r) -> Delta r
  SumElements :: Delta (Vector r) -> Int -> Delta r
  Konst :: Delta r -> Delta (Vector r)
  Seq :: Data.Vector.Vector (Delta r) -> Delta (Vector r)
  Index :: Delta (Vector r) -> Int -> Int -> Delta r
  DotL :: Matrix r -> Delta (Matrix r) -> Delta (Vector r)
  DotRowL :: Vector r -> Delta (Matrix r) -> Delta (Vector r)
  KonstL :: Delta (Vector r) -> Delta (Matrix r)
  SeqL :: Data.Vector.Vector (Delta (Vector r)) -> Delta (Matrix r)

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

buildVector :: forall s r. (Eq r, Numeric r, Num (Vector r))
            => Int -> Int -> Int -> DeltaState r -> Delta r
            -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                    , Data.Vector.Mutable.MVector s (Vector r)
                    , Data.Vector.Mutable.MVector s (Matrix r) )
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
  storeL <- VM.replicate dimL (fromRows [] :: Matrix r)  -- dummy value
  intMapV <- newSTRef IM.empty
  intMapL <- newSTRef IM.empty
  -- This is probably not worth optimizing further, e.g., reusing the same
  -- three parameter vectors (only the initial portion of @store@ for scalars)
  -- or updating in-place inside vectors and matrices. Experiments indicate
  -- that allocation and runtime gains of the latter optimization are
  -- a few percent (because the vector and matrix arithmetic's in the forward
  -- pass are done immutably anyway), and for both optimizations, any thunk
  -- pointing inside the mutated vectors can easily be catastrophic.
  -- Maintaining this brittle optimization would also make harder any future
  -- parallelization, whether on CPU or GPU.
  --
  -- OTOH, removing @storeV@ and @storeL@ increases GC for vector-based
  -- MNIST500x500 by half, so let's keep them. Probably CPU manages cache better
  -- when vectors are stored in a (mutable?) vector, not a tree spread
  -- all around the heap. For few but very long vectors this may not matter
  -- much, though.
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
      addToMatrix i o = let r = convertMatrixOuter o
                            addToStore v = if rows v <= 0 then r else v + r
                            addToIntMap (Just v) = Just $ v + r
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
        Dot vr vd -> evalV (Numeric.LinearAlgebra.scale r vr) vd
        SumElements vd n -> evalV (konst r n) vd
        Konst{} -> error "buildVector: Konst can't result in a scalar"
        Seq{} -> error "buildVector: Seq can't result in a scalar"
        Index d i n -> evalV (konst 0 n V.// [(i, r)]) d
        DotL{} -> error "buildVector: DotL can't result in a scalar"
        DotRowL{} -> error "buildVector: DotRowL can't result in a scalar"
        KonstL{} -> error "buildVector: KonstL can't result in a scalar"
        SeqL{} -> error "buildVector: SeqL can't result in a scalar"
      evalV :: Vector r -> Delta (Vector r) -> ST s ()
      evalV !r = \case
        Zero -> return ()
        Scale k d -> evalV (k * r) d
        Add d1 d2 -> evalV r d1 >> evalV r d2
        Var (DeltaId i) -> addToVector i r
        Dot{} -> error "buildVector: unboxed vectors of vectors not possible"
        SumElements{} ->
          error "buildVector: unboxed vectors of vectors not possible"
        Konst d -> V.mapM_ (`eval` d) r
        Seq vd -> V.imapM_ (\i d -> eval (r V.! i) d) vd
        Index{} -> error "buildVector: unboxed vectors of vectors not possible"
        DotL mr md ->
          let !m = asColumn r * mr
          in evalL (MatrixOuter (Just m) Nothing) md
          -- this @asColumn@ interacted disastrously with @mr = asRow v@
          -- in @(#>!)@, each causing an allocation of a whole new @n^2@ matrix
          -- and then a third with their outer product;
          -- when doing the same computation by hand using @Vector@
          -- instead of @Matrix@, we can avoid even a single matrix allocation;
          -- the cost for the manual computation is many extra delta
          -- expressions which, however, with square enough matrices,
          -- don't dominate
        DotRowL row md -> evalL (MatrixOuter Nothing (Just (r, row))) md
          -- this is a way to alleviate the ephemeral matrices problem,
          -- by polluting the API with the detail about the shape
          -- of the passed array (the replicated row shape),
          -- which eliminates two of the three matrix allocations;
      evalL :: MatrixOuter r -> Delta (Matrix r) -> ST s ()
      evalL !r@(MatrixOuter mm mcr) = \case
        Zero -> return ()
        Scale k d ->
          let !m = maybe k (k *) mm
          in evalL (MatrixOuter (Just m) mcr) d
        Add d1 d2 -> evalL r d1 >> evalL r d2
        Var (DeltaId i) -> addToMatrix i r
        Dot{} -> error "buildVector: unboxed vectors of vectors not possible"
        SumElements{} ->
          error "buildVector: unboxed vectors of vectors not possible"
        Index{} -> error "buildVector: unboxed vectors of vectors not possible"
        KonstL d -> mapM_ (`evalV` d) (toRows $ convertMatrixOuter r)
        SeqL md -> zipWithM_ evalV (toRows $ convertMatrixOuter r) (V.toList md)
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
          unless (rows r <= 0) $
            evalL (MatrixOuter (Just r) Nothing) d
        else do
          mr <- IM.lookup i <$> readSTRef intMapL
          maybe (pure ()) (\ !r -> evalL (MatrixOuter (Just r) Nothing) d) mr
        return $! DeltaId (pred i)
  minusOne <- foldM evalUnlessZero (DeltaId $ pred storeSize) (deltaBindings st)
  let _A = assert (minusOne == DeltaId (-1)) ()
  return (VM.slice 0 dim store, storeV, storeL)

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
    return (r, rV, rL)
