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
import           Control.Monad (foldM, when, zipWithM_)
import           Control.Monad.ST.Strict (ST, runST)
import           Data.Kind (Type)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           Numeric.LinearAlgebra
  (Matrix, Numeric, Vector, asColumn, fromRows, outer, rows, toRows)
import qualified Numeric.LinearAlgebra

data Delta :: Type -> Type where
  Zero :: Delta a
  Scale :: a -> Delta a -> Delta a
  Add :: Delta a -> Delta a -> Delta a
  Var :: DeltaId -> Delta a
  Dot :: Vector r -> Delta (Vector r) -> Delta r
  Konst :: Delta r -> Delta (Vector r)
  Seq :: Data.Vector.Vector (Delta r) -> Delta (Vector r)
  DotL :: Matrix r -> Delta (Matrix r) -> Delta (Vector r)
  DotRowL :: Vector r -> Delta (Matrix r) -> Delta (Vector r)
  KonstL :: Delta (Vector r) -> Delta (Matrix r)
  SeqL :: Data.Vector.Vector (Delta (Vector r)) -> Delta (Matrix r)

newtype DeltaId = DeltaId Int
  deriving (Show, Eq, Ord)

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
  -- This is relatively very cheap allocation, so no problem even when most
  -- parameters and vars are not scalars:
  store <- VM.replicate storeSize 0
  -- TODO: this is probably not a safe asumption (it would be clearly wrong
  -- for scalars) and, regardless, should be communicated to the user:
  -- These allocations are very expensive, so let's try to avoid them.
  -- If no vector parameters, assume there will be no vector vars.
  -- If no vector parameters, assume there will be no matrix vars.
  storeV <- VM.replicate (if dimV == 0 then 0 else storeSize - dim)
                         (V.empty :: Vector r)
  storeL <- VM.replicate (if dimL == 0 then 0 else storeSize - dimSV)
                         (fromRows [] :: Matrix r)
  let eval :: r -> Delta r -> ST s ()
      eval !r = \case
        Zero -> return ()
        Scale k d -> eval (k * r) d
        Add d1 d2 -> eval r d1 >> eval r d2
        Var (DeltaId i) -> VM.modify store (+ r) i
        Dot vr vd -> evalV (Numeric.LinearAlgebra.scale r vr) vd
        Konst{} -> error "buildVector: Konst can't result in a scalar"
        Seq{} -> error "buildVector: Seq can't result in a scalar"
        DotL{} -> error "buildVector: DotL can't result in a scalar"
        DotRowL{} -> error "buildVector: DotRowL can't result in a scalar"
        KonstL{} -> error "buildVector: KonstL can't result in a scalar"
        SeqL{} -> error "buildVector: SeqL can't result in a scalar"
      evalV :: Vector r -> Delta (Vector r) -> ST s ()
      evalV !r = \case
        Zero -> return ()
        Scale k d -> evalV (k * r) d
        Add d1 d2 -> evalV r d1 >> evalV r d2
        Var (DeltaId i) -> let addToVector v = if V.null v then r else v + r
                           in VM.modify storeV addToVector (i - dim)
        Dot{} -> error "buildVector: unboxed vectors of vectors not possible"
        Konst d -> V.mapM_ (`eval` d) r
        Seq vd -> V.imapM_ (\i d -> eval (r V.! i) d) vd
        DotL mr md -> evalL (asColumn r * mr) md
          -- this @asColumn@ interacted disastrously with @mr = asRow v@
          -- in @(#>!)@, each causing an allocation of a whole new @n^2@ matrix
          -- and then a third with their outer product;
          -- when doing the same computation by hand using @Vector@
          -- instead of @Matrix@, we can avoid even a single matrix allocation;
          -- the cost for the manual computation is many extra delta
          -- expressions which, however, with square enough matrices,
          -- don't dominate
        DotRowL row md -> evalL (r `outer` row) md
          -- this is a way to alleviate the ephemeral matrices problem,
          -- by polluting the API with the detail about the shape
          -- of the passed array (the replicated row shape),
          -- which eliminates two of the three matrix allocations;
          -- we could do even better keeping such matrices unevaluated
          -- and we could sometimes get away with modifying only the vectors
          -- but, e.g., @Scale@ forces allocation of a whole matrix regardless
      evalL :: Matrix r -> Delta (Matrix r) -> ST s ()
      evalL !r = \case
        Zero -> return ()
        Scale k d -> evalL (k * r) d
        Add d1 d2 -> evalL r d1 >> evalL r d2
        Var (DeltaId i) -> let addToMatrix m = if rows m <= 0 then r else m + r
                           in VM.modify storeL addToMatrix (i - dimSV)
        Dot{} -> error "buildVector: unboxed vectors of vectors not possible"
        KonstL d -> mapM_ (`evalV` d) (toRows r)
        SeqL md -> zipWithM_ evalV (toRows r) (V.toList md)
  eval 1 d0  -- dt is 1 or hardwired in f
  let evalUnlessZero :: DeltaId -> DeltaBinding r -> ST s DeltaId
      evalUnlessZero (DeltaId !i) (DScalar d) = do
        r <- store `VM.read` i
        when (r /= 0) $  -- we init with exactly 0 above so the comparison is OK
          eval r d
        return $! DeltaId (pred i)
      evalUnlessZero (DeltaId !i) (DVector d) = do
        r <- storeV `VM.read` (i - dim)
        when (not $ V.null r) $
          evalV r d
        return $! DeltaId (pred i)
      evalUnlessZero (DeltaId !i) (DMatrix d) = do
        r <- storeL `VM.read` (i - dimSV)
        when (rows r > 0) $
          evalL r d
        return $! DeltaId (pred i)
  minusOne <- foldM evalUnlessZero (DeltaId $ pred storeSize) (deltaBindings st)
  let _A = assert (minusOne == DeltaId (-1)) ()
  return ( VM.slice 0 dim store
         , VM.slice 0 dimV storeV
         , VM.slice 0 dimL storeL )

evalBindings :: forall r. (Eq r, Numeric r, Num (Vector r))
             => Int -> Int -> Int -> DeltaState r -> Delta r
             -> ( Vector r
                , Data.Vector.Vector (Vector r)
                , Data.Vector.Vector (Matrix r) )
evalBindings dim dimV dimL st d0 =
  -- We can't just call @V.create@ thrice, because it would run
  -- the @ST@ action thrice.
  runST $ do
    (res, resV, resL) <- buildVector dim dimV dimL st d0
    r <- V.unsafeFreeze res
    rV <- V.unsafeFreeze resV
    rL <- V.unsafeFreeze resL
    return (r, rV, rL)
