-- | An ad-hoc representation of matrices that saves allocations
-- and speeds up computing gradients. The major improvement comes
-- from avoiding, often, the construction of some matrices,
-- e.g., outer products or repeated columns that naturally occur
-- in delta-expressions. Minor improvements come from better fusion
-- (via vector or hmatrix/blas/lapack) and so less allocation
-- of intermediate matrix results of arithmetic and other operations.
--
-- The latter improvements are very likely tied to the vagaries
-- of hmatrix (or, less likely, vector or blas/lapack) that work underneath
-- and apparently conspire to fuse some matrix operations but not others.
-- That would explain why vector-based MNIST nn allocates not much less
-- than matrix-based MNIST, despite producing much larger delta-expressions.
-- Matrix operations probably fuse worse, even though they are really
-- vector operations on the underlying vector representation,
-- because the dimensions book-keeping of the matrix comes in the way
-- and also because some operations work on columns, against the grain
-- of the representation.
--
-- For fully connected MNIST nns 10 times larger than usual, vector-based
-- implementation allocates similarly and runs faster than matrix-based,
-- despite the latter spending 8 times less in GC. probably because
-- matrices don't fit in cache at this size and vectors still do.
module HordeAd.Internal.MatrixOuter
  ( MatrixOuter (..)
  , emptyMatrixOuter, nullMatrixOuter
  , convertMatrixOuter, convertMatrixOuterOrNull
  , toRowsMatrixOuter, toColumnsMatrixOuter
  , plusMatrixOuter, multiplyMatrixNormalAndOuter
  , konstMatrixOuter, asRowMatrixOuter, asColumnMatrixOuter
  , rowAppendMatrixOuter, columnAppendMatrixOuter
  , takeRowsMatrixOuter, takeColumnsMatrixOuter
  , dropRowsMatrixOuter, dropColumnsMatrixOuter
  , transposeMatrixOuter
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Data.Maybe (fromJust)
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

-- | A representation of a matrix as a product of a basic matrix
-- and an outer product of two vectors. Each component defaults to ones.
data MatrixOuter r = MatrixOuter (Maybe (Matrix r))
                                 (Maybe (Vector r)) (Maybe (Vector r))

emptyMatrixOuter :: MatrixOuter r
emptyMatrixOuter = MatrixOuter Nothing Nothing Nothing

nullMatrixOuter :: MatrixOuter r -> Bool
nullMatrixOuter (MatrixOuter Nothing Nothing Nothing) = True
nullMatrixOuter _ = False

convertMatrixOuter :: (Numeric r, Num (Vector r)) => MatrixOuter r -> Matrix r
convertMatrixOuter (MatrixOuter (Just m) Nothing Nothing) = m
convertMatrixOuter (MatrixOuter (Just m) (Just c) Nothing) =
  m * HM.asColumn c  -- this @asColumn@ is safe, because it's expanded via @m@
    -- beware, depending on context, @m * outer c (konst 1 (cols m))@
    -- may allocate much less and perhaps @fromRows . toRowsMatrixOuter@
    -- may be even better; that's probably vector being picky about fusing;
    -- it doesn't matter if @m@ comes first
convertMatrixOuter (MatrixOuter (Just m) Nothing (Just r)) =
  m * HM.asRow r  -- this @asRow@ is safe, because it's expanded via @m@
convertMatrixOuter (MatrixOuter (Just m) (Just c) (Just r)) = m * HM.outer c r
convertMatrixOuter (MatrixOuter Nothing (Just c) (Just r)) = HM.outer c r
convertMatrixOuter _ =
  error "convertMatrixOuter: dimensions can't be determined"

convertMatrixOuterOrNull
  :: (Numeric r, Num (Vector r)) => MatrixOuter r -> Matrix r
convertMatrixOuterOrNull (MatrixOuter Nothing Nothing Nothing) = HM.fromRows []
convertMatrixOuterOrNull m = convertMatrixOuter m

toRowsMatrixOuter :: (Numeric r, Num (Vector r)) => MatrixOuter r -> [Vector r]
toRowsMatrixOuter (MatrixOuter (Just m) Nothing Nothing) = HM.toRows m
toRowsMatrixOuter (MatrixOuter (Just m) mc Nothing) =
  maybe id (zipWith HM.scale . V.toList) mc $ HM.toRows m
toRowsMatrixOuter (MatrixOuter (Just m) mc (Just r)) =
  maybe (map (r *)) (zipWith (\s row -> r * HM.scale s row) . V.toList) mc
  $ HM.toRows m
toRowsMatrixOuter (MatrixOuter Nothing (Just c) (Just r)) =
  map (`HM.scale` r) $ V.toList c
toRowsMatrixOuter _ =
  error "toRowsMatrixOuter: dimensions can't be determined"

toColumnsMatrixOuter :: (Numeric r, Num (Vector r))
                     => MatrixOuter r -> [Vector r]
toColumnsMatrixOuter (MatrixOuter (Just m) Nothing Nothing) = HM.toColumns m
toColumnsMatrixOuter (MatrixOuter (Just m) Nothing mr) =
  maybe id (zipWith HM.scale . V.toList) mr $ HM.toColumns m
toColumnsMatrixOuter (MatrixOuter (Just m) (Just c) mr) =
-- traceShow (sizeMatrixOuter (MatrixOuter (Just m) (Just c) mr)) $
  maybe (map (c *)) (zipWith (\s col -> c * HM.scale s col) . V.toList) mr
  $ HM.toColumns m
toColumnsMatrixOuter (MatrixOuter Nothing (Just c) (Just r)) =
  map (`HM.scale` c) $ V.toList r
toColumnsMatrixOuter _ =
  error "toColumnsMatrixOuter: dimensions can't be determined"

sizeMatrixOuter :: Numeric r
                => MatrixOuter r -> (Maybe (Int, Int), Maybe Int, Maybe Int)
sizeMatrixOuter (MatrixOuter mm mc mr) =
  (HM.size <$> mm, HM.size <$> mc, HM.size <$> mr)

plusMatrixOuter :: (Numeric r, Num (Vector r))
                => MatrixOuter r -> MatrixOuter r -> MatrixOuter r
plusMatrixOuter o1 o2 =
  let !o = convertMatrixOuter o1 + convertMatrixOuter o2
  in MatrixOuter (Just o) Nothing Nothing
    -- TODO: Here we allocate up to 5 matrices, but we should allocate one
    -- and in-place add to it and multiply it, etc., ideally using raw FFI
    -- or at least vector streams/bundles; an easy option to have only
    -- one allocation is to do this pointwise, but then the speedup, if any,
    -- from blas/lapack does not apply

multiplyMatrixNormalAndOuter :: (Numeric r, Num (Vector r))
                             => Matrix r -> MatrixOuter r -> MatrixOuter r
multiplyMatrixNormalAndOuter k o@(MatrixOuter mm mc mr) =
  assert
    (HM.size k
     == maybe (HM.size $ fromJust mc, HM.size $ fromJust mr) HM.size mm
     `blame` (HM.size k, sizeMatrixOuter o)) $
  let !m = maybe k (k *) mm
  in MatrixOuter (Just m) mc mr

konstMatrixOuter :: Numeric r => r -> Int -> Int -> MatrixOuter r
konstMatrixOuter x nrows ncols =
  let !c = HM.konst x nrows
      !r = HM.konst x ncols
  in MatrixOuter Nothing (Just c) (Just r)

asRowMatrixOuter :: Numeric r => Vector r -> Int -> MatrixOuter r
asRowMatrixOuter !r nrows =
  let !c = HM.konst 1 nrows
  in MatrixOuter Nothing (Just c) (Just r)

asColumnMatrixOuter :: Numeric r => Vector r -> Int -> MatrixOuter r
asColumnMatrixOuter !c ncols =
  let !r = HM.konst 1 ncols
  in MatrixOuter Nothing (Just c) (Just r)

rowAppendMatrixOuter :: (Numeric r, Num (Vector r))
                     => MatrixOuter r -> MatrixOuter r -> MatrixOuter r
rowAppendMatrixOuter o1 o2 =
  let !o = convertMatrixOuter o1 HM.=== convertMatrixOuter o2
  in MatrixOuter (Just o) Nothing Nothing

columnAppendMatrixOuter :: (Numeric r, Num (Vector r))
                        => MatrixOuter r -> MatrixOuter r -> MatrixOuter r
columnAppendMatrixOuter o1 o2 =
  let !o = convertMatrixOuter o1 HM.||| convertMatrixOuter o2
  in MatrixOuter (Just o) Nothing Nothing

takeRowsMatrixOuter :: Numeric r => Int -> MatrixOuter r -> MatrixOuter r
takeRowsMatrixOuter k (MatrixOuter mm mc mr) =
  MatrixOuter (HM.takeRows k <$> mm)
              (V.take k <$> mc)
              mr

takeColumnsMatrixOuter :: Numeric r => Int -> MatrixOuter r -> MatrixOuter r
takeColumnsMatrixOuter k (MatrixOuter mm mc mr) =
  MatrixOuter (HM.takeColumns k <$> mm)
              mc
              (V.take k <$> mr)

dropRowsMatrixOuter :: Numeric r => Int -> MatrixOuter r -> MatrixOuter r
dropRowsMatrixOuter k (MatrixOuter mm mc mr) =
  MatrixOuter (HM.dropRows k <$> mm)
              (V.drop k <$> mc)
              mr

dropColumnsMatrixOuter :: Numeric r => Int -> MatrixOuter r -> MatrixOuter r
dropColumnsMatrixOuter k (MatrixOuter mm mc mr) =
  MatrixOuter (HM.dropColumns k <$> mm)
              mc
              (V.drop k <$> mr)

transposeMatrixOuter :: Numeric r => MatrixOuter r -> MatrixOuter r
transposeMatrixOuter (MatrixOuter mm mc mr) = MatrixOuter (HM.tr' <$> mm) mr mc
