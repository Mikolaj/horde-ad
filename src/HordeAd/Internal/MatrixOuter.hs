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
  , emptyMatrixOuter, nullMatrixOuter, rows, cols
  , convertMatrixOuter, convertMatrixOuterOrNull
  , toRows, toColumns, plus, multiplyWithOuter
  , konst, asRow, asColumn, rowAppend, columnAppend
  , takeRows, takeColumns, dropRows, dropColumns
  , transpose, matMul, flipud, fliprl
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Data.Maybe (fromJust)
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA

-- | A representation of a matrix as a product of a basic matrix
-- and an outer product of two vectors. Each component defaults to ones.
data MatrixOuter r = MatrixOuter (Maybe (Matrix r))
                                 (Maybe (Vector r)) (Maybe (Vector r))

emptyMatrixOuter :: MatrixOuter r
emptyMatrixOuter = MatrixOuter Nothing Nothing Nothing

nullMatrixOuter :: MatrixOuter r -> Bool
nullMatrixOuter (MatrixOuter Nothing Nothing Nothing) = True
nullMatrixOuter _ = False

rows :: Numeric r => MatrixOuter r -> Int
rows (MatrixOuter (Just m) _ _) = LA.rows m
rows (MatrixOuter Nothing (Just c) _) = V.length c
rows _ = error "rows: dimensions can't be determined"

cols :: Numeric r => MatrixOuter r -> Int
cols (MatrixOuter (Just m) _ _) = LA.cols m
cols (MatrixOuter Nothing _ (Just r)) = V.length r
cols _ = error "cols: dimensions can't be determined"

convertMatrixOuter :: (Numeric r, Num (Vector r)) => MatrixOuter r -> Matrix r
convertMatrixOuter (MatrixOuter (Just m) Nothing Nothing) = m
convertMatrixOuter (MatrixOuter (Just m) (Just c) Nothing) = m * LA.asColumn c
  -- This @asColumn@ is safe, because it's expanded via @m@.
  --
  -- Beware, depending on context, @m * outer c (konst 1 (cols m))@
  -- may allocate much less and perhaps @fromRows . toRowsMatrixOuter@
  -- may be even better; that's probably vector being picky about fusing.
  -- It doesn't matter if @m@ comes first.
convertMatrixOuter (MatrixOuter (Just m) Nothing (Just r)) = m * LA.asRow r
  -- This @asRow@ is safe, because it's expanded via @m@.
convertMatrixOuter (MatrixOuter (Just m) (Just c) (Just r)) = m * LA.outer c r
convertMatrixOuter (MatrixOuter Nothing (Just c) (Just r)) = LA.outer c r
convertMatrixOuter _ =
  error "convertMatrixOuter: dimensions can't be determined"

convertMatrixOuterOrNull :: (Numeric r, Num (Vector r))
                         => MatrixOuter r -> Matrix r
convertMatrixOuterOrNull (MatrixOuter Nothing Nothing Nothing) = LA.fromRows []
convertMatrixOuterOrNull m = convertMatrixOuter m

toRows :: (Numeric r, Num (Vector r)) => MatrixOuter r -> [Vector r]
toRows (MatrixOuter (Just m) Nothing Nothing) = LA.toRows m
toRows (MatrixOuter (Just m) mc Nothing) =
  maybe id (zipWith LA.scale . V.toList) mc $ LA.toRows m
toRows (MatrixOuter (Just m) mc (Just r)) =
  maybe (map (r *)) (zipWith (\s row -> r * LA.scale s row) . V.toList) mc
  $ LA.toRows m
toRows (MatrixOuter Nothing (Just c) (Just r)) =
  map (`LA.scale` r) $ V.toList c
toRows _ = error "toRows: dimensions can't be determined"

toColumns :: (Numeric r, Num (Vector r)) => MatrixOuter r -> [Vector r]
toColumns (MatrixOuter (Just m) Nothing Nothing) = LA.toColumns m
toColumns (MatrixOuter (Just m) Nothing mr) =
  maybe id (zipWith LA.scale . V.toList) mr $ LA.toColumns m
toColumns (MatrixOuter (Just m) (Just c) mr) =
-- traceShow (sizeMatrixOuter (MatrixOuter (Just m) (Just c) mr)) $
  maybe (map (c *)) (zipWith (\s col -> c * LA.scale s col) . V.toList) mr
  $ LA.toColumns m
toColumns (MatrixOuter Nothing (Just c) (Just r)) =
  map (`LA.scale` c) $ V.toList r
toColumns _ = error "toColumns: dimensions can't be determined"

size :: Numeric r => MatrixOuter r -> (Maybe (Int, Int), Maybe Int, Maybe Int)
size (MatrixOuter mm mc mr) = (LA.size <$> mm, LA.size <$> mc, LA.size <$> mr)

plus :: (Numeric r, Num (Vector r))
     => MatrixOuter r -> MatrixOuter r -> MatrixOuter r
plus o1 o2 =
  let !o = convertMatrixOuter o1 + convertMatrixOuter o2
  in MatrixOuter (Just o) Nothing Nothing
    -- TODO: Here we allocate up to 5 matrices, but we should allocate one
    -- and in-place add to it and multiply it, etc., ideally using raw FFI
    -- or at least vector streams/bundles; an easy option to have only
    -- one allocation is to do this pointwise, but then the speedup, if any,
    -- from blas/lapack does not apply

multiplyWithOuter :: (Numeric r, Num (Vector r))
                  => Matrix r -> MatrixOuter r -> MatrixOuter r
multiplyWithOuter k o@(MatrixOuter mm mc mr) =
  assert (LA.size k
          == maybe (LA.size $ fromJust mc, LA.size $ fromJust mr) LA.size mm
         `blame` (LA.size k, size o)) $
  let !m = maybe k (k *) mm
  in MatrixOuter (Just m) mc mr

konst :: Numeric r => r -> Int -> Int -> MatrixOuter r
konst x nrows ncols =
  let !c = LA.konst x nrows
      !r = LA.konst x ncols
  in MatrixOuter Nothing (Just c) (Just r)

asRow :: Numeric r => Vector r -> Int -> MatrixOuter r
asRow !r nrows =
  let !c = LA.konst 1 nrows
  in MatrixOuter Nothing (Just c) (Just r)

asColumn :: Numeric r => Vector r -> Int -> MatrixOuter r
asColumn !c ncols =
  let !r = LA.konst 1 ncols
  in MatrixOuter Nothing (Just c) (Just r)

rowAppend :: (Numeric r, Num (Vector r))
          => MatrixOuter r -> MatrixOuter r -> MatrixOuter r
rowAppend o1 o2 =
  let !o = convertMatrixOuter o1 LA.=== convertMatrixOuter o2
  in MatrixOuter (Just o) Nothing Nothing

columnAppend :: (Numeric r, Num (Vector r))
             => MatrixOuter r -> MatrixOuter r -> MatrixOuter r
columnAppend o1 o2 =
  let !o = convertMatrixOuter o1 LA.||| convertMatrixOuter o2
  in MatrixOuter (Just o) Nothing Nothing

takeRows :: Numeric r => Int -> MatrixOuter r -> MatrixOuter r
takeRows k (MatrixOuter mm mc mr) =
  MatrixOuter (LA.takeRows k <$> mm)
              (V.take k <$> mc)
              mr

takeColumns :: Numeric r => Int -> MatrixOuter r -> MatrixOuter r
takeColumns k (MatrixOuter mm mc mr) =
  MatrixOuter (LA.takeColumns k <$> mm)
              mc
              (V.take k <$> mr)

dropRows :: Numeric r => Int -> MatrixOuter r -> MatrixOuter r
dropRows k (MatrixOuter mm mc mr) =
  MatrixOuter (LA.dropRows k <$> mm)
              (V.drop k <$> mc)
              mr

dropColumns :: Numeric r => Int -> MatrixOuter r -> MatrixOuter r
dropColumns k (MatrixOuter mm mc mr) =
  MatrixOuter (LA.dropColumns k <$> mm)
              mc
              (V.drop k <$> mr)

transpose :: Numeric r => MatrixOuter r -> MatrixOuter r
transpose (MatrixOuter mm mc mr) = MatrixOuter (LA.tr' <$> mm) mr mc

matMul :: (Numeric r, Num (Vector r))
       => MatrixOuter r -> MatrixOuter r -> MatrixOuter r
matMul m1 m2 =
  MatrixOuter (Just $ convertMatrixOuter m1 LA.<> convertMatrixOuter m2)
              Nothing Nothing

flipud :: Numeric r => MatrixOuter r -> MatrixOuter r
flipud (MatrixOuter mm mc mr) =
  MatrixOuter (LA.flipud <$> mm) mr (V.reverse <$> mc)

fliprl :: Numeric r => MatrixOuter r -> MatrixOuter r
fliprl (MatrixOuter mm mc mr) =
  MatrixOuter (LA.fliprl <$> mm) (V.reverse <$> mr) mc
