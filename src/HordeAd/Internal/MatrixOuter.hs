{-# LANGUAGE FlexibleContexts #-}
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
  , nullMatrixOuter, convertMatrixOuter, toRowsMatrixOuter, plusMatrixOuter
  ) where

import Prelude

import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra
  (Matrix, Numeric, Vector, asColumn, asRow, outer, toRows)
import qualified Numeric.LinearAlgebra

-- | A representation of a matrix as a product of a basic matrix
-- and an outer product of two vectors. Each component defaults to ones.
data MatrixOuter r = MatrixOuter (Maybe (Matrix r))
                                 (Maybe (Vector r)) (Maybe (Vector r))

nullMatrixOuter :: (MatrixOuter r) -> Bool
nullMatrixOuter (MatrixOuter Nothing Nothing Nothing) = True
nullMatrixOuter _ = False

convertMatrixOuter :: (Numeric r, Num (Vector r)) => MatrixOuter r -> Matrix r
convertMatrixOuter (MatrixOuter (Just m) Nothing Nothing) = m
convertMatrixOuter (MatrixOuter (Just m) (Just c) Nothing) = m * asColumn c
  -- beware, depending on context, @m * outer c (konst 1 (cols m))@
  -- may allocate much less and perhaps @fromRows . toRowsMatrixOuter@
  -- may be even better; that's probably vector being picky about fusing;
  -- it doesn't matter if @m@ comes first
convertMatrixOuter (MatrixOuter (Just m) Nothing (Just r)) = m * asRow r
convertMatrixOuter (MatrixOuter (Just m) (Just c) (Just r)) = m * outer c r
convertMatrixOuter (MatrixOuter Nothing (Just c) (Just r)) = outer c r
convertMatrixOuter _ =
  error "convertMatrixOuter: dimensions can't be determined"

toRowsMatrixOuter :: (Numeric r, Num (Vector r)) => MatrixOuter r -> [Vector r]
toRowsMatrixOuter (MatrixOuter (Just m) Nothing Nothing) = toRows m
toRowsMatrixOuter (MatrixOuter (Just m) mc Nothing) =
  maybe id
        (\c -> zipWith (\s row -> Numeric.LinearAlgebra.scale s row)
                       (V.toList c))
        mc
  $ toRows m
toRowsMatrixOuter (MatrixOuter (Just m) mc (Just r)) =
  maybe (map (r *))
        (\c -> zipWith (\s row -> r * Numeric.LinearAlgebra.scale s row)
                       (V.toList c))
        mc
  $ toRows m
toRowsMatrixOuter (MatrixOuter Nothing (Just c) (Just r)) =
  map (`Numeric.LinearAlgebra.scale` r) $ V.toList c
toRowsMatrixOuter _ =
  error "toRowsMatrixOuter: dimensions can't be determined"

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
