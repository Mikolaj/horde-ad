{-# LANGUAGE AllowAmbiguousTypes, DataKinds, FunctionalDependencies,
             TypeFamilies, TypeOperators, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-missing-methods #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Dual numbers and various operations on them, arithmetic and related
-- to tensors (vectors, matrices and others).
module HordeAd.Core.DualNumber where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.Dynamic as OTB
import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.List.Index (imap)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Vector, (#>), (<.>))
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Core.DualClass

-- * The main dual number types

data DualNumber a = D (Primal a) a

class (IsScalar r, Monad m, Functor m, Applicative m)
      => DualMonad r m | m -> r where
  returnLet :: IsDualWithScalar a r
            => DualNumber a -> m (DualNumber a)

type Domain0 r = Vector (Primal r)

type Domain1 r = Data.Vector.Vector (Primal (Tensor1 r))

type Domain2 r = Data.Vector.Vector (Primal (Tensor2 r))

type DomainX r = Data.Vector.Vector (Primal (TensorX r))

type Domains r = (Domain0 r, Domain1 r, Domain2 r, DomainX r)


-- * General non-monadic operations, for any scalar rank

-- This instances are required by the @Real@ instance, which is required
-- by @RealFloat@, which gives @atan2@. No idea what properties
-- @Real@ requires here, so let it crash if it's really needed.
instance Eq (DualNumber r) where

instance Ord (DualNumber r) where

-- These instances are dangerous. Expressions should be wrapped in
-- the monadic @returnLet@ whenever there is a possibility they can be
-- used multiple times in a larger expression. Safer yet, monadic arithmetic
-- operations that already include @returnLet@ should be used instead,
-- such as @+\@, @*\@, etc.
--
-- @Num (Primal r)@ forces @UndecidableInstances@.
instance (Num (Primal r), IsDual r) => Num (DualNumber r) where
  D u u' + D v v' = D (u + v) (dAdd u' v')
  D u u' - D v v' = D (u - v) (dAdd u' (dScale (-1) v'))
  D u u' * D v v' = D (u * v) (dAdd (dScale v u') (dScale u v'))
  negate (D v v') = D (- v) (dScale (-1) v')
  abs = undefined  -- TODO
  signum = undefined  -- TODO
  fromInteger = scalar . fromInteger

instance (Real (Primal r), IsDual r) => Real (DualNumber r) where
  toRational = undefined  -- TODO?

instance (Fractional (Primal r), IsDual r) => Fractional (DualNumber r) where
  D u u' / D v v' =
    let recipSq = recip (v * v)
    in D (u / v) (dAdd (dScale (v * recipSq) u') (dScale (- u * recipSq) v'))
  recip (D v v') =
    let minusRecipSq = - recip (v * v)
    in D (recip v) (dScale minusRecipSq v')
  fromRational = scalar . fromRational

instance (Floating (Primal r), IsDual r) => Floating (DualNumber r) where
  pi = scalar pi
  exp (D u u') = let expU = exp u
                 in D expU (dScale expU u')
  log (D u u') = D (log u) (dScale (recip u) u')
  sqrt = undefined  -- TODO
  D u u' ** D v v' = D (u ** v) (dAdd (dScale (v * (u ** (v - 1))) u')
                                      (dScale ((u ** v) * log u) v'))
  logBase = undefined  -- TODO
  sin (D u u') = D (sin u) (dScale (cos u) u')
  cos (D u u') = D (cos u) (dScale (- (sin u)) u')
  tan = undefined  -- TODO
  asin = undefined  -- TODO
  acos = undefined  -- TODO
  atan = undefined  -- TODO
  sinh = undefined  -- TODO
  cosh = undefined  -- TODO
  tanh (D u u') = let y = tanh u
                  in D y (dScale (1 - y * y) u')
  asinh = undefined  -- TODO
  acosh = undefined  -- TODO
  atanh = undefined  -- TODO

instance (RealFrac (Primal r), IsDual r) => RealFrac (DualNumber r) where
  properFraction = undefined
    -- very low priority, since these are all extremely not continuous

instance (RealFloat (Primal r), IsDual r) => RealFloat (DualNumber r) where
  atan2 (D u u') (D v v') =
    let t = 1 / (u * u + v * v)
    in D (atan2 u v) (dAdd (dScale (- u * t) v') (dScale (v * t) u'))
      -- we can be selective here and omit the other methods,
      -- most of which don't even have a differentiable codomain

scalar :: IsDual a => Primal a -> DualNumber a
scalar a = D a dZero

scale :: (Num (Primal a), IsDual a) => Primal a -> DualNumber a -> DualNumber a
scale a (D u u') = D (a * u) (dScale a u')


-- * Non-monadic operations resulting in a scalar

sumElements0 :: IsScalar r => DualNumber (Tensor1 r) -> DualNumber r
sumElements0 (D u u') = D (HM.sumElements u) (dSumElements0 u' (V.length u))

index0 :: IsScalar r => DualNumber (Tensor1 r) -> Int -> DualNumber r
index0 (D u u') ix = D (u V.! ix) (dIndex0 u' ix (V.length u))

minimum0 :: IsScalar r => DualNumber (Tensor1 r) -> DualNumber r
minimum0 (D u u') =
  D (HM.minElement u) (dIndex0 u' (HM.minIndex u) (V.length u))

maximum0 :: IsScalar r => DualNumber (Tensor1 r) -> DualNumber r
maximum0 (D u u') =
  D (HM.maxElement u) (dIndex0 u' (HM.maxIndex u) (V.length u))

-- If @v'@ is a @Var1@, this is much faster due to the optimization
-- in @Index0@.
foldl'0 :: IsScalar r
        => (DualNumber r -> DualNumber r -> DualNumber r)
        -> DualNumber r -> DualNumber (Tensor1 r)
        -> DualNumber r
foldl'0 f uu' (D v v') =
  let k = V.length v
      g !acc ix p = f (D p (dIndex0 v' ix k)) acc
  in V.ifoldl' g uu' v

altSumElements0 :: IsScalar r => DualNumber (Tensor1 r) -> DualNumber r
altSumElements0 = foldl'0 (+) 0

-- | Dot product.
infixr 8 <.>!
(<.>!) :: IsScalar r
       => DualNumber (Tensor1 r) -> DualNumber (Tensor1 r) -> DualNumber r
(<.>!) (D u u') (D v v') = D (u <.> v) (dAdd (dDot0 v u') (dDot0 u v'))

-- | Dot product with a constant vector.
infixr 8 <.>!!
(<.>!!) :: IsScalar r
        => DualNumber (Tensor1 r) -> Primal (Tensor1 r) -> DualNumber r
(<.>!!) (D u u') v = D (u <.> v) (dDot0 v u')

fromX0 :: IsScalar r => DualNumber (TensorX r) -> DualNumber r
fromX0 (D u u') = D (OT.unScalar u) (dFromX0 u')

fromS0 :: IsScalarS '[] r => DualNumber (TensorS '[] r) -> DualNumber r
fromS0 (D u u') = D (OS.unScalar u) (dFromS0 u')


-- * Non-monadic operations resulting in a vector

-- @1@ means rank one, so the dual component represents a vector.
seq1 :: IsScalar r
     => Data.Vector.Vector (DualNumber r) -> DualNumber (Tensor1 r)
seq1 v = D (V.convert $ V.map (\(D u _) -> u) v)  -- I hope this fuses
           (dSeq1 $ V.map (\(D _ u') -> u') v)

konst1 :: IsScalar r => DualNumber r -> Int -> DualNumber (Tensor1 r)
konst1 (D u u') n = D (HM.konst u n) (dKonst1 u' n)

append1 :: IsScalar r
        => DualNumber (Tensor1 r) -> DualNumber (Tensor1 r)
        -> DualNumber (Tensor1 r)
append1 (D u u') (D v v') = D (u V.++ v) (dAppend1 u' (V.length u) v')

slice1 :: IsScalar r
       => Int -> Int -> DualNumber (Tensor1 r) -> DualNumber (Tensor1 r)
slice1 i n (D u u') = D (V.slice i n u) (dSlice1 i n u' (V.length u))

sumRows1 :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (Tensor1 r)
sumRows1 (D u u') = D (V.fromList $ map HM.sumElements $ HM.toRows u)
                      (dSumRows1 u' (HM.cols u))

sumColumns1 :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (Tensor1 r)
sumColumns1 (D u u') = D (V.fromList $ map HM.sumElements $ HM.toColumns u)
                         (dSumColumns1 u' (HM.rows u))

-- If @v'@ is a @Var1@, this is much faster due to the optimization
-- in @Index0@. The detour through a boxed vector (list probably fuses away)
-- is costly, but only matters if @f@ is cheap.
map1 :: IsScalar r
     => (DualNumber r -> DualNumber r) -> DualNumber (Tensor1 r)
     -> DualNumber (Tensor1 r)
map1 f (D v v') =
  let k = V.length v
      g ix p = f $ D p (dIndex0 v' ix k)
      ds = imap g $ V.toList v
  in seq1 $ V.fromList ds

-- | Dense matrix-vector product.
infixr 8 #>!
(#>!) :: IsScalar r
      => DualNumber (Tensor2 r) -> DualNumber (Tensor1 r)
      -> DualNumber (Tensor1 r)
(#>!) (D u u') (D v v') = D (u #> v) (dAdd (dMD_V1 u' v) (dM_VD1 u v'))

-- | Dense matrix-vector product with a constant vector.
infixr 8 #>!!
(#>!!) :: IsScalar r
       => DualNumber (Tensor2 r) -> Primal (Tensor1 r)
       -> DualNumber (Tensor1 r)
(#>!!) (D u u') v = D (u #> v) (dMD_V1 u' v)

fromX1 :: IsScalar r => DualNumber (TensorX r) -> DualNumber (Tensor1 r)
fromX1 (D u u') = D (OT.toVector u) (dFromX1 u')

fromS1 :: forall len r. (KnownNat len, IsScalarS '[len] r)
       => DualNumber (TensorS '[len] r) -> DualNumber (Tensor1 r)
fromS1 (D u u') = D (OS.toVector u) (dFromS1 u')

reverse1 :: IsScalar r => DualNumber (Tensor1 r) -> DualNumber (Tensor1 r)
reverse1 (D u u') = D (V.reverse u) (dReverse1 u')

flatten1 :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (Tensor1 r)
flatten1 (D u u') = let (rows, cols) = HM.size u
                    in D (HM.flatten u) (dFlatten1 rows cols u')

flattenX1 :: IsScalar r => DualNumber (TensorX r) -> DualNumber (Tensor1 r)
flattenX1 (D u u') = let sh = OT.shapeL u
                     in D (OT.toVector u) (dFlattenX1 sh u')

flattenS1 :: IsScalarS sh r
          => DualNumber (TensorS sh r) -> DualNumber (Tensor1 r)
flattenS1 (D u u') = D (OS.toVector u) (dFlattenS1 u')

corr1 :: IsScalar r
      => DualNumber (Tensor1 r) -> DualNumber (Tensor1 r)
      -> DualNumber (Tensor1 r)
corr1 ker@(D u _) vv@(D v _) = case (V.length u, V.length v) of
  (0, lenV) -> konst1 0 lenV
  (lenK, lenV) -> if lenK <= lenV
                  then vectorSlices2 lenK vv #>! ker
                  else error $ "corr1: len kernel " ++ show lenK
                               ++ " > len vector " ++ show lenV

-- This is not optimally implemented: @append1@ is costly compared
-- to a @mconcat@ counterpart and @z@ is used twice without
-- assigning it to a variable.
conv1 :: IsScalar r
      => DualNumber (Tensor1 r) -> DualNumber (Tensor1 r)
      -> DualNumber (Tensor1 r)
conv1 ker@(D u _) vv@(D v _) =
  let lenK = V.length u
      lenV = V.length v
      kerRev = reverse1 ker
      z = konst1 0 (lenK - 1)
      vvPadded = append1 z $ append1 vv z
  in if lenK == 0
     then konst1 0 lenV
     else corr1 kerRev vvPadded

-- No padding; remaining areas ignored.
maxPool1 :: IsScalar r
         => Int -> Int -> DualNumber (Tensor1 r) -> DualNumber (Tensor1 r)
maxPool1 ksize stride v@(D u _) =
  let slices = [slice1 i ksize v | i <- [0, stride .. V.length u - ksize]]
  in seq1 $ V.fromList $ map maximum0 slices


-- * Non-monadic operations resulting in a matrix

-- @2@ means rank two, so the dual component represents a matrix.
fromRows2 :: IsScalar r
          => Data.Vector.Vector (DualNumber (Tensor1 r))
          -> DualNumber (Tensor2 r)
fromRows2 v = D (HM.fromRows $ map (\(D u _) -> u) $ V.toList v)
                (dFromRows2 $ V.map (\(D _ u') -> u') v)

fromColumns2 :: IsScalar r
             => Data.Vector.Vector (DualNumber (Tensor1 r))
             -> DualNumber (Tensor2 r)
fromColumns2 v = D (HM.fromRows $ map (\(D u _) -> u) $ V.toList v)
                   (dFromColumns2 $ V.map (\(D _ u') -> u') v)

konst2 :: IsScalar r => DualNumber r -> (Int, Int) -> DualNumber (Tensor2 r)
konst2 (D u u') sz = D (HM.konst u sz) (dKonst2 u' sz)

transpose2 :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
transpose2 (D u u') = D (HM.tr' u) (dTranspose2 u')

-- | Dense matrix-matrix product.
--
-- If @u@ is a m x n (number of rows x number of columns) matrix
-- and @v@ is a n x p matrix then the result of @u <>! v@ is a m x p matrix.
infixr 8 <>!
(<>!) :: IsScalar r
      => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
      -> DualNumber (Tensor2 r)
(<>!) (D u u') (D v v') = D (u HM.<> v) (dAdd (dMD_M2 u' v) (dM_MD2 u v'))

-- | Dense matrix-matrix product with a constant matrix.
infixr 8 <>!!
(<>!!) :: IsScalar r
       => DualNumber (Tensor2 r) -> Primal (Tensor2 r)
       -> DualNumber (Tensor2 r)
(<>!!) (D u u') v = D (u HM.<> v) (dMD_M2 u' v)

rowAppend2 :: IsScalar r
           => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
           -> DualNumber (Tensor2 r)
rowAppend2 (D u u') (D v v') =
  D (u HM.=== v) (dRowAppend2 u' (HM.rows u) v')

columnAppend2 :: IsScalar r
              => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
              -> DualNumber (Tensor2 r)
columnAppend2 (D u u') (D v v') =
  D (u HM.||| v) (dColumnAppend2 u' (HM.cols u) v')

rowSlice2 :: IsScalar r
          => Int -> Int -> DualNumber (Tensor2 r)
          -> DualNumber (Tensor2 r)
rowSlice2 i n (D u u') = D (HM.subMatrix (i, 0) (n, HM.cols u) u)
                           (dRowSlice2 i n u' (HM.rows u))

columnSlice2 :: IsScalar r
             => Int -> Int -> DualNumber (Tensor2 r)
             -> DualNumber (Tensor2 r)
columnSlice2 i n (D u u') = D (HM.subMatrix (0, i) (HM.rows u, n) u)
                              (dColumnSlice2 i n u' (HM.rows u))

asRow2 :: IsScalar r
       => DualNumber (Tensor1 r) -> Int -> DualNumber (Tensor2 r)
asRow2 (D u u') n = D (HM.fromRows $ replicate n u) (dAsRow2 u')

asColumn2 :: IsScalar r
          => DualNumber (Tensor1 r) -> Int -> DualNumber (Tensor2 r)
asColumn2 (D u u') n = D (HM.fromColumns $ replicate n u) (dAsColumn2 u')

fromX2 :: IsScalar r => DualNumber (TensorX r) -> DualNumber (Tensor2 r)
fromX2 (D u u') = case OT.shapeL u of
  [_, cols] -> D (HM.reshape cols $ OT.toVector u) (dFromX2 u')
  dims -> error $ "fromX2: the tensor has wrong dimensions " ++ show dims

fromS2 :: forall rows cols r.
          (KnownNat rows, KnownNat cols, IsScalarS '[rows, cols] r)
       => DualNumber (TensorS '[rows, cols] r) -> DualNumber (Tensor2 r)
fromS2 (D u u') = D (HM.reshape (valueOf @cols) $ OS.toVector u) (dFromS2 u')

flipud2 :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
flipud2 (D u u') = D (HM.flipud u) (dFlipud2 u')

fliprl2 :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
fliprl2 (D u u') = D (HM.fliprl u) (dFliprl2 u')

vectorSlices2 :: IsScalar r
              => Int -> DualNumber (Tensor1 r) -> DualNumber (Tensor2 r)
vectorSlices2 n vv@(D v _) =
  fromRows2 $ V.fromList [slice1 i n vv | i <- [0 .. V.length v - n]]

reshape2 :: IsScalar r
         => Int -> DualNumber (Tensor1 r) -> DualNumber (Tensor2 r)
reshape2 cols (D u u') = D (HM.reshape cols u) (dReshape2 cols u')


-- * Non-monadic operations resulting in an arbitrary tensor

-- Warning: not tested nor benchmarked.

konstX :: IsScalar r => DualNumber r -> OT.ShapeL -> DualNumber (TensorX r)
konstX (D u u') sh = D (OT.constant sh u) (dKonstX u' sh)

appendX :: IsScalar r
        => DualNumber (TensorX r) -> DualNumber (TensorX r)
        -> DualNumber (TensorX r)
appendX (D u u') (D v v') =
  D (u `OT.append` v) (dAppendX u' (head $ OT.shapeL u) v')

sliceX :: IsScalar r
       => Int -> Int -> DualNumber (TensorX r) -> DualNumber (TensorX r)
sliceX i n (D u u') = D (OT.slice [(i, n)] u)
                        (dSliceX i n u' (head $ OT.shapeL u))

indexX :: IsScalar r
       => DualNumber (TensorX r) -> Int -> DualNumber (TensorX r)
indexX (D u u') ix = D (OT.index u ix)
                       (dIndexX u' ix (head $ OT.shapeL u))

ravelFromListX :: IsScalar r
               => [DualNumber (TensorX r)] -> DualNumber (TensorX r)
ravelFromListX ld =
  let (lu, lu') = unzip $ map (\(D u u') -> (u, u')) ld
      sh = case lu of
        u : _ -> length lu : OT.shapeL u
        [] -> []
  in D (OT.ravel $ OTB.fromList sh lu) (dRavelFromListX lu')

unravelToListX :: IsScalar r
               => DualNumber (TensorX r) -> [DualNumber (TensorX r)]
unravelToListX (D v v') = case OT.shapeL v of
  k : _ ->
    let g ix p = D p (dIndexX v' ix k)
    in imap g $ OTB.toList $ OT.unravel v
  [] -> error "unravelToListX: wrong tensor dimensions"  -- catch early

mapX :: IsScalar r
     => (DualNumber (TensorX r) -> DualNumber (TensorX r))
     -> DualNumber (TensorX r)
     -> DualNumber (TensorX r)
mapX f = ravelFromListX . map f . unravelToListX

zipWithX :: IsScalar r
         => (DualNumber (TensorX r) -> DualNumber (TensorX r)
             -> DualNumber (TensorX r))
         -> DualNumber (TensorX r) -> DualNumber (TensorX r)
         -> DualNumber (TensorX r)
zipWithX f d e =
  ravelFromListX $ zipWith f (unravelToListX d) (unravelToListX e)

reshapeX :: IsScalar r
         => OT.ShapeL -> DualNumber (TensorX r) -> DualNumber (TensorX r)
reshapeX sh' (D u u') = D (OT.reshape sh' u) (dReshapeX (OT.shapeL u) sh' u')

from0X :: IsScalar r => DualNumber r -> DualNumber (TensorX r)
from0X (D u u') = D (OT.scalar u) (dFrom0X u')

from1X :: IsScalar r => DualNumber (Tensor1 r) -> DualNumber (TensorX r)
from1X (D u u') = D (OT.fromVector [V.length u] u) (dFrom1X u')

from2X :: IsScalar r => DualNumber (Tensor2 r) -> DualNumber (TensorX r)
from2X (D u u') = D (OT.fromVector [HM.rows u, HM.cols u] $ HM.flatten u)
                    (dFrom2X u' (HM.cols u))

fromSX :: forall sh r. IsScalarS sh r
       => DualNumber (TensorS sh r) -> DualNumber (TensorX r)
fromSX (D u u') = D (Data.Array.Convert.convert u) (dFromSX u')


-- * Non-monadic operations resulting in an arbitrary fully typed Shaped tensor

-- Warning: not tested nor benchmarked.

konstS :: IsScalarS sh r => DualNumber r -> DualNumber (TensorS sh r)
konstS (D u u') = D (OS.constant u) (dKonstS u')

appendS :: ( KnownNat m, KnownNat n, IsScalarS sh r, IsScalarS (m ': sh) r
           , IsScalarS (n ': sh) r, IsScalarS ((m + n) ': sh) r )
        => DualNumber (TensorS (m ': sh) r)
        -> DualNumber (TensorS (n ': sh) r)
        -> DualNumber (TensorS ((m + n) ': sh) r)
appendS (D u u') (D v v') = D (u `OS.append` v) (dAppendS u' v')

sliceS :: forall i n k rest r.
          ( KnownNat i, KnownNat n, KnownNat k, IsScalarS rest r
          , IsScalarS (i + n + k ': rest) r, IsScalarS (n ': rest) r )
       => DualNumber (TensorS (i + n + k ': rest) r)
       -> DualNumber (TensorS (n ': rest) r)
sliceS (D u u') = D (OS.slice @'[ '(i, n) ] u)
                    (dSliceS (Proxy :: Proxy i) Proxy u')

indexS :: forall ix k rest r.
          ( KnownNat ix, KnownNat k
          , IsScalarS (ix + 1 + k ': rest) r, IsScalarS rest r )
       => DualNumber (TensorS (ix + 1 + k ': rest) r)
       -> DualNumber (TensorS rest r)
indexS (D u u') = D (OS.index u (valueOf @ix))
                    (dIndexS u' (Proxy :: Proxy ix))

ravelFromListS :: forall rest k r.
                  (KnownNat k, IsScalarS rest r, IsScalarS (k : rest) r)
               => [DualNumber (TensorS rest r)]
               -> DualNumber (TensorS (k : rest) r)
ravelFromListS ld =
  let (lu, lu') = unzip $ map (\(D u u') -> (u, u')) ld
  in D (OS.ravel $ OSB.fromList lu) (dRavelFromListS lu')

unravelToListS :: forall k rest r.
                  (KnownNat k, IsScalarS rest r, IsScalarS (k : rest) r)
               => DualNumber (TensorS (k : rest) r)
               -> [DualNumber (TensorS rest r)]
unravelToListS (D v v') =
  -- @dIndexS@ is rigid, with type-level bound-checking, so we have to switch
  -- to @dIndexX@ for this function.
  let g ix p = D p (dFromXS $ dIndexX (dFromSX v') ix (valueOf @k))
  in imap g $ OSB.toList $ OS.unravel v

mapS :: forall k sh1 sh r. ( KnownNat k
                           , IsScalarS sh1 r, IsScalarS (k : sh1) r
                           , IsScalarS sh r, IsScalarS (k : sh) r )
     => (DualNumber (TensorS sh1 r) -> DualNumber (TensorS sh r))
     -> DualNumber (TensorS (k : sh1) r)
     -> DualNumber (TensorS (k : sh) r)
mapS f = ravelFromListS . map f . unravelToListS

mapMS :: forall k sh1 sh r m. ( Monad m, KnownNat k
                              , IsScalarS sh1 r, IsScalarS (k : sh1) r
                              , IsScalarS sh r, IsScalarS (k : sh) r )
      => (DualNumber (TensorS sh1 r) -> m (DualNumber (TensorS sh r)))
      -> DualNumber (TensorS (k : sh1) r)
      -> m (DualNumber (TensorS (k : sh) r))
mapMS f d = do
  let ld = unravelToListS d
  ld2 <- mapM f ld
  return $! ravelFromListS ld2

zipWithS :: forall k sh1 sh2 sh r.
            ( KnownNat k
            , IsScalarS sh1 r, IsScalarS (k : sh1) r
            , IsScalarS sh2 r, IsScalarS (k : sh2) r
            , IsScalarS sh r, IsScalarS (k : sh) r )
         => (DualNumber (TensorS sh1 r) -> DualNumber (TensorS sh2 r)
             -> DualNumber (TensorS sh r))
         -> DualNumber (TensorS (k : sh1) r)
         -> DualNumber (TensorS (k : sh2) r)
         -> DualNumber (TensorS (k : sh) r)
zipWithS f d e =
  ravelFromListS $ zipWith f (unravelToListS d) (unravelToListS e)

reshapeS :: (IsScalarS sh r, IsScalarS sh' r, OS.Size sh ~ OS.Size sh')
         => DualNumber (TensorS sh r) -> DualNumber (TensorS sh' r)
reshapeS (D u u') = D (OS.reshape u) (dReshapeS u')

from0S :: IsScalarS '[] r => DualNumber r -> DualNumber (TensorS '[] r)
from0S (D u u') = D (OS.scalar u) (dFrom0S u')

from1S :: (KnownNat n, IsScalarS '[n] r)
       => DualNumber (Tensor1 r) -> DualNumber (TensorS '[n] r)
from1S (D u u') = D (OS.fromVector u) (dFrom1S u')

from2S :: (KnownNat rows, KnownNat cols, IsScalarS '[rows, cols] r)
       => DualNumber (Tensor2 r) -> DualNumber (TensorS '[rows, cols] r)
from2S (D u u') = D (OS.fromVector $ HM.flatten u) (dFrom2S Proxy u')

fromXS :: IsScalarS sh r => DualNumber (TensorX r) -> DualNumber (TensorS sh r)
fromXS (D u u') = D (Data.Array.Convert.convert u) (dFromXS u')


-- * General monadic operations, for any scalar rank

tanhAct :: (DualMonad r m, IsDualWithScalar a r, Floating (Primal a))
        => DualNumber a -> m (DualNumber a)
tanhAct = returnLet . tanh

logistic :: (Floating (Primal a), IsDual a) => DualNumber a -> DualNumber a
logistic (D u u') =
  let y = recip (1 + exp (- u))
  in D y (dScale (y * (1 - y)) u')

logisticAct :: (DualMonad r m, IsDualWithScalar a r, Floating (Primal a))
            => DualNumber a -> m (DualNumber a)
logisticAct = returnLet . logistic

-- Optimized and more clearly written @u ** 2@.
square :: (Num (Primal a), IsDual a) => DualNumber a -> DualNumber a
square (D u u') = D (u * u) (dScale (2 * u) u')

squaredDifference :: (Num (Primal a), IsDual a)
                  => Primal a -> DualNumber a -> DualNumber a
squaredDifference targ res = square $ res - scalar targ

lossSquared :: (DualMonad r m, IsDualWithScalar a r)
            => Primal a -> DualNumber a -> m (DualNumber a)
lossSquared targ res = returnLet $ squaredDifference targ res


-- * Monadic operations resulting in a scalar

-- The type permits other ranks, but it's nonsense.
reluAct :: DualMonad r m => DualNumber r -> m (DualNumber r)
reluAct (D u u') = returnLet $ D (max 0 u) (dScale (if u > 0 then 1 else 0) u')

sumElementsVectorOfDual
  :: IsScalar r => Data.Vector.Vector (DualNumber r) -> DualNumber r
sumElementsVectorOfDual = V.foldl' (+) 0

softMaxAct :: DualMonad r m
           => Data.Vector.Vector (DualNumber r)
           -> m (Data.Vector.Vector (DualNumber r))
softMaxAct us = do
  expUs <- V.mapM (returnLet . exp) us
  let sumExpUs = sumElementsVectorOfDual expUs
  -- This has to be let-bound, because it's used many times below.
  recipSum <- returnLet $ recip sumExpUs
  V.mapM (\r -> returnLet $ r * recipSum) expUs

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropy :: forall r m. DualMonad r m
                 => Primal (Tensor1 r)
                 -> Data.Vector.Vector (DualNumber r)
                 -> m (DualNumber r)
lossCrossEntropy targ res = do
  let f :: DualNumber r -> Int -> DualNumber r -> DualNumber r
      f !acc i d = acc + scale (targ V.! i) (log d)
  returnLet $ negate $ V.ifoldl' f 0 res

-- In terms of hmatrix: @-(log res <.> targ)@.
lossCrossEntropyV :: (DualMonad r m, Floating (Primal (Tensor1 r)))
                  => Primal (Tensor1 r)
                  -> DualNumber (Tensor1 r)
                  -> m (DualNumber r)
lossCrossEntropyV targ res = returnLet $ negate $ log res <.>!! targ

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are on-hot.
lossSoftMaxCrossEntropyV
  :: (DualMonad r m, Floating (Primal (Tensor1 r)))
  => Primal (Tensor1 r) -> DualNumber (Tensor1 r) -> m (DualNumber r)
lossSoftMaxCrossEntropyV target (D u u') = do
  -- The following protects from underflows, overflows and exploding gradients
  -- and is required by the QuickCheck test in TestMnistCNN.
  -- See https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/sparse_softmax_op.cc#L106
  -- and https://github.com/tensorflow/tensorflow/blob/5a566a7701381a5cf7f70fce397759483764e482/tensorflow/core/kernels/xent_op.h
  let expU = exp (u - HM.scalar (HM.maxElement u))
      sumExpU = HM.sumElements expU
      recipSum = recip sumExpU
-- not exposed: softMaxU = HM.scaleRecip sumExpU expU
      softMaxU = HM.scale recipSum expU
  returnLet $ D (negate $ log softMaxU <.> target)  -- TODO: avoid @log . exp@
                (dDot0 (softMaxU - target) u')


-- * Monadic operations resulting in a vector

reluAct1 :: DualMonad r m
         => DualNumber (Tensor1 r) -> m (DualNumber (Tensor1 r))
reluAct1 v@(D u _) = do
  let oneIfGtZero = V.map (\x -> if x > 0 then 1 else 0) u
  returnLet $ scale oneIfGtZero v

reluLeakyAct1 :: DualMonad r m
              => DualNumber (Tensor1 r) -> m (DualNumber (Tensor1 r))
reluLeakyAct1 v@(D u _) = do
  let oneIfGtZero = V.map (\x -> if x > 0 then 1 else 0.01) u
  returnLet $ scale oneIfGtZero v

softMaxActV :: (DualMonad r m, Floating (Primal (Tensor1 r)))
            => DualNumber (Tensor1 r) -> m (DualNumber (Tensor1 r))
softMaxActV d@(D u _) = do
  expU <- returnLet $ exp d
  let sumExpU = sumElements0 expU
  -- This has to be let-bound, because it's used many times below.
  recipSum <- returnLet $ recip sumExpU
  returnLet $ konst1 recipSum (V.length u) * expU

-- Note that this is equivalent to a composition of softMax and cross entropy
-- only when @target@ is one-hot. Otherwise, results vary wildly. In our
-- rendering of the MNIST data all labels are on-hot.
lossSoftMaxCrossEntropyL
  :: (DualMonad r m, Floating (Primal (Tensor2 r)))
  => Primal (Tensor2 r)
  -> DualNumber (Tensor2 r)
  -> m (DualNumber (Tensor1 r))
lossSoftMaxCrossEntropyL target (D u u') = do
  let expU = exp (u - HM.scalar (HM.maxElement u))  -- vs exploding gradients
      sumExpU = V.fromList $ map HM.sumElements $ HM.toColumns expU
      recipSum = recip sumExpU
      softMaxU = HM.asRow recipSum * expU
                   -- this @asRow@ is safe; multiplied at once
      scaled = D (negate $ log softMaxU * target)
                 (dScale (softMaxU - target) u')
  returnLet $ sumColumns1 scaled


-- * Monadic operations resulting in a matrix (or matrices)

reluAct2 :: DualMonad r m
         => DualNumber (Tensor2 r) -> m (DualNumber (Tensor2 r))
reluAct2 m@(D u _) = do
  let oneIfGtZero = HM.cmap (\x -> if x > 0 then 1 else 0) u
  returnLet $ scale oneIfGtZero m

-- TODO: This has list of matrices result instead of a cube tensor.
matrixSlices2 :: DualMonad r m
              => Int -> DualNumber (Tensor2 r) -> m [DualNumber (Tensor2 r)]
matrixSlices2 dr m@(D u _) = do
  let (rows, cols) = HM.size u
      n = dr * cols
  v <- returnLet $ flatten1 m  -- used many times below
  let f k = returnLet $ reshape2 cols $ slice1 (k * cols) n v
  mapM f [0 .. rows - dr]

-- Not optimal: matrix is constructed and destructed immediately,
-- which is costly when evaluating delta expressions. The transposes
-- may not be optimal, either. This goes down to individual deltas
-- of scalars, which is horrible for performance. Unlike @corr1@
-- this uses the slow dot product instead of the fast matrix-vector
-- (or matrix-matrix) multiplication.
corr2 :: forall r m. DualMonad r m
      => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
      -> m (DualNumber (Tensor2 r))
corr2 ker@(D u _) m@(D v _) = do
  let (rowsK, colsK) = HM.size u
      (rowsM, colsM) = HM.size v
      rr = rowsM - rowsK + 1
      rc = colsM - colsK + 1
  if | rowsK <= 0 || colsK <= 0 ->
       error $ "corr2: empty kernel not handled: " ++ show (rowsK, colsK)
     | rr <= 0 || rc <= 0 ->
       error $ "corr2: dim kernel " ++ show (rowsK, colsK)
               ++ " > dim matrix " ++ show (rowsM, colsM)
     | otherwise -> do
       kerTransV <- returnLet $ flatten1 (transpose2 ker)
       let dotColSlices :: DualNumber (Tensor2 r) -> m [DualNumber r]
           dotColSlices tm = do
             ttm <- returnLet $ transpose2 tm
             colSlices <- matrixSlices2 colsK ttm
             let f :: DualNumber (Tensor2 r) -> DualNumber r
                 f sm = kerTransV <.>! flatten1 sm
             return $ map f colSlices
       rowSlices <- matrixSlices2 rowsK m
       dotSlicesOfSlices <- mapM dotColSlices rowSlices
       returnLet $ reshape2 rc $ seq1 $ V.fromList $ concat dotSlicesOfSlices

conv2 :: forall r m. DualMonad r m
      => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
      -> m (DualNumber (Tensor2 r))
conv2 ker@(D u _) m@(D v _) = do
  let (rowsK, colsK) = HM.size u
      (rowsM, colsM) = HM.size v
  if | rowsK <= 0 || colsK <= 0 ->
       returnLet $ konst2 0 (rowsM + rowsK - 1, colsM + colsK - 1)
     | otherwise -> do
       let zRow = konst2 0 (rowsK - 1, colsM)
           rowPadded = rowAppend2 zRow $ rowAppend2 m zRow
           zCol = konst2 0 (rowsM + 2 * (rowsK - 1), colsK - 1)
           padded = columnAppend2 zCol $ columnAppend2 rowPadded zCol
       corr2 (fliprl2 . flipud2 $ ker) padded

conv2' :: IsScalar r
       => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
       -> DualNumber (Tensor2 r)
conv2' (D u u') (D v v') = D (HM.conv2 u v) (dAdd (dConv2 u v') (dConv2 v u'))

conv2S :: forall r filter_height_1 filter_width_1 in_height in_width.
          ( KnownNat filter_height_1, KnownNat filter_width_1
          , KnownNat in_height, KnownNat in_width
          , IsScalarS '[ in_height + filter_height_1
                       , in_width + filter_width_1 ] r
          , IsScalarS '[filter_height_1 + 1, filter_width_1 + 1] r
          , IsScalarS '[in_height, in_width] r )
       => DualNumber (TensorS '[filter_height_1 + 1, filter_width_1 + 1] r)
       -> DualNumber (TensorS '[in_height, in_width] r)
       -> DualNumber (TensorS '[ in_height + filter_height_1
                               , in_width + filter_width_1 ] r)
conv2S ker x = from2S $ conv2' (fromS2 ker) (fromS2 x)

-- Convolution of many matrices at once. The names of dimensions are from
-- https://www.tensorflow.org/api_docs/python/tf/nn/conv2d
conv24 :: forall filter_height_1 filter_width_1
                 out_channels in_height in_width n_batches in_channels r.
          ( KnownNat n_batches, KnownNat in_channels, KnownNat out_channels
          , KnownNat filter_height_1, KnownNat filter_width_1
          , KnownNat in_height, KnownNat in_width
          , IsScalarS '[ n_batches
                       , in_channels
                       , in_height + filter_height_1
                       , in_width + filter_width_1 ] r
          , IsScalarS '[ out_channels, in_channels
                       , filter_height_1 + 1, filter_width_1 + 1 ] r
          , IsScalarS '[ in_channels
                       , in_height + filter_height_1
                       , in_width + filter_width_1 ] r
          , IsScalarS '[ in_channels
                       , filter_height_1 + 1, filter_width_1 + 1 ] r
          , IsScalarS '[in_height, in_width] r
          , IsScalarS '[in_channels, in_height, in_width] r
          , IsScalarS '[filter_height_1 + 1, filter_width_1 + 1] r
          , IsScalarS '[ in_height + filter_height_1
                       , in_width + filter_width_1 ] r
          , IsScalarS '[ out_channels
                       , in_height + filter_height_1
                       , in_width + filter_width_1 ] r
          , IsScalarS '[ n_batches, out_channels
                       , in_height + filter_height_1
                       , in_width + filter_width_1 ] r
          , IsScalarS '[n_batches, in_channels, in_height, in_width] r
          )
       => DualNumber (TensorS '[ out_channels, in_channels
                               , filter_height_1 + 1, filter_width_1 + 1 ] r)
       -> DualNumber (TensorS '[ n_batches, in_channels
                               , in_height, in_width ] r)
       -> DualNumber (TensorS '[ n_batches, out_channels
                               , in_height + filter_height_1
                               , in_width + filter_width_1 ] r)
conv24 ker x = mapS conv23 x where
  conv23 :: DualNumber (TensorS '[in_channels, in_height, in_width] r)
         -> DualNumber (TensorS '[ out_channels
                                 , in_height + filter_height_1
                                 , in_width + filter_width_1 ] r)
  conv23 x1 = mapS (convFilters x1) ker
  convFilters
    :: DualNumber (TensorS '[in_channels, in_height, in_width] r)
    -> DualNumber (TensorS '[ in_channels
                            , filter_height_1 + 1, filter_width_1 + 1 ] r)
    -> DualNumber (TensorS '[ in_height + filter_height_1
                            , in_width + filter_width_1 ] r)
  convFilters x1 ker1 = sumOutermost $ zipWithS conv2S ker1 x1
  sumOutermost :: DualNumber (TensorS '[ in_channels
                                       , in_height + filter_height_1
                                       , in_width + filter_width_1 ] r)
               -> DualNumber (TensorS '[ in_height + filter_height_1
                            , in_width + filter_width_1 ] r)
  sumOutermost = sum . unravelToListS
    -- slow; should go through Tensor2, or the Num instance should when possible

-- A variant with limited padding, corresponding to SAME padding
-- from Tensorflow. Data size does not change with this padding.
-- It also performs convolution wrt flipped kernel (and so saves
-- on flipping it here), which makes no practical difference when
-- the kernel is initialized randomly.
convSame2 :: forall r m. DualMonad r m
          => DualNumber (Tensor2 r) -> DualNumber (Tensor2 r)
          -> m (DualNumber (Tensor2 r))
convSame2 ker@(D u _) m@(D v _) = do
  let (rowsK, colsK) = HM.size u
      (rowsM, colsM) = HM.size v
  if | rowsK <= 0 || colsK <= 0 ->
       returnLet $ konst2 0 (rowsM, colsM)
     | otherwise -> do
       let zRow = konst2 0 ((rowsK - 1) `div` 2, colsM)
           rowPadded = rowAppend2 zRow $ rowAppend2 m zRow
           zCol = konst2 0 (rowsM + rowsK - 1, (colsK - 1) `div` 2)
           padded = columnAppend2 zCol $ columnAppend2 rowPadded zCol
       corr2 ker padded

-- No padding; remaining areas ignored.
maxPool2 :: forall r m. DualMonad r m
         => Int -> Int -> DualNumber (Tensor2 r) -> m (DualNumber (Tensor2 r))
maxPool2 ksize stride m@(D u _) = do
  let (rows, cols) = HM.size u
      colsOut = cols `div` stride
      resultRows = [0, stride .. rows - ksize]
      resultCols = [0, stride .. cols - ksize]
      resultCoords = [(r, c) | r <- resultRows, c <- resultCols]
  v <- returnLet $ flatten1 m  -- used many times below
  let getArea :: (Int, Int) -> DualNumber (Tensor1 r)
      getArea (r0, c0) =
        let getAreaAtRow r1 = append1 (slice1 (r1 * cols + c0) ksize v)
        in foldr getAreaAtRow (seq1 V.empty) [r0 .. r0 + ksize - 1]
      mins = map (maximum0 . getArea) resultCoords
  returnLet $ reshape2 colsOut $ seq1 $ V.fromList mins

maxPool24 :: forall r m n_batches channels
                    in_height in_width out_height out_width.
             ( DualMonad r m, KnownNat n_batches, KnownNat channels
             , KnownNat in_height, KnownNat in_width
             , KnownNat out_height, KnownNat out_width
             , IsScalarS '[ n_batches, channels, in_height, in_width ] r
             , IsScalarS '[ n_batches, channels, out_height, out_width ] r
             , IsScalarS '[ channels, in_height, in_width ] r
             , IsScalarS '[ channels, out_height, out_width ] r
             , IsScalarS '[ in_height, in_width ] r
             , IsScalarS '[ out_height, out_width ] r )
          => Int -> Int
          -> DualNumber (TensorS '[ n_batches, channels
                                  , in_height, in_width ] r)
          -> m (DualNumber (TensorS '[ n_batches, channels
                                     , out_height, out_width ] r))
maxPool24 ksize stride d = do
  res <- mapMS (mapMS (fmap from2S . maxPool2 ksize stride . fromS2)) d
  returnLet res

reluActS :: (DualMonad r m, IsScalarS sh r)
         => DualNumber (TensorS sh r) -> m (DualNumber (TensorS sh r))
reluActS d@(D u _) = do
  let oneIfGtZero = OS.mapA (\x -> if x > 0 then 1 else 0) u
  returnLet $ scale oneIfGtZero d
