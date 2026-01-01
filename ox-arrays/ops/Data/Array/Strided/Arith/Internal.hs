{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Data.Array.Strided.Arith.Internal where

import Control.Monad
import Data.Bifunctor (second)
import Data.Bits
import Data.Int
import Data.List (sort, zip4)
import Data.Proxy
import Data.Type.Equality
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.Mutable qualified as VSM
import Foreign.C.Types
import Foreign.Ptr
import Foreign.Storable
import GHC.TypeLits
import GHC.TypeNats qualified as TN
import Language.Haskell.TH
import System.IO (hFlush, stdout)
import System.IO.Unsafe

import Data.Array.Strided.Arith.Internal.Foreign
import Data.Array.Strided.Arith.Internal.Lists
import Data.Array.Strided.Array


-- TODO: need to sort strides for reduction-like functions so that the C inner-loop specialisation has some chance of working even after transposition


-- TODO: move this to a utilities module
fromSNat' :: SNat n -> Int
fromSNat' = fromEnum . TN.fromSNat

data Dict c where
  Dict :: c => Dict c

debugShow :: forall n a. (Storable a, KnownNat n) => Array n a -> String
debugShow (Array sh strides offset vec) =
  "Array @" ++ show (natVal (Proxy @n)) ++ " " ++ show sh ++ " " ++ show strides ++ " " ++ show offset ++ " <_*" ++ show (VS.length vec) ++ ">"


-- TODO: test all the cases of this thing with various input strides
liftOpEltwise1 :: Storable a
               => SNat n
               -> (Ptr a -> Ptr b)
               -> (Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())
               -> Array n a -> Array n a
liftOpEltwise1 sn@SNat ptrconv cf_strided arr@(Array sh strides offset vec)
  | Just (blockOff, blockSz) <- stridesDense sh offset strides =
      if blockSz == 0
        then Array sh (map (const 0) strides) 0 VS.empty
        else let resvec = arrValues $ wrapUnary sn ptrconv cf_strided (Array [blockSz] [1] blockOff vec)
             in Array sh strides (offset - blockOff) resvec
  | otherwise = wrapUnary sn ptrconv cf_strided arr

-- TODO: test all the cases of this thing with various input strides
liftOpEltwise2 :: Storable a
               => SNat n
               -> (a -> b)
               -> (Ptr a -> Ptr b)
               -> (a -> a -> a)
               -> (Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ sv
               -> (Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> b -> IO ())  -- ^ vs
               -> (Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ vv
               -> Array n a -> Array n a -> Array n a
liftOpEltwise2 sn@SNat valconv ptrconv f_ss f_sv f_vs f_vv
    arr1@(Array sh1 strides1 offset1 vec1)
    arr2@(Array sh2 strides2 offset2 vec2)
  | sh1 /= sh2 = error $ "liftOpEltwise2: shapes unequal: " ++ show sh1 ++ " vs " ++ show sh2
  | any (<= 0) sh1 = Array sh1 (0 <$ strides1) 0 VS.empty
  | otherwise = case (stridesDense sh1 offset1 strides1, stridesDense sh2 offset2 strides2) of
      (Just (_, 1), Just (_, 1)) ->  -- both are a (potentially replicated) scalar; just apply f to the scalars
        let vec' = VS.singleton (f_ss (vec1 VS.! offset1) (vec2 VS.! offset2))
        in Array sh1 strides1 0 vec'

      (Just (_, 1), Just (blockOff, blockSz)) ->  -- scalar * dense
        let arr2' = arrayFromVector [blockSz] (VS.slice blockOff blockSz vec2)
            resvec = arrValues $ wrapBinarySV (SNat @1) valconv ptrconv f_sv (vec1 VS.! offset1) arr2'
        in Array sh1 strides2 (offset2 - blockOff) resvec

      (Just (_, 1), Nothing) ->  -- scalar * array
        wrapBinarySV sn valconv ptrconv f_sv (vec1 VS.! offset1) arr2

      (Just (blockOff, blockSz), Just (_, 1)) ->  -- dense * scalar
        let arr1' = arrayFromVector [blockSz] (VS.slice blockOff blockSz vec1)
            resvec = arrValues $ wrapBinaryVS (SNat @1) valconv ptrconv f_vs arr1' (vec2 VS.! offset2)
        in Array sh1 strides1 (offset1 - blockOff) resvec

      (Nothing, Just (_, 1)) ->  -- array * scalar
        wrapBinaryVS sn valconv ptrconv f_vs arr1 (vec2 VS.! offset2)

      (Just (blockOff1, blockSz1), Just (blockOff2, blockSz2))
        | strides1 == strides2
        ->  -- dense * dense but the strides match
          if blockSz1 /= blockSz2 || offset1 - blockOff1 /= offset2 - blockOff2
            then error $ "Data.Array.Strided.Ops.Internal(liftOpEltwise2): Internal error: cannot happen " ++ show (strides1, (blockOff1, blockSz1), strides2, (blockOff2, blockSz2))
            else
              let arr1' = arrayFromVector [blockSz1] (VS.slice blockOff1 blockSz1 vec1)
                  arr2' = arrayFromVector [blockSz1] (VS.slice blockOff2 blockSz2 vec2)
                  resvec = arrValues $ wrapBinaryVV (SNat @1) ptrconv f_vv arr1' arr2'
              in Array sh1 strides1 (offset1 - blockOff1) resvec

      (_, _) ->  -- fallback case
        wrapBinaryVV sn ptrconv f_vv arr1 arr2

-- | Given shape vector, offset and stride vector, check whether this virtual
-- vector uses a dense subarray of its backing array. If so, the first index
-- and the number of elements in this subarray is returned.
-- This excludes any offset.
stridesDense :: [Int] -> Int -> [Int] -> Maybe (Int, Int)
stridesDense sh offset _ | any (<= 0) sh = Just (offset, 0)
stridesDense sh offsetNeg stridesNeg =
  -- First reverse all dimensions with negative stride, so that the first used
  -- value is at 'offset' and the rest is >= offset.
  let (offset, strides) = flipReverseds sh offsetNeg stridesNeg
  in -- sort dimensions on their stride, ascending, dropping any zero strides
     case filter ((/= 0) . fst) (sort (zip strides sh)) of
       [] -> Just (offset, 1)
       (1, n) : pairs -> (offset,) <$> checkCover n pairs
       _ -> Nothing  -- if the smallest stride is not 1, it will never be dense
  where
    -- Given size of currently densely covered region at beginning of the
    -- array and the remaining (stride, size) pairs with all strides >=1,
    -- return whether this all together covers a dense prefix of the array. If
    -- it does, return the number of elements in this prefix.
    checkCover :: Int -> [(Int, Int)] -> Maybe Int
    checkCover block [] = Just block
    checkCover block ((s, n) : pairs) = guard (s <= block) >> checkCover ((n-1) * s + block) pairs

    -- Given shape, offset and strides, returns new (offset, strides) such that all strides are >=0
    flipReverseds :: [Int] -> Int -> [Int] -> (Int, [Int])
    flipReverseds [] off [] = (off, [])
    flipReverseds (n : sh') off (s : str')
      | s >= 0 = second (s :) (flipReverseds sh' off str')
      | otherwise =
          let off' = off + (n - 1) * s
          in second ((-s) :) (flipReverseds sh' off' str')
    flipReverseds _ _ _ = error "flipReverseds: invalid arguments"

data Unreplicated a =
  forall n'. KnownNat n' =>
    -- | Let the original array, with replicated dimensions, be called A.
    Unreplicated -- | An array with all strides /= 0. Call this array U. It has
                 -- the same shape as A, except with all the replicated (stride
                 -- == 0) dimensions removed. The shape of U is the
                 -- "unreplicated shape".
                 (Array n' a)
                 -- | Product of sizes of the unreplicated dimensions
                 Int
                 -- | Given the stride vector of an array with the unreplicated
                 -- shape, this function reinserts zeros so that it may be
                 -- combined with the original shape of A.
                 ([Int] -> [Int])

-- | Removes all replicated dimensions (i.e. those with stride == 0) from the array.
unreplicateStrides :: Array n a -> Unreplicated a
unreplicateStrides (Array sh strides offset vec) =
  let replDims = map (== 0) strides
      (shF, stridesF) = unzip [(n, s) | (n, s) <- zip sh strides, s /= 0]

      reinsertZeros (False : zeros) (s : strides') = s : reinsertZeros zeros strides'
      reinsertZeros (True : zeros) strides' = 0 : reinsertZeros zeros strides'
      reinsertZeros [] [] = []
      reinsertZeros (False : _) [] = error "unreplicateStrides: Internal error: reply strides too short"
      reinsertZeros [] (_:_) = error "unreplicateStrides: Internal error: reply strides too long"

      unrepSize = product [n | (n, True) <- zip sh replDims]

  in TN.withSomeSNat (fromIntegral (length shF)) $ \(SNat :: SNat lenshF) ->
       Unreplicated (Array @lenshF shF stridesF offset vec) unrepSize (reinsertZeros replDims)

simplifyArray :: Array n a
              -> (forall n'. KnownNat n'
                          => Array n' a  -- U
                          -- Product of sizes of the unreplicated dimensions
                          -> Int
                          -- Convert index in U back to index into original
                          -- array. Replicated dimensions get 0.
                          -> ([Int] -> [Int])
                          -- Given a new array of the same shape as U, convert
                          -- it back to the original shape and iteration order.
                          -> (Array n' a -> Array n a)
                          -- Do the same except without the INNER dimension.
                          -- This throws an error if the inner dimension had
                          -- stride 0.
                          -> (Array (n' - 1) a -> Array (n - 1) a)
                          -> r)
              -> r
simplifyArray array k
  | let revDims = map (< 0) (arrStrides array)
  , Unreplicated array' unrepSize rereplicate <- unreplicateStrides (arrayRevDims revDims array)
  = k array'
      unrepSize
      (\idx -> rereplicate (zipWith3 (\b n i -> if b then n - 1 - i else i)
                                     revDims (arrShape array') idx))
      (\(Array sh' strides' offset' vec') ->
         if sh' == arrShape array'
           then arrayRevDims revDims (Array (arrShape array) (rereplicate strides') offset' vec')
           else error $ "simplifyArray: Internal error: reply shape wrong (reply " ++ show sh' ++ ", unreplicated " ++ show (arrShape array') ++ ")")
      (\(Array sh' strides' offset' vec') ->
         if | sh' /= init (arrShape array') ->
                error $ "simplifyArray: Internal error: reply shape wrong (reply " ++ show sh' ++ ", unreplicated " ++ show (arrShape array') ++ ")"
            | last (arrStrides array) == 0 ->
                error "simplifyArray: Internal error: reduction reply handler used while inner stride was 0"
            | otherwise ->
                arrayRevDims (init revDims) (Array (init (arrShape array)) (init (rereplicate (strides' ++ [0]))) offset' vec'))

-- | The two input arrays must have the same shape.
simplifyArray2 :: Array n a -> Array n a
               -> (forall n'. KnownNat n'
                           => Array n' a  -- U1
                           -> Array n' a  -- U2 (same shape as U1)
                           -- Product of sizes of the dimensions that are
                           -- replicated in neither input
                           -> Int
                           -- Convert index in U{1,2} back to index into original
                           -- arrays. Dimensions that are replicated in both
                           -- inputs get 0.
                           -> ([Int] -> [Int])
                           -- Given a new array of the same shape as U1 (& U2),
                           -- convert it back to the original shape and
                           -- iteration order.
                           -> (Array n' a -> Array n a)
                           -- Do the same except without the INNER dimension.
                           -- This throws an error if the inner dimension had
                           -- stride 0 in both inputs.
                           -> (Array (n' - 1) a -> Array (n - 1) a)
                           -> r)
               -> r
simplifyArray2 arr1@(Array sh _ _ _) arr2@(Array sh2 _ _ _) k
  | sh /= sh2 = error "simplifyArray2: Unequal shapes"

  | let revDims = zipWith (\s1 s2 -> s1 < 0 && s2 < 0) (arrStrides arr1) (arrStrides arr2)
  , Array _ strides1 offset1 vec1 <- arrayRevDims revDims arr1
  , Array _ strides2 offset2 vec2 <- arrayRevDims revDims arr2

  , let replDims = zipWith (\s1 s2 -> s1 == 0 && s2 == 0) strides1 strides2
  , let (shF, strides1F, strides2F) = unzip3 [(n, s1, s2) | (n, s1, s2, False) <- zip4 sh strides1 strides2 replDims]

  , let reinsertZeros (False : zeros) (s : strides') = s : reinsertZeros zeros strides'
        reinsertZeros (True : zeros) strides' = 0 : reinsertZeros zeros strides'
        reinsertZeros [] [] = []
        reinsertZeros (False : _) [] = error "simplifyArray2: Internal error: reply strides too short"
        reinsertZeros [] (_:_) = error "simplifyArray2: Internal error: reply strides too long"

  , let unrepSize = product [n | (n, True) <- zip sh replDims]

  = TN.withSomeSNat (fromIntegral (length shF)) $ \(SNat :: SNat lenshF) ->
    k @lenshF
      (Array shF strides1F offset1 vec1)
      (Array shF strides2F offset2 vec2)
      unrepSize
      (\idx -> zipWith3 (\b n i -> if b then n - 1 - i else i)
                        revDims sh (reinsertZeros replDims idx))
      (\(Array sh' strides' offset' vec') ->
         if sh' /= shF then error $ "simplifyArray2: Internal error: reply shape wrong (reply " ++ show sh' ++ ", unreplicated " ++ show shF ++ ")"
         else arrayRevDims revDims (Array sh (reinsertZeros replDims strides') offset' vec'))
      (\(Array sh' strides' offset' vec') ->
         if | sh' /= init shF ->
                error $ "simplifyArray2: Internal error: reply shape wrong (reply " ++ show sh' ++ ", unreplicated " ++ show shF ++ ")"
            | last replDims ->
                error "simplifyArray2: Internal error: reduction reply handler used while inner dimension was unreplicated"
            | otherwise ->
                arrayRevDims (init revDims) (Array (init sh) (reinsertZeros (init replDims) strides') offset' vec'))

{-# NOINLINE wrapUnary #-}
wrapUnary :: forall a b n. Storable a
          => SNat n
          -> (Ptr a -> Ptr b)
          -> (Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())
          -> Array n a
          -> Array n a
wrapUnary _ ptrconv cf_strided array =
  simplifyArray array $ \(Array sh strides offset vec) _ _ restore _ -> unsafePerformIO $ do
    let ndims' = length sh
    outv <- VSM.unsafeNew (product sh)
    VSM.unsafeWith outv $ \poutv ->
      VS.unsafeWith (VS.fromListN ndims' (map fromIntegral sh)) $ \psh ->
      VS.unsafeWith (VS.fromListN ndims' (map fromIntegral strides)) $ \pstrides ->
      VS.unsafeWith vec $ \pv ->
        let pv' = pv `plusPtr` (offset * sizeOf (undefined :: a))
        in cf_strided (fromIntegral ndims') (ptrconv poutv) psh pstrides pv'
    restore . arrayFromVector sh <$> VS.unsafeFreeze outv

{-# NOINLINE wrapBinarySV #-}
wrapBinarySV :: forall a b n. Storable a
             => SNat n
             -> (a -> b)
             -> (Ptr a -> Ptr b)
             -> (Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())
             -> a -> Array n a
             -> Array n a
wrapBinarySV SNat valconv ptrconv cf_strided x array =
  simplifyArray array $ \(Array sh strides offset vec) _ _ restore _ -> unsafePerformIO $ do
    let ndims' = length sh
    outv <- VSM.unsafeNew (product sh)
    VSM.unsafeWith outv $ \poutv ->
      VS.unsafeWith (VS.fromListN ndims' (map fromIntegral sh)) $ \psh ->
      VS.unsafeWith (VS.fromListN ndims' (map fromIntegral strides)) $ \pstrides ->
      VS.unsafeWith vec $ \pv ->
        let pv' = pv `plusPtr` (offset * sizeOf (undefined :: a))
        in cf_strided (fromIntegral ndims') psh (ptrconv poutv) (valconv x) pstrides pv'
    restore . arrayFromVector sh <$> VS.unsafeFreeze outv

wrapBinaryVS :: Storable a
             => SNat n
             -> (a -> b)
             -> (Ptr a -> Ptr b)
             -> (Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> b -> IO ())
             -> Array n a -> a
             -> Array n a
wrapBinaryVS sn valconv ptrconv cf_strided arr y =
  wrapBinarySV sn valconv ptrconv
               (\rank psh poutv y' pstrides pv -> cf_strided rank psh poutv pstrides pv y') y arr

-- | The two shapes must be equal and non-empty. This is checked.
{-# NOINLINE wrapBinaryVV #-}
wrapBinaryVV :: forall a b n. Storable a
             => SNat n
             -> (Ptr a -> Ptr b)
             -> (Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> IO ())
             -> Array n a -> Array n a
             -> Array n a
-- TODO: do unreversing and unreplication on the input arrays (but
-- simultaneously: can only unreplicate if _both_ are replicated on that
-- dimension)
wrapBinaryVV sn@SNat ptrconv cf_strided
    (Array sh strides1 offset1 vec1)
    (Array sh2 strides2 offset2 vec2)
  | sh /= sh2 = error $ "wrapBinaryVV: unequal shapes: " ++ show sh ++ " and " ++ show sh2
  | any (<= 0) sh = error $ "wrapBinaryVV: empty shape: " ++ show sh
  | otherwise = unsafePerformIO $ do
      outv <- VSM.unsafeNew (product sh)
      VSM.unsafeWith outv $ \poutv ->
        VS.unsafeWith (VS.fromListN (fromSNat' sn) (map fromIntegral sh)) $ \psh ->
        VS.unsafeWith (VS.fromListN (fromSNat' sn) (map fromIntegral strides1)) $ \pstrides1 ->
        VS.unsafeWith (VS.fromListN (fromSNat' sn) (map fromIntegral strides2)) $ \pstrides2 ->
        VS.unsafeWith vec1 $ \pv1 ->
        VS.unsafeWith vec2 $ \pv2 ->
          let pv1' = pv1 `plusPtr` (offset1 * sizeOf (undefined :: a))
              pv2' = pv2 `plusPtr` (offset2 * sizeOf (undefined :: a))
          in cf_strided (fromIntegral (fromSNat' sn)) psh (ptrconv poutv) pstrides1 pv1' pstrides2 pv2'
      arrayFromVector sh <$> VS.unsafeFreeze outv

-- TODO: test handling of negative strides
-- | Reduce along the inner dimension
{-# NOINLINE vectorRedInnerOp #-}
vectorRedInnerOp :: forall a b n. (Num a, Storable a)
                 => SNat n
                 -> (a -> b)
                 -> (Ptr a -> Ptr b)
                 -> (Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ scale by constant
                 -> (Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())  -- ^ reduction kernel
                 -> Array (n + 1) a -> Array n a
vectorRedInnerOp sn@SNat valconv ptrconv fscale fred array@(Array sh strides offset vec)
  | null sh = error "unreachable"
  | last sh <= 0 = arrayFromConstant (init sh) 0
  | any (<= 0) (init sh) = Array (init sh) (0 <$ init strides) 0 VS.empty
  -- now the input array is nonempty
  | last sh == 1 = Array (init sh) (init strides) offset vec
  | last strides == 0 =
      wrapBinarySV sn valconv ptrconv fscale (fromIntegral @Int @a (last sh))
                   (Array (init sh) (init strides) offset vec)
  -- now there is useful work along the inner dimension
  -- Note that unreplication keeps the inner dimension intact, because `last strides /= 0` at this point.
  | otherwise =
      simplifyArray array $ \(Array sh' strides' offset' vec' :: Array n' a) _ _ _ restore -> unsafePerformIO $ do
        let ndims' = length sh'
        outv <- VSM.unsafeNew (product (init sh'))
        VSM.unsafeWith outv $ \poutv ->
          VS.unsafeWith (VS.fromListN ndims' (map fromIntegral sh')) $ \psh ->
          VS.unsafeWith (VS.fromListN ndims' (map fromIntegral strides')) $ \pstrides ->
          VS.unsafeWith vec' $ \pv ->
            let pv' = pv `plusPtr` (offset' * sizeOf (undefined :: a))
            in fred (fromIntegral ndims') (ptrconv poutv) psh pstrides (ptrconv pv')
        TN.withSomeSNat (fromIntegral (ndims' - 1)) $ \(SNat :: SNat n'm1) -> do
          (Dict :: Dict (1 <= n')) <- case cmpNat (natSing @1) (natSing @n') of
                                        LTI -> pure Dict
                                        EQI -> pure Dict
                                        _ -> error "impossible"  -- because `last strides /= 0`
          case sameNat (natSing @(n' - 1)) (natSing @n'm1) of
            Just Refl -> restore . arrayFromVector @_ @n'm1 (init sh') <$> VS.unsafeFreeze outv
            Nothing -> error "impossible"

-- TODO: test handling of negative strides
-- | Reduce full array
{-# NOINLINE vectorRedFullOp #-}
vectorRedFullOp :: forall a b n. (Num a, Storable a)
                => SNat n
                -> (a -> Int -> a)
                -> (b -> a)
                -> (Ptr a -> Ptr b)
                -> (Int64 -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO b)  -- ^ reduction kernel
                -> Array n a -> a
vectorRedFullOp _ scaleval valbackconv ptrconv fred array@(Array sh strides offset vec)
  | null sh = vec VS.! offset  -- 0D array has one element
  | any (<= 0) sh = 0
  -- now the input array is nonempty
  | all (== 0) strides = fromIntegral (product sh) * vec VS.! offset
  -- now there is at least one non-replicated dimension
  | otherwise =
      simplifyArray array $ \(Array sh' strides' offset' vec') unrepSize _ _ _ -> unsafePerformIO $ do
        let ndims' = length sh'
        VS.unsafeWith (VS.fromListN ndims' (map fromIntegral sh')) $ \psh ->
          VS.unsafeWith (VS.fromListN ndims' (map fromIntegral strides')) $ \pstrides ->
          VS.unsafeWith vec' $ \pv ->
            let pv' = pv `plusPtr` (offset' * sizeOf (undefined :: a))
            in (`scaleval` unrepSize) . valbackconv
                 <$> fred (fromIntegral ndims') psh pstrides (ptrconv pv')

-- TODO: test this function
-- | Find extremum (minindex ("argmin") or maxindex) in full array
{-# NOINLINE vectorExtremumOp #-}
vectorExtremumOp :: forall a b n. Storable a
                 => (Ptr a -> Ptr b)
                 -> (Ptr Int64 -> Int64 -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())  -- ^ extremum kernel
                 -> Array n a -> [Int]  -- result length: n
vectorExtremumOp ptrconv fextrem array@(Array sh strides _ _)
  | null sh = []
  | any (<= 0) sh = error "Extremum (minindex/maxindex): empty array"
  -- now the input array is nonempty
  | all (== 0) strides = 0 <$ sh
  -- now there is at least one non-replicated dimension
  | otherwise =
      simplifyArray array $ \(Array sh' strides' offset' vec') _ upindex _ _ -> unsafePerformIO $ do
        let ndims' = length sh'
        outvR <- VSM.unsafeNew (length sh')
        VSM.unsafeWith outvR $ \poutv ->
          VS.unsafeWith (VS.fromListN ndims' (map fromIntegral sh')) $ \psh ->
          VS.unsafeWith (VS.fromListN ndims' (map fromIntegral strides')) $ \pstrides ->
          VS.unsafeWith vec' $ \pv ->
            let pv' = pv `plusPtr` (offset' * sizeOf (undefined :: a))
            in fextrem poutv (fromIntegral ndims') psh pstrides (ptrconv pv')
        upindex . map (fromIntegral @Int64 @Int) . VS.toList <$> VS.unsafeFreeze outvR

{-# NOINLINE vectorDotprodInnerOp #-}
vectorDotprodInnerOp :: forall a b n. (Num a, Storable a)
                     => SNat n
                     -> (a -> b)
                     -> (Ptr a -> Ptr b)
                     -> (SNat n -> Array n a -> Array n a -> Array n a)  -- ^ elementwise multiplication
                     -> (Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ scale by constant
                     -> (Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())  -- ^ reduction kernel
                     -> (Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ dotprod kernel
                     -> Array (n + 1) a -> Array (n + 1) a -> Array n a
vectorDotprodInnerOp sn@SNat valconv ptrconv fmul fscale fred fdotinner
    arr1@(Array sh1 strides1 offset1 vec1)
    arr2@(Array sh2 strides2 offset2 vec2)
  | null sh1 || null sh2 = error "unreachable"
  | sh1 /= sh2 = error $ "vectorDotprodInnerOp: shapes unequal: " ++ show sh1 ++ " vs " ++ show sh2
  | last sh1 <= 0 = arrayFromConstant (init sh1) 0
  | any (<= 0) (init sh1) = Array (init sh1) (0 <$ init strides1) 0 VS.empty
  -- now the input arrays are nonempty
  | last sh1 == 1 =
      fmul sn (Array (init sh1) (init strides1) offset1 vec1)
              (Array (init sh2) (init strides2) offset2 vec2)
  | last strides1 == 0 =
      fmul sn
        (Array (init sh1) (init strides1) offset1 vec1)
        (vectorRedInnerOp sn valconv ptrconv fscale fred arr2)
  | last strides2 == 0 =
      fmul sn
        (vectorRedInnerOp sn valconv ptrconv fscale fred arr1)
        (Array (init sh2) (init strides2) offset2 vec2)
  -- now there is useful dotprod work along the inner dimension
  | otherwise =
      simplifyArray2 arr1 arr2 $ \(Array sh' strides1' offset1' vec1' :: Array n' a) (Array _ strides2' offset2' vec2') _ _ _ restore ->
      unsafePerformIO $ do
        let inrank = length sh'
        outv <- VSM.unsafeNew (product (init sh'))
        VSM.unsafeWith outv $ \poutv ->
          VS.unsafeWith (VS.fromListN inrank (map fromIntegral sh')) $ \psh ->
          VS.unsafeWith (VS.fromListN inrank (map fromIntegral strides1')) $ \pstrides1 ->
          VS.unsafeWith vec1' $ \pvec1 ->
          VS.unsafeWith (VS.fromListN inrank (map fromIntegral strides2')) $ \pstrides2 ->
          VS.unsafeWith vec2' $ \pvec2 ->
            fdotinner (fromIntegral @Int @Int64 inrank) psh (ptrconv poutv)
                      pstrides1 (ptrconv pvec1 `plusPtr` (sizeOf (undefined :: a) * offset1'))
                      pstrides2 (ptrconv pvec2 `plusPtr` (sizeOf (undefined :: a) * offset2'))
        TN.withSomeSNat (fromIntegral (inrank - 1)) $ \(SNat :: SNat n'm1) -> do
          (Dict :: Dict (1 <= n')) <- case cmpNat (natSing @1) (natSing @n') of
                                        LTI -> pure Dict
                                        EQI -> pure Dict
                                        GTI -> error "impossible"  -- because `last strides1 /= 0`
          case sameNat (natSing @(n' - 1)) (natSing @n'm1) of
            Just Refl -> restore . arrayFromVector (init sh') <$> VS.unsafeFreeze outv
            Nothing -> error "impossible"

mulWithInt :: Num a => a -> Int -> a
mulWithInt a i = a * fromIntegral i


$(fmap concat . forM typesList $ \arithtype -> do
    let ttyp = conT (atType arithtype)
    fmap concat . forM [minBound..maxBound] $ \arithop -> do
      let name = mkName (aboName arithop ++ "Vector" ++ nameBase (atType arithtype))
          cnamebase = "c_binary_" ++ atCName arithtype
          c_ss_str = varE (aboNumOp arithop)
          c_sv_str = varE (mkName (cnamebase ++ "_sv_strided")) `appE` litE (integerL (fromIntegral (aboEnum arithop)))
          c_vs_str = varE (mkName (cnamebase ++ "_vs_strided")) `appE` litE (integerL (fromIntegral (aboEnum arithop)))
          c_vv_str = varE (mkName (cnamebase ++ "_vv_strided")) `appE` litE (integerL (fromIntegral (aboEnum arithop)))
      sequence [SigD name <$>
                     [t| forall n. SNat n -> Array n $ttyp -> Array n $ttyp -> Array n $ttyp |]
               ,do body <- [| \sn -> liftOpEltwise2 sn id id $c_ss_str $c_sv_str $c_vs_str $c_vv_str |]
                   return $ FunD name [Clause [] (NormalB body) []]])

$(fmap concat . forM intTypesList $ \arithtype -> do
    let ttyp = conT (atType arithtype)
    fmap concat . forM [minBound..maxBound] $ \arithop -> do
      let name = mkName (aiboName arithop ++ "Vector" ++ nameBase (atType arithtype))
          cnamebase = "c_ibinary_" ++ atCName arithtype
          c_ss_str = varE (aiboNumOp arithop)
          c_sv_str = varE (mkName (cnamebase ++ "_sv_strided")) `appE` litE (integerL (fromIntegral (aiboEnum arithop)))
          c_vs_str = varE (mkName (cnamebase ++ "_vs_strided")) `appE` litE (integerL (fromIntegral (aiboEnum arithop)))
          c_vv_str = varE (mkName (cnamebase ++ "_vv_strided")) `appE` litE (integerL (fromIntegral (aiboEnum arithop)))
      sequence [SigD name <$>
                     [t| forall n. SNat n -> Array n $ttyp -> Array n $ttyp -> Array n $ttyp |]
               ,do body <- [| \sn -> liftOpEltwise2 sn id id $c_ss_str $c_sv_str $c_vs_str $c_vv_str |]
                   return $ FunD name [Clause [] (NormalB body) []]])

$(fmap concat . forM floatTypesList $ \arithtype -> do
    let ttyp = conT (atType arithtype)
    fmap concat . forM [minBound..maxBound] $ \arithop -> do
      let name = mkName (afboName arithop ++ "Vector" ++ nameBase (atType arithtype))
          cnamebase = "c_fbinary_" ++ atCName arithtype
          c_ss_str = varE (afboNumOp arithop)
          c_sv_str = varE (mkName (cnamebase ++ "_sv_strided")) `appE` litE (integerL (fromIntegral (afboEnum arithop)))
          c_vs_str = varE (mkName (cnamebase ++ "_vs_strided")) `appE` litE (integerL (fromIntegral (afboEnum arithop)))
          c_vv_str = varE (mkName (cnamebase ++ "_vv_strided")) `appE` litE (integerL (fromIntegral (afboEnum arithop)))
      sequence [SigD name <$>
                     [t| forall n. SNat n -> Array n $ttyp -> Array n $ttyp -> Array n $ttyp |]
               ,do body <- [| \sn -> liftOpEltwise2 sn id id $c_ss_str $c_sv_str $c_vs_str $c_vv_str |]
                   return $ FunD name [Clause [] (NormalB body) []]])

$(fmap concat . forM typesList $ \arithtype -> do
    let ttyp = conT (atType arithtype)
    fmap concat . forM [minBound..maxBound] $ \arithop -> do
      let name = mkName (auoName arithop ++ "Vector" ++ nameBase (atType arithtype))
          c_op_strided = varE (mkName ("c_unary_" ++ atCName arithtype ++ "_strided")) `appE` litE (integerL (fromIntegral (auoEnum arithop)))
      sequence [SigD name <$>
                     [t| forall n. SNat n -> Array n $ttyp -> Array n $ttyp |]
               ,do body <- [| \sn -> liftOpEltwise1 sn id $c_op_strided |]
                   return $ FunD name [Clause [] (NormalB body) []]])

$(fmap concat . forM floatTypesList $ \arithtype -> do
    let ttyp = conT (atType arithtype)
    fmap concat . forM [minBound..maxBound] $ \arithop -> do
      let name = mkName (afuoName arithop ++ "Vector" ++ nameBase (atType arithtype))
          c_op_strided = varE (mkName ("c_funary_" ++ atCName arithtype ++ "_strided")) `appE` litE (integerL (fromIntegral (afuoEnum arithop)))
      sequence [SigD name <$>
                     [t| forall n. SNat n -> Array n $ttyp -> Array n $ttyp |]
               ,do body <- [| \sn -> liftOpEltwise1 sn id $c_op_strided |]
                   return $ FunD name [Clause [] (NormalB body) []]])

$(fmap concat . forM typesList $ \arithtype -> do
    let ttyp = conT (atType arithtype)
    fmap concat . forM [minBound..maxBound] $ \arithop -> do
      let scaleVar = case arithop of
                       RO_SUM -> varE 'mulWithInt
                       RO_PRODUCT -> varE '(^)
      let name1 = mkName (aroName arithop ++ "1Vector" ++ nameBase (atType arithtype))
          namefull = mkName (aroName arithop ++ "FullVector" ++ nameBase (atType arithtype))
          c_op1 = varE (mkName ("c_reduce1_" ++ atCName arithtype)) `appE` litE (integerL (fromIntegral (aroEnum arithop)))
          c_opfull = varE (mkName ("c_reducefull_" ++ atCName arithtype)) `appE` litE (integerL (fromIntegral (aroEnum arithop)))
          c_scale_op = varE (mkName ("c_binary_" ++ atCName arithtype ++ "_sv_strided")) `appE` litE (integerL (fromIntegral (aboEnum BO_MUL)))
      sequence [SigD name1 <$>
                     [t| forall n. SNat n -> Array (n + 1) $ttyp -> Array n $ttyp |]
               ,do body <- [| \sn -> vectorRedInnerOp sn id id $c_scale_op $c_op1 |]
                   return $ FunD name1 [Clause [] (NormalB body) []]
               ,SigD namefull <$>
                     [t| forall n. SNat n -> Array n $ttyp -> $ttyp |]
               ,do body <- [| \sn -> vectorRedFullOp sn $scaleVar id id $c_opfull |]
                   return $ FunD namefull [Clause [] (NormalB body) []]
               ])

$(fmap concat . forM typesList $ \arithtype ->
    fmap concat . forM ["min", "max"] $ \fname -> do
      let ttyp = conT (atType arithtype)
          name = mkName (fname ++ "indexVector" ++ nameBase (atType arithtype))
          c_op = varE (mkName ("c_extremum_" ++ fname ++ "_" ++ atCName arithtype))
      sequence [SigD name <$>
                     [t| forall n. Array n $ttyp -> [Int] |]
               ,do body <- [| vectorExtremumOp id $c_op |]
                   return $ FunD name [Clause [] (NormalB body) []]])

$(fmap concat . forM typesList $ \arithtype -> do
    let ttyp = conT (atType arithtype)
        name = mkName ("dotprodinnerVector" ++ nameBase (atType arithtype))
        c_op = varE (mkName ("c_dotprodinner_" ++ atCName arithtype))
        mul_op = varE (mkName ("mulVector" ++ nameBase (atType arithtype)))
        c_scale_op = varE (mkName ("c_binary_" ++ atCName arithtype ++ "_sv_strided")) `appE` litE (integerL (fromIntegral (aboEnum BO_MUL)))
        c_red_op = varE (mkName ("c_reduce1_" ++ atCName arithtype)) `appE` litE (integerL (fromIntegral (aroEnum RO_SUM)))
    sequence [SigD name <$>
                   [t| forall n. SNat n -> Array (n + 1) $ttyp -> Array (n + 1) $ttyp -> Array n $ttyp |]
             ,do body <- [| \sn -> vectorDotprodInnerOp sn id id $mul_op $c_scale_op $c_red_op $c_op |]
                 return $ FunD name [Clause [] (NormalB body) []]])

foreign import ccall unsafe "oxarrays_stats_enable" c_stats_enable :: Int32 -> IO ()
foreign import ccall unsafe "oxarrays_stats_print_all" c_stats_print_all :: IO ()

statisticsEnable :: Bool -> IO ()
statisticsEnable b = c_stats_enable (if b then 1 else 0)

-- | Consumes the log: one particular event will only ever be printed once,
-- even if statisticsPrintAll is called multiple times.
statisticsPrintAll :: IO ()
statisticsPrintAll = do
  hFlush stdout  -- lower the chance of overlapping output
  c_stats_print_all

-- This branch is ostensibly a runtime branch, but will (hopefully) be
-- constant-folded away by GHC.
intWidBranch1 :: forall i n. (FiniteBits i, Storable i)
              => (forall b. b ~ Int32 => Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())
              -> (forall b. b ~ Int64 => Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())
              -> (SNat n -> Array n i -> Array n i)
intWidBranch1 f32 f64 sn
  | finiteBitSize (undefined :: i) == 32 = liftOpEltwise1 sn castPtr f32
  | finiteBitSize (undefined :: i) == 64 = liftOpEltwise1 sn castPtr f64
  | otherwise = error "Unsupported Int width"

intWidBranch2 :: forall i n. (FiniteBits i, Storable i, Integral i)
              => (i -> i -> i)  -- ss
                 -- int32
              -> (forall b. b ~ Int32 => Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())  -- sv
              -> (forall b. b ~ Int32 => Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> b -> IO ())  -- vs
              -> (forall b. b ~ Int32 => Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> IO ())  -- vv
                 -- int64
              -> (forall b. b ~ Int64 => Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())  -- sv
              -> (forall b. b ~ Int64 => Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> b -> IO ())  -- vs
              -> (forall b. b ~ Int64 => Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> IO ())  -- vv
              -> (SNat n -> Array n i -> Array n i -> Array n i)
intWidBranch2 ss sv32 vs32 vv32 sv64 vs64 vv64 sn
  | finiteBitSize (undefined :: i) == 32 = liftOpEltwise2 sn fromIntegral castPtr ss sv32 vs32 vv32
  | finiteBitSize (undefined :: i) == 64 = liftOpEltwise2 sn fromIntegral castPtr ss sv64 vs64 vv64
  | otherwise = error "Unsupported Int width"

intWidBranchRed1 :: forall i n. (FiniteBits i, Storable i, Integral i)
                 => -- int32
                    (forall b. b ~ Int32 => Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ scale by constant
                 -> (forall b. b ~ Int32 => Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())  -- ^ reduction kernel
                    -- int64
                 -> (forall b. b ~ Int64 => Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ scale by constant
                 -> (forall b. b ~ Int64 => Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())  -- ^ reduction kernel
                 -> (SNat n -> Array (n + 1) i -> Array n i)
intWidBranchRed1 fsc32 fred32 fsc64 fred64 sn
  | finiteBitSize (undefined :: i) == 32 = vectorRedInnerOp @i @Int32 sn fromIntegral castPtr fsc32 fred32
  | finiteBitSize (undefined :: i) == 64 = vectorRedInnerOp @i @Int64 sn fromIntegral castPtr fsc64 fred64
  | otherwise = error "Unsupported Int width"

intWidBranchRedFull :: forall i n. (FiniteBits i, Storable i, Integral i)
                    => (i -> Int -> i)  -- ^ scale op
                       -- int32
                    -> (forall b. b ~ Int32 => Int64 -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO b)  -- ^ reduction kernel
                       -- int64
                    -> (forall b. b ~ Int64 => Int64 -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO b)  -- ^ reduction kernel
                    -> (SNat n -> Array n i -> i)
intWidBranchRedFull fsc fred32 fred64 sn
  | finiteBitSize (undefined :: i) == 32 = vectorRedFullOp @i @Int32 sn fsc fromIntegral castPtr fred32
  | finiteBitSize (undefined :: i) == 64 = vectorRedFullOp @i @Int64 sn fsc fromIntegral castPtr fred64
  | otherwise = error "Unsupported Int width"

intWidBranchExtr :: forall i n. (FiniteBits i, Storable i)
                 => -- int32
                    (forall b. b ~ Int32 => Ptr Int64 -> Int64 -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())  -- ^ extremum kernel
                    -- int64
                 -> (forall b. b ~ Int64 => Ptr Int64 -> Int64 -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())  -- ^ extremum kernel
                 -> (Array n i -> [Int])
intWidBranchExtr fextr32 fextr64
  | finiteBitSize (undefined :: i) == 32 = vectorExtremumOp @i @Int32 castPtr fextr32
  | finiteBitSize (undefined :: i) == 64 = vectorExtremumOp @i @Int64 castPtr fextr64
  | otherwise = error "Unsupported Int width"

intWidBranchDotprod :: forall i n. (FiniteBits i, Storable i, Integral i, NumElt i)
                    => -- int32
                       (forall b. b ~ Int32 => Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ scale by constant
                    -> (forall b. b ~ Int32 => Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())  -- ^ reduction kernel
                    -> (forall b. b ~ Int32 => Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ dotprod kernel
                       -- int64
                    -> (forall b. b ~ Int64 => Int64 -> Ptr Int64 -> Ptr b -> b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ scale by constant
                    -> (forall b. b ~ Int64 => Int64 -> Ptr b -> Ptr Int64 -> Ptr Int64 -> Ptr b -> IO ())  -- ^ reduction kernel
                    -> (forall b. b ~ Int64 => Int64 -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> Ptr Int64 -> Ptr b -> IO ())  -- ^ dotprod kernel
                    -> (SNat n -> Array (n + 1) i -> Array (n + 1) i -> Array n i)
intWidBranchDotprod fsc32 fred32 fdot32 fsc64 fred64 fdot64 sn
  | finiteBitSize (undefined :: i) == 32 = vectorDotprodInnerOp @i @Int32 sn fromIntegral castPtr numEltMul fsc32 fred32 fdot32
  | finiteBitSize (undefined :: i) == 64 = vectorDotprodInnerOp @i @Int64 sn fromIntegral castPtr numEltMul fsc64 fred64 fdot64
  | otherwise = error "Unsupported Int width"

class NumElt a where
  numEltAdd :: SNat n -> Array n a -> Array n a -> Array n a
  numEltSub :: SNat n -> Array n a -> Array n a -> Array n a
  numEltMul :: SNat n -> Array n a -> Array n a -> Array n a
  numEltNeg :: SNat n -> Array n a -> Array n a
  numEltAbs :: SNat n -> Array n a -> Array n a
  numEltSignum :: SNat n -> Array n a -> Array n a
  numEltSum1Inner :: SNat n -> Array (n + 1) a -> Array n a
  numEltProduct1Inner :: SNat n -> Array (n + 1) a -> Array n a
  numEltSumFull :: SNat n -> Array n a -> a
  numEltProductFull :: SNat n -> Array n a -> a
  numEltMinIndex :: SNat n -> Array n a -> [Int]
  numEltMaxIndex :: SNat n -> Array n a -> [Int]
  numEltDotprodInner :: SNat n -> Array (n + 1) a -> Array (n + 1) a -> Array n a

instance NumElt Int8 where
  numEltAdd = addVectorInt8
  numEltSub = subVectorInt8
  numEltMul = mulVectorInt8
  numEltNeg = negVectorInt8
  numEltAbs = absVectorInt8
  numEltSignum = signumVectorInt8
  numEltSum1Inner = sum1VectorInt8
  numEltProduct1Inner = product1VectorInt8
  numEltSumFull = sumFullVectorInt8
  numEltProductFull = productFullVectorInt8
  numEltMinIndex _ = minindexVectorInt8
  numEltMaxIndex _ = maxindexVectorInt8
  numEltDotprodInner = dotprodinnerVectorInt8

instance NumElt Int16 where
  numEltAdd = addVectorInt16
  numEltSub = subVectorInt16
  numEltMul = mulVectorInt16
  numEltNeg = negVectorInt16
  numEltAbs = absVectorInt16
  numEltSignum = signumVectorInt16
  numEltSum1Inner = sum1VectorInt16
  numEltProduct1Inner = product1VectorInt16
  numEltSumFull = sumFullVectorInt16
  numEltProductFull = productFullVectorInt16
  numEltMinIndex _ = minindexVectorInt16
  numEltMaxIndex _ = maxindexVectorInt16
  numEltDotprodInner = dotprodinnerVectorInt16

instance NumElt Int32 where
  numEltAdd = addVectorInt32
  numEltSub = subVectorInt32
  numEltMul = mulVectorInt32
  numEltNeg = negVectorInt32
  numEltAbs = absVectorInt32
  numEltSignum = signumVectorInt32
  numEltSum1Inner = sum1VectorInt32
  numEltProduct1Inner = product1VectorInt32
  numEltSumFull = sumFullVectorInt32
  numEltProductFull = productFullVectorInt32
  numEltMinIndex _ = minindexVectorInt32
  numEltMaxIndex _ = maxindexVectorInt32
  numEltDotprodInner = dotprodinnerVectorInt32

instance NumElt Int64 where
  numEltAdd = addVectorInt64
  numEltSub = subVectorInt64
  numEltMul = mulVectorInt64
  numEltNeg = negVectorInt64
  numEltAbs = absVectorInt64
  numEltSignum = signumVectorInt64
  numEltSum1Inner = sum1VectorInt64
  numEltProduct1Inner = product1VectorInt64
  numEltSumFull = sumFullVectorInt64
  numEltProductFull = productFullVectorInt64
  numEltMinIndex _ = minindexVectorInt64
  numEltMaxIndex _ = maxindexVectorInt64
  numEltDotprodInner = dotprodinnerVectorInt64

instance NumElt Float where
  numEltAdd = addVectorFloat
  numEltSub = subVectorFloat
  numEltMul = mulVectorFloat
  numEltNeg = negVectorFloat
  numEltAbs = absVectorFloat
  numEltSignum = signumVectorFloat
  numEltSum1Inner = sum1VectorFloat
  numEltProduct1Inner = product1VectorFloat
  numEltSumFull = sumFullVectorFloat
  numEltProductFull = productFullVectorFloat
  numEltMinIndex _ = minindexVectorFloat
  numEltMaxIndex _ = maxindexVectorFloat
  numEltDotprodInner = dotprodinnerVectorFloat

instance NumElt Double where
  numEltAdd = addVectorDouble
  numEltSub = subVectorDouble
  numEltMul = mulVectorDouble
  numEltNeg = negVectorDouble
  numEltAbs = absVectorDouble
  numEltSignum = signumVectorDouble
  numEltSum1Inner = sum1VectorDouble
  numEltProduct1Inner = product1VectorDouble
  numEltSumFull = sumFullVectorDouble
  numEltProductFull = productFullVectorDouble
  numEltMinIndex _ = minindexVectorDouble
  numEltMaxIndex _ = maxindexVectorDouble
  numEltDotprodInner = dotprodinnerVectorDouble

instance NumElt Int where
  numEltAdd = intWidBranch2 @Int (+)
                (c_binary_i32_sv_strided (aboEnum BO_ADD)) (c_binary_i32_vs_strided (aboEnum BO_ADD)) (c_binary_i32_vv_strided (aboEnum BO_ADD))
                (c_binary_i64_sv_strided (aboEnum BO_ADD)) (c_binary_i64_vs_strided (aboEnum BO_ADD)) (c_binary_i64_vv_strided (aboEnum BO_ADD))
  numEltSub = intWidBranch2 @Int (-)
                (c_binary_i32_sv_strided (aboEnum BO_SUB)) (c_binary_i32_vs_strided (aboEnum BO_SUB)) (c_binary_i32_vv_strided (aboEnum BO_SUB))
                (c_binary_i64_sv_strided (aboEnum BO_SUB)) (c_binary_i64_vs_strided (aboEnum BO_SUB)) (c_binary_i64_vv_strided (aboEnum BO_SUB))
  numEltMul = intWidBranch2 @Int (*)
                (c_binary_i32_sv_strided (aboEnum BO_MUL)) (c_binary_i32_vs_strided (aboEnum BO_MUL)) (c_binary_i32_vv_strided (aboEnum BO_MUL))
                (c_binary_i64_sv_strided (aboEnum BO_MUL)) (c_binary_i64_vs_strided (aboEnum BO_MUL)) (c_binary_i64_vv_strided (aboEnum BO_MUL))
  numEltNeg = intWidBranch1 @Int (c_unary_i32_strided (auoEnum UO_NEG)) (c_unary_i64_strided (auoEnum UO_NEG))
  numEltAbs = intWidBranch1 @Int (c_unary_i32_strided (auoEnum UO_ABS)) (c_unary_i64_strided (auoEnum UO_ABS))
  numEltSignum = intWidBranch1 @Int (c_unary_i32_strided (auoEnum UO_SIGNUM)) (c_unary_i64_strided (auoEnum UO_SIGNUM))
  numEltSum1Inner = intWidBranchRed1 @Int
                      (c_binary_i32_sv_strided (aboEnum BO_MUL)) (c_reduce1_i32 (aroEnum RO_SUM))
                      (c_binary_i64_sv_strided (aboEnum BO_MUL)) (c_reduce1_i64 (aroEnum RO_SUM))
  numEltProduct1Inner = intWidBranchRed1 @Int
                          (c_binary_i32_sv_strided (aboEnum BO_MUL)) (c_reduce1_i32 (aroEnum RO_PRODUCT))
                          (c_binary_i64_sv_strided (aboEnum BO_MUL)) (c_reduce1_i64 (aroEnum RO_PRODUCT))
  numEltSumFull = intWidBranchRedFull @Int (*) (c_reducefull_i32 (aroEnum RO_SUM)) (c_reducefull_i64 (aroEnum RO_SUM))
  numEltProductFull = intWidBranchRedFull @Int (^) (c_reducefull_i32 (aroEnum RO_PRODUCT)) (c_reducefull_i64 (aroEnum RO_PRODUCT))
  numEltMinIndex _ = intWidBranchExtr @Int c_extremum_min_i32 c_extremum_min_i64
  numEltMaxIndex _ = intWidBranchExtr @Int c_extremum_max_i32 c_extremum_max_i64
  numEltDotprodInner = intWidBranchDotprod @Int (c_binary_i32_sv_strided (aboEnum BO_MUL)) (c_reduce1_i32 (aroEnum RO_SUM)) c_dotprodinner_i32
                                                (c_binary_i64_sv_strided (aboEnum BO_MUL)) (c_reduce1_i64 (aroEnum RO_SUM)) c_dotprodinner_i64

instance NumElt CInt where
  numEltAdd = intWidBranch2 @CInt (+)
                (c_binary_i32_sv_strided (aboEnum BO_ADD)) (c_binary_i32_vs_strided (aboEnum BO_ADD)) (c_binary_i32_vv_strided (aboEnum BO_ADD))
                (c_binary_i64_sv_strided (aboEnum BO_ADD)) (c_binary_i64_vs_strided (aboEnum BO_ADD)) (c_binary_i64_vv_strided (aboEnum BO_ADD))
  numEltSub = intWidBranch2 @CInt (-)
                (c_binary_i32_sv_strided (aboEnum BO_SUB)) (c_binary_i32_vs_strided (aboEnum BO_SUB)) (c_binary_i32_vv_strided (aboEnum BO_SUB))
                (c_binary_i64_sv_strided (aboEnum BO_SUB)) (c_binary_i64_vs_strided (aboEnum BO_SUB)) (c_binary_i64_vv_strided (aboEnum BO_SUB))
  numEltMul = intWidBranch2 @CInt (*)
                (c_binary_i32_sv_strided (aboEnum BO_MUL)) (c_binary_i32_vs_strided (aboEnum BO_MUL)) (c_binary_i32_vv_strided (aboEnum BO_MUL))
                (c_binary_i64_sv_strided (aboEnum BO_MUL)) (c_binary_i64_vs_strided (aboEnum BO_MUL)) (c_binary_i64_vv_strided (aboEnum BO_MUL))
  numEltNeg = intWidBranch1 @CInt (c_unary_i32_strided (auoEnum UO_NEG)) (c_unary_i64_strided (auoEnum UO_NEG))
  numEltAbs = intWidBranch1 @CInt (c_unary_i32_strided (auoEnum UO_ABS)) (c_unary_i64_strided (auoEnum UO_ABS))
  numEltSignum = intWidBranch1 @CInt (c_unary_i32_strided (auoEnum UO_SIGNUM)) (c_unary_i64_strided (auoEnum UO_SIGNUM))
  numEltSum1Inner = intWidBranchRed1 @CInt
                      (c_binary_i32_sv_strided (aboEnum BO_MUL)) (c_reduce1_i32 (aroEnum RO_SUM))
                      (c_binary_i64_sv_strided (aboEnum BO_MUL)) (c_reduce1_i64 (aroEnum RO_SUM))
  numEltProduct1Inner = intWidBranchRed1 @CInt
                          (c_binary_i32_sv_strided (aboEnum BO_MUL)) (c_reduce1_i32 (aroEnum RO_PRODUCT))
                          (c_binary_i64_sv_strided (aboEnum BO_MUL)) (c_reduce1_i64 (aroEnum RO_PRODUCT))
  numEltSumFull = intWidBranchRedFull @CInt mulWithInt (c_reducefull_i32 (aroEnum RO_SUM)) (c_reducefull_i64 (aroEnum RO_SUM))
  numEltProductFull = intWidBranchRedFull @CInt (^) (c_reducefull_i32 (aroEnum RO_PRODUCT)) (c_reducefull_i64 (aroEnum RO_PRODUCT))
  numEltMinIndex _ = intWidBranchExtr @CInt c_extremum_min_i32 c_extremum_min_i64
  numEltMaxIndex _ = intWidBranchExtr @CInt c_extremum_max_i32 c_extremum_max_i64
  numEltDotprodInner = intWidBranchDotprod @CInt (c_binary_i32_sv_strided (aboEnum BO_MUL)) (c_reduce1_i32 (aroEnum RO_SUM)) c_dotprodinner_i32
                                                 (c_binary_i64_sv_strided (aboEnum BO_MUL)) (c_reduce1_i64 (aroEnum RO_SUM)) c_dotprodinner_i64

class NumElt a => IntElt a where
  intEltQuot :: SNat n -> Array n a -> Array n a -> Array n a
  intEltRem :: SNat n -> Array n a -> Array n a -> Array n a

instance IntElt Int8 where
  intEltQuot = quotVectorInt8
  intEltRem = remVectorInt8

instance IntElt Int16 where
  intEltQuot = quotVectorInt16
  intEltRem = remVectorInt16

instance IntElt Int32 where
  intEltQuot = quotVectorInt32
  intEltRem = remVectorInt32

instance IntElt Int64 where
  intEltQuot = quotVectorInt64
  intEltRem = remVectorInt64

instance IntElt Int where
  intEltQuot = intWidBranch2 @Int quot
                 (c_ibinary_i32_sv_strided (aiboEnum IB_QUOT)) (c_ibinary_i32_vs_strided (aiboEnum IB_QUOT)) (c_ibinary_i32_vv_strided (aiboEnum IB_QUOT))
                 (c_ibinary_i64_sv_strided (aiboEnum IB_QUOT)) (c_ibinary_i64_vs_strided (aiboEnum IB_QUOT)) (c_ibinary_i64_vv_strided (aiboEnum IB_QUOT))
  intEltRem = intWidBranch2 @Int rem
                (c_ibinary_i32_sv_strided (aiboEnum IB_REM)) (c_ibinary_i32_vs_strided (aiboEnum IB_REM)) (c_ibinary_i32_vv_strided (aiboEnum IB_REM))
                (c_ibinary_i64_sv_strided (aiboEnum IB_REM)) (c_ibinary_i64_vs_strided (aiboEnum IB_REM)) (c_ibinary_i64_vv_strided (aiboEnum IB_REM))

instance IntElt CInt where
  intEltQuot = intWidBranch2 @CInt quot
                 (c_ibinary_i32_sv_strided (aiboEnum IB_QUOT)) (c_ibinary_i32_vs_strided (aiboEnum IB_QUOT)) (c_ibinary_i32_vv_strided (aiboEnum IB_QUOT))
                 (c_ibinary_i64_sv_strided (aiboEnum IB_QUOT)) (c_ibinary_i64_vs_strided (aiboEnum IB_QUOT)) (c_ibinary_i64_vv_strided (aiboEnum IB_QUOT))
  intEltRem = intWidBranch2 @CInt rem
                (c_ibinary_i32_sv_strided (aiboEnum IB_REM)) (c_ibinary_i32_vs_strided (aiboEnum IB_REM)) (c_ibinary_i32_vv_strided (aiboEnum IB_REM))
                (c_ibinary_i64_sv_strided (aiboEnum IB_REM)) (c_ibinary_i64_vs_strided (aiboEnum IB_REM)) (c_ibinary_i64_vv_strided (aiboEnum IB_REM))

class NumElt a => FloatElt a where
  floatEltDiv :: SNat n -> Array n a -> Array n a -> Array n a
  floatEltPow :: SNat n -> Array n a -> Array n a -> Array n a
  floatEltLogbase :: SNat n -> Array n a -> Array n a -> Array n a
  floatEltRecip :: SNat n -> Array n a -> Array n a
  floatEltExp :: SNat n -> Array n a -> Array n a
  floatEltLog :: SNat n -> Array n a -> Array n a
  floatEltSqrt :: SNat n -> Array n a -> Array n a
  floatEltSin :: SNat n -> Array n a -> Array n a
  floatEltCos :: SNat n -> Array n a -> Array n a
  floatEltTan :: SNat n -> Array n a -> Array n a
  floatEltAsin :: SNat n -> Array n a -> Array n a
  floatEltAcos :: SNat n -> Array n a -> Array n a
  floatEltAtan :: SNat n -> Array n a -> Array n a
  floatEltSinh :: SNat n -> Array n a -> Array n a
  floatEltCosh :: SNat n -> Array n a -> Array n a
  floatEltTanh :: SNat n -> Array n a -> Array n a
  floatEltAsinh :: SNat n -> Array n a -> Array n a
  floatEltAcosh :: SNat n -> Array n a -> Array n a
  floatEltAtanh :: SNat n -> Array n a -> Array n a
  floatEltLog1p :: SNat n -> Array n a -> Array n a
  floatEltExpm1 :: SNat n -> Array n a -> Array n a
  floatEltLog1pexp :: SNat n -> Array n a -> Array n a
  floatEltLog1mexp :: SNat n -> Array n a -> Array n a
  floatEltAtan2 :: SNat n -> Array n a -> Array n a -> Array n a

instance FloatElt Float where
  floatEltDiv = divVectorFloat
  floatEltPow = powVectorFloat
  floatEltLogbase = logbaseVectorFloat
  floatEltRecip = recipVectorFloat
  floatEltExp = expVectorFloat
  floatEltLog = logVectorFloat
  floatEltSqrt = sqrtVectorFloat
  floatEltSin = sinVectorFloat
  floatEltCos = cosVectorFloat
  floatEltTan = tanVectorFloat
  floatEltAsin = asinVectorFloat
  floatEltAcos = acosVectorFloat
  floatEltAtan = atanVectorFloat
  floatEltSinh = sinhVectorFloat
  floatEltCosh = coshVectorFloat
  floatEltTanh = tanhVectorFloat
  floatEltAsinh = asinhVectorFloat
  floatEltAcosh = acoshVectorFloat
  floatEltAtanh = atanhVectorFloat
  floatEltLog1p = log1pVectorFloat
  floatEltExpm1 = expm1VectorFloat
  floatEltLog1pexp = log1pexpVectorFloat
  floatEltLog1mexp = log1mexpVectorFloat
  floatEltAtan2 = atan2VectorFloat

instance FloatElt Double where
  floatEltDiv = divVectorDouble
  floatEltPow = powVectorDouble
  floatEltLogbase = logbaseVectorDouble
  floatEltRecip = recipVectorDouble
  floatEltExp = expVectorDouble
  floatEltLog = logVectorDouble
  floatEltSqrt = sqrtVectorDouble
  floatEltSin = sinVectorDouble
  floatEltCos = cosVectorDouble
  floatEltTan = tanVectorDouble
  floatEltAsin = asinVectorDouble
  floatEltAcos = acosVectorDouble
  floatEltAtan = atanVectorDouble
  floatEltSinh = sinhVectorDouble
  floatEltCosh = coshVectorDouble
  floatEltTanh = tanhVectorDouble
  floatEltAsinh = asinhVectorDouble
  floatEltAcosh = acoshVectorDouble
  floatEltAtanh = atanhVectorDouble
  floatEltLog1p = log1pVectorDouble
  floatEltExpm1 = expm1VectorDouble
  floatEltLog1pexp = log1pexpVectorDouble
  floatEltLog1mexp = log1mexpVectorDouble
  floatEltAtan2 = atan2VectorDouble
