{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Gen where

import Data.ByteString qualified as BS
import Data.Type.Equality
import Data.Type.Ord
import Data.Vector.Storable qualified as VS
import Foreign
import GHC.TypeLits
import GHC.TypeNats qualified as TN

import Data.Array.Nested
import Data.Array.Nested.Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Types

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import System.Random qualified as Random

import Util


-- | Generates zero with small probability, because there's typically only one
-- interesting case for 0 anyway.
genRank :: Monad m => (forall n. SNat n -> PropertyT m ()) -> PropertyT m ()
genRank k = do
  rank <- forAll $ Gen.frequency [(1, return 0)
                                 ,(49, Gen.int (Range.linear 1 8))]
  TN.withSomeSNat (fromIntegral rank) k

genLowBiased :: RealFloat a => (a, a) -> Gen a
genLowBiased (lo, hi) = do
  x <- Gen.realFloat (Range.linearFrac 0 1)
  return (lo + x * x * x * (hi - lo))

shuffleShR :: IShR n -> Gen (IShR n)
shuffleShR = \sh -> go (shrLength sh) (shrToList sh) sh
  where
    go :: Int -> [Int] -> IShR n -> Gen (IShR n)
    go _    _   ZSR = return ZSR
    go nbag bag (_ :$: sh) = do
      idx <- Gen.int (Range.linear 0 (nbag - 1))
      let (dim, bag') = case splitAt idx bag of
                          (pre, n : post) -> (n, pre ++ post)
                          _ -> error "unreachable"
      (dim :$:) <$> go (nbag - 1) bag' sh

genShR :: SNat n -> Gen (IShR n)
genShR = genShRwithTarget 100_000

genShRwithTarget :: Int -> SNat n -> Gen (IShR n)
genShRwithTarget targetMax sn = do
  let n = fromSNat' sn
  targetSize <- Gen.int (Range.linear 0 targetMax)
  let genDims :: SNat m -> Int -> Gen (IShR m)
      genDims SZ _ = return ZSR
      genDims (SS m) 0 = do
        dim <- Gen.int (Range.linear 0 20)
        dims <- genDims m 0
        return (dim :$: dims)
      genDims (SS m) tgt = do
        dim <- Gen.frequency [(20 * n, round <$> genLowBiased @Double (2.0, max 2.0 (sqrt (fromIntegral tgt))))
                             ,(2     , return tgt)
                             ,(4     , return 1)
                             ,(1     , return 0)]
        dims <- genDims m (if dim == 0 then 0 else tgt `div` dim)
        return (dim :$: dims)
  dims <- genDims sn targetSize
  let maxdim = maximum $ shrToList dims
      cap = binarySearch (`div` 2) 1 maxdim (\cap' -> shrSize (min cap' <$> dims) <= targetSize)
  shuffleShR (min cap <$> dims)

-- | Example: given 3 and 7, might return:
--
-- @
-- ([   13,       4, 27   ]
-- ,[1, 13, 1, 1, 4, 27, 1]
-- ,[4, 13, 1, 3, 4, 27, 2])
-- @
--
-- The up-replicated dimensions are always nonzero and not very large, but the
-- other dimensions might be zero.
genReplicatedShR :: m <= n => SNat m -> SNat n -> Gen (IShR m, IShR n, IShR n)
genReplicatedShR = \m n -> do
  let expectedSizeIncrease = round (repvalavg ^ (fromSNat' n - fromSNat' m))
  sh1 <- genShRwithTarget (1_000_000 `div` expectedSizeIncrease) m
  (sh2, sh3) <- injectOnes n sh1 sh1
  return (sh1, sh2, sh3)
  where
    repvalrange = (1::Int, 5)
    repvalavg = let (lo, hi) = repvalrange in fromIntegral (lo + hi) / 2 :: Double

    injectOnes :: m <= n => SNat n -> IShR m -> IShR m -> Gen (IShR n, IShR n)
    injectOnes n@SNat shOnes sh
      | m@SNat <- shrRank sh
      = case cmpNat n m of
          LTI -> error "unreachable"
          EQI -> return (shOnes, sh)
          GTI -> do
            index <- Gen.int (Range.linear 0 (fromSNat' m))
            value <- Gen.int (uncurry Range.linear repvalrange)
            Refl <- return (lem n m)
            injectOnes n (inject index 1 shOnes) (inject index value sh)

    lem :: forall n m proxy. n > m => proxy n -> proxy m -> (m + 1 <=? n) :~: True
    lem _ _ = unsafeCoerceRefl

    inject :: Int -> Int -> IShR m -> IShR (m + 1)
    inject 0 v sh = v :$: sh
    inject i v (w :$: sh) = w :$: inject (i - 1) v sh
    inject _ _ ZSR = error "unreachable"

genStorables :: forall a. Storable a => Range Int -> (Word64 -> a) -> GenT IO (VS.Vector a)
genStorables rng f = do
  n <- Gen.int rng
  seed <- Gen.resize 99 $ Gen.int Range.linearBounded
  let gen0 = Random.mkStdGen seed
      (bs, _) = Random.uniformByteString (8 * n) gen0
  let readW64 i = sum (zipWith (*) (iterate (*256) 1) [fromIntegral (bs `BS.index` (8 * i + j)) | j <- [0..7]])
  return $ VS.generate n (f . readW64)

genStaticShX :: Monad m => SNat n -> (forall sh. Rank sh ~ n => StaticShX sh -> PropertyT m ()) -> PropertyT m ()
genStaticShX = \n k -> case n of
  SZ -> k ZKX
  SS n' ->
    genItem $ \item ->
    genStaticShX n' $ \ssh ->
      k (item :!% ssh)
  where
    genItem :: Monad m => (forall n. SMayNat () n -> PropertyT m ()) -> PropertyT m ()
    genItem k = do
      b <- forAll Gen.bool
      if b
        then do
          n <- forAll $ Gen.frequency [(20, Gen.int (Range.linear 1 4))
                                      ,(1, return 0)]
          TN.withSomeSNat (fromIntegral n) $ \sn -> k (SKnown sn)
        else k (SUnknown ())

genShX :: StaticShX sh -> Gen (IShX sh)
genShX ZKX = return ZSX
genShX (SKnown sn :!% ssh) = (SKnown sn :$%) <$> genShX ssh
genShX (SUnknown () :!% ssh) = do
  dim <- Gen.int (Range.linear 1 4)
  (SUnknown dim :$%) <$> genShX ssh

genPermR :: Int -> Gen PermR
genPermR n = Gen.shuffle [0 .. n-1]

genPerm :: Monad m => SNat n -> (forall p. (IsPermutation p, Rank p ~ n) => Perm p -> PropertyT m r) -> PropertyT m r
genPerm n@SNat k = do
  list <- forAll $ genPermR (fromSNat' n)
  permFromListCont list $ \perm -> do
    case permCheckPermutation perm $
           case sameNat' (permRank perm) n of
             Just Refl -> Just (k perm)
             Nothing -> Nothing
         of
      Just (Just act) -> act
      _ -> error ""
