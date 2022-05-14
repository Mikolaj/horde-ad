{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module HordeAd.Core.Again.Classifier (module HordeAd.Core.Again.Classifier) where

import qualified Data.Array.Shaped as OShaped
import qualified Data.Array.ShapedS as OS
import GHC.TypeLits (KnownNat)
import qualified GHC.TypeNats
import HordeAd.Core.Again
  ( DeltaF,
    Dual,
    DualMonad,
    Ops,
    addS,
    constS,
    dSingleArg,
    mulS,
    mulSDual,
    softMaxCrossEntropy,
  )
import Numeric.LinearAlgebra (Numeric)
import Text.Printf (printf)
import Prelude

model ::
  forall s labels samples dim dual m.
  ( Numeric s,
    Ops (DeltaF s) dual,
    KnownNat labels,
    KnownNat samples,
    KnownNat dim,
    Floating s,
    DualMonad dual m
  ) =>
  -- | Data points
  OS.Array [samples, dim] s ->
  -- | Ground truth
  OS.Array [samples, labels] s ->
  -- | Linear layer
  Dual dual (OS.Array [dim, labels] s) ->
  -- | Loss
  m (Dual dual s)
model data_ groundTruth layer = do
  let predictions :: Dual dual (OS.Array [samples, labels] s)
      predictions = constS data_ `mulSDual` layer

  softMaxCrossEntropy predictions (constS groundTruth)

type NumSamples = 5 GHC.TypeNats.* 5 GHC.TypeNats.* 5 GHC.TypeNats.* 5

type Dim = 4

type Labels = 2

inputData :: OS.Array [NumSamples, Dim] Double
inputData = (OS.ravel . OShaped.fromList . map OS.fromList) inputDataList

inputDataList :: [[Double]]
inputDataList = do
  x1 <- [-2 .. 2 :: Int]
  x2 <- [-2 .. 2 :: Int]
  x3 <- [-2 .. 2 :: Int]
  x4 <- [-2 .. 2 :: Int]
  pure (map fromIntegral [x1, x2, x3, x4])

labels :: OS.Array [NumSamples, Labels] Double
labels = OS.ravel $ OShaped.fromList $ map OS.fromList labelsList

labelsList :: [[Double]]
labelsList = do
  xs <- inputDataList
  pure $
    if sum (zipWith (*) [-1, 2, 5, -7] xs) > 0
      then [1, 0]
      else [0, 1]

initialWeights :: OS.Array [Dim, Labels] Double
initialWeights = OS.fromList $ do
  x <- [0 .. 7 :: Int]
  pure (fromIntegral x / 10)

loop :: OS.Array '[Dim, Labels] Double -> Int -> IO ()
loop weights 1 = do
  let logPrediction = inputData `mulS` weights
      prediction = OS.mapA exp logPrediction
      normalization = prediction `mulS` OS.constant 1
      normalizedPrediction = OS.zipWithA (/) prediction normalization

      asList = map OS.toList (OShaped.toList (OS.unravel normalizedPrediction))

      zipped = zip asList labelsList

  _ <- flip traverse zipped $ \(predicted, actual) -> do
    _ <- flip traverse predicted $ \a -> do
      putStr (printf "%.2f " a)
    _ <- flip traverse actual $ \a -> do
      putStr (printf "%.2f " a)
    putStrLn ""

  pure ()
loop weights n = do
  let learningRate = 0.1
  putStr "Starting iteration "
  print n
  let (loss, update) = dSingleArg weights learningRate (model inputData labels)

  print loss
  loop (weights `addS` update) (n + 1)
