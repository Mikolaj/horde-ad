{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module HordeAd.Core.Again.Classifier (module HordeAd.Core.Again.Classifier) where

import qualified Data.Array.Shaped as OShaped
import qualified Data.Array.ShapedS as OS
import Data.Biapplicative ((<<*>>))
import qualified Data.Biapplicative as B
import GHC.TypeLits (KnownNat)
import qualified GHC.TypeNats
import HordeAd.Core.Again
  ( DeltaF,
    Dual,
    DualMonad,
    Ops,
    adaptArg,
    addS,
    constS,
    dSingleArg,
    dSingleArgForward,
    mulS,
    mulSDual,
    reluSDual,
    runDualMonadAdapt,
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

--

mlpInputDataList :: [([Double], [Double])]
mlpInputDataList =
  let first = do
        let count = 100
            totalAngle = 3 * pi / 4
            tick = totalAngle / (count - 1)

        p <- [0 .. count - 1]

        pure (1 + 2 * cos (tick * p), 2 * sin (tick * p))
   in map (\(x, y) -> ([x, y], [1, 0])) first
        ++ map (\(x, y) -> ([- x, - y], [0, 1])) first

mlpInputData :: OS.Array [200, 2] Double
mlpInputData =
  ( OS.ravel . OShaped.fromList
      . map (OS.fromList . fst)
  )
    mlpInputDataList

mlpLabels :: OS.Array [200, 2] Double
mlpLabels =
  ( OS.ravel . OShaped.fromList . map (OS.fromList . snd)
  )
    mlpInputDataList

mlpPredict ::
  forall s labels hidden1 hidden2 dim.
  ( Numeric s,
    Ord s,
    KnownNat labels,
    KnownNat hidden1,
    KnownNat hidden2,
    KnownNat dim,
    Floating s
  ) =>
  OS.Array '[1, dim] s ->
  ( OS.Array '[dim, hidden1] s,
    OS.Array '[hidden1, hidden2] s,
    OS.Array '[hidden2, labels] s
  ) ->
  s
mlpPredict data_ (layer1, layer2, layer3) =
  let logPrediction :: OS.Array [1, labels] s
      (logPrediction, _) =
        dSingleArgForward
          data_
          (OS.constant 0)
          ( pure
              . (`mulSDual` constS layer3)
              . reluSDual
              . (`mulSDual` constS layer2)
              . reluSDual
              . (`mulSDual` constS layer1)
          )

      prediction = OS.mapA exp logPrediction
      normalization = prediction `mulS` OS.constant 1
      normalizedPrediction = OS.zipWithA (/) prediction normalization
   in head (OS.toList normalizedPrediction)

mlp ::
  ( Ops (DeltaF s) dual,
    Numeric s,
    Ord s,
    KnownNat labels,
    KnownNat samples,
    Floating s,
    DualMonad dual m,
    KnownNat hidden1,
    KnownNat hidden2,
    KnownNat dim
  ) =>
  OS.Array '[samples, dim] s ->
  OS.Array '[samples, labels] s ->
  ( Dual dual (OS.Array '[dim, hidden1] s),
    Dual dual (OS.Array '[hidden1, hidden2] s),
    Dual dual (OS.Array '[hidden2, labels] s)
  ) ->
  m (Dual dual s)
mlp data_ groundTruth (layer1, layer2, layer3) = do
  let predictions =
        (`mulSDual` layer3)
          . reluSDual
          . (`mulSDual` layer2)
          . reluSDual
          . (`mulSDual` layer1)
          $ constS data_

  softMaxCrossEntropy predictions (constS groundTruth)

mlpInitialWeights ::
  ( OS.Array [2, 10] Double,
    OS.Array [10, 10] Double,
    OS.Array [10, 2] Double
  )
mlpInitialWeights =
  ( OS.fromList $ map ((/ 40) . fromIntegral) [-9 .. 10 :: Int],
    OS.fromList $ map ((/ 100) . fromIntegral) [-50 .. 49 :: Int],
    OS.fromList $ map ((/ 40) . fromIntegral) [-9 .. 10 :: Int]
  )

mlpLoop ::
  ( KnownNat hidden1,
    KnownNat hidden2
  ) =>
  ( OS.Array [2, hidden1] Double,
    OS.Array [hidden1, hidden2] Double,
    OS.Array [hidden2, 2] Double
  ) ->
  Int ->
  IO ()
mlpLoop weights 100 = do
  let f = flip mlpPredict weights

      output =
        unlines $
          ["x      y"] ++ do
            x <- [-3, -2.9 .. 3]
            y <- [-3, -2.9 .. 3]
            pure (printf "%.3f %.3f %.3f" x y (f (OS.fromList [x, y])))

  writeFile "/tmp/foo.dat" output

  print weights

  _ <- flip traverse mlpInputDataList $ \(data_, class_) -> do
    _ <- flip traverse data_ $ \a -> do
      putStr (printf "%.2f " a)
    _ <- flip traverse class_ $ \a -> do
      putStr (printf "%.2f " a)
    print (f (OS.fromList data_))

  _ <- flip traverse [2.5, 2.4 .. -2.5] $ \j -> do
    _ <- flip traverse [-3, -2.9 .. 3] $ \i -> do
      putStr $
        if
            | flip any mlpInputDataList $ \([x, y], _) ->
                (x >= i) && (x < i + 0.1) && (y >= j) && (y < j + 0.1) ->
              "+"
            | f (OS.fromList [i, j]) > 0.75 -> "X"
            | otherwise -> "_"
    putStrLn ""

  pure ()
mlpLoop (l1, l2, l3) n = do
  let learningRate = 0.01
  putStr "Starting iteration "
  print n
  let (loss, (ul1, ul2, ul3)) =
        runDualMonadAdapt
          ( B.bipure (,,) (,,)
              <<*>> adaptArg l1
              <<*>> adaptArg l2
              <<*>> adaptArg l3
          )
          learningRate
          (mlp mlpInputData mlpLabels)

  print loss

  mlpLoop
    ( l1 `addS` ul1,
      l2 `addS` ul2,
      l3 `addS` ul3
    )
    (n + 1)
