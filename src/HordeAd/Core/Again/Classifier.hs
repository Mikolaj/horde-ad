{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module HordeAd.Core.Again.Classifier (module HordeAd.Core.Again.Classifier) where

import qualified Data.Array.Shaped as OShaped
import qualified Data.Array.ShapedS as OS
import Data.Biapplicative ((<<*>>))
import qualified Data.Biapplicative as B
import Data.Proxy (Proxy (Proxy))
import Data.Random.Normal (normalIO, mkNormals)
import Foreign (Storable)
import GHC.TypeLits (KnownNat)
import GHC.TypeNats (natVal)
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
    dValue,
    mulS,
    mulSDual,
    reluSDual,
    runDualMonadAdapt,
    softMaxCrossEntropy,
  )
import Numeric.LinearAlgebra (Numeric)
import System.IO.Temp (createTempDirectory)
import System.Random (Random)
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

  softMaxCrossEntropy predictions groundTruth

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
  let count = valueOf @HalfSamples
      first = do
        let totalAngle = 5 * pi / 4
            tick = totalAngle / fromIntegral (count - 1)

        p' <- [0 .. count - 1]
        let p = fromIntegral p'

        pure (1 + 2 * cos (tick * p), 2 * sin (tick * p))

      (normals1, rest1) = splitAt count (mkNormals 1)
      (normals2, rest2) = splitAt count rest1
      (normals3, rest3) = splitAt count rest2
      (normals4, _) = splitAt count rest3

   in map (\((x, y), dx, dy) -> ([1, x + dx / 3, y + dy / 3], [1, 0])) (zip3 first normals1 normals2)
        ++ map (\((x, y), dx, dy) -> ([1, - x + dx / 3, - y + dy / 3], [0, 1])) (zip3 first normals3 normals4)

type HalfSamples = 10

type Samples = HalfSamples GHC.TypeNats.* 2

mlpInputData :: OS.Array [Samples, Features] Double
mlpInputData =
  ( OS.ravel . OShaped.fromList . map (OS.fromList . fst)
  )
    mlpInputDataList

mlpLabels :: OS.Array [Samples, Classes] Double
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
      logPrediction =
        dValue
          ( pure $
              mlp (constS layer1, constS layer2, constS layer3) (constS data_)
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
    KnownNat hidden1,
    KnownNat hidden2,
    KnownNat dim
  ) =>
  ( Dual dual (OS.Array '[dim, hidden1] s),
    Dual dual (OS.Array '[hidden1, hidden2] s),
    Dual dual (OS.Array '[hidden2, labels] s)
  ) ->
  Dual dual (OS.Array '[samples, dim] s) ->
  Dual dual (OS.Array '[samples, labels] s)
mlp (layer1, layer2, layer3) =
  (`mulSDual` layer3)
    . reluSDual
    . (`mulSDual` layer2)
    . reluSDual
    . (`mulSDual` layer1)

mlpTrain ::
  ( Ops (DeltaF s) dual,
    Numeric s,
    Ord s,
    KnownNat labels,
    KnownNat samples,
    KnownNat hidden1,
    KnownNat hidden2,
    KnownNat dim,
    Floating s,
    DualMonad dual m
  ) =>
  OS.Array '[samples, dim] s ->
  OS.Array '[samples, labels] s ->
  ( Dual dual (OS.Array '[dim, hidden1] s),
    Dual dual (OS.Array '[hidden1, hidden2] s),
    Dual dual (OS.Array '[hidden2, labels] s)
  ) ->
  m (Dual dual s)
mlpTrain data_ groundTruth layers = do
  let predictions = mlp layers (constS data_)
  softMaxCrossEntropy predictions groundTruth

type Features = 3

type Classes = 2

valueOf :: forall n. KnownNat n => Int
valueOf = fromIntegral (natVal (Proxy :: Proxy n))

mlpInitialWeights ::
  ( KnownNat features,
    KnownNat classes,
    KnownNat hidden2,
    KnownNat hidden1
  ) =>
  IO
    ( OS.Array [features, hidden1] Double,
      OS.Array [hidden1, hidden2] Double,
      OS.Array [hidden2, classes] Double
    )
mlpInitialWeights = (,,) <$> normalArray <*> normalArray <*> normalArray

normalArray ::
  forall sh a.
  (OS.Shape sh, Random a, Storable a, Floating a) =>
  IO (OS.Array sh a)
normalArray = OS.fromList <$> normals (OS.sizeP (Proxy @sh))

normals :: (Random a, Floating a) => Int -> IO [a]
normals 0 = pure []
normals n = do
  r <- (/ 10) <$> normalIO
  rest <- normals (n - 1)
  pure (r : rest)

type Params features hidden1 hidden2 classes a =
  ( OS.Array [features, hidden1] a,
    OS.Array [hidden1, hidden2] a,
    OS.Array [hidden2, classes] a
  )

addParams ::
  ( KnownNat hidden1,
    KnownNat features,
    Numeric a,
    KnownNat hidden2,
    KnownNat classes
  ) =>
  Params features hidden1 hidden2 classes a ->
  Params features hidden1 hidden2 classes a ->
  Params features hidden1 hidden2 classes a
addParams (p1, p2, p3) (q1, q2, q3) = (p1 `addS` q1, p2 `addS` q2, p3 `addS` q3)

mlpLoop ::
  forall hidden1 hidden2.
  ( KnownNat hidden1,
    KnownNat hidden2
  ) =>
  String ->
  Params Features hidden1 hidden2 Classes Double ->
  Int ->
  IO ()
mlpLoop dir weights n@300 = do
  let f = flip mlpPredict weights

  _ <- flip traverse [2.5, 2.4 .. -2.5] $ \j -> do
    _ <- flip traverse [-3, -2.9 .. 3] $ \i -> do
      putStr $
        if
            | flip any mlpInputDataList $ \([1, x, y], _) ->
                (x >= i) && (x < i + 0.1) && (y >= j) && (y < j + 0.1) ->
              "+"
            | f (OS.fromList [1, i, j]) > 0.5 -> "X"
            | otherwise -> "_"
    putStrLn ""

  let output' = gnuplotImage f n

  appendFile (dir ++ "/all.dat") output'

  let output1 = unlines $ do
        ([1, x, y], [1, 0]) <- mlpInputDataList
        pure (printf "%.2f %.2f" x y)

  let output2 = unlines $ do
        ([1, x, y], [0, 1]) <- mlpInputDataList
        pure (printf "%.2f %.2f" x y)

  writeFile (dir ++ "/points1.dat") output1
  writeFile (dir ++ "/points2.dat") output2

  pure ()
mlpLoop dir weights@(l1, l2, l3) n = do
  let learningRate = 0.05
  putStr "Starting iteration "
  print n
  let (loss, adjustment) =
        runDualMonadAdapt
          ( B.bipure (,,) (,,)
              <<*>> adaptArg l1
              <<*>> adaptArg l2
              <<*>> adaptArg l3
          )
          learningRate
          (mlpTrain mlpInputData mlpLabels)

  print loss

  let nextWeights = weights `addParams` adjustment

  let f = flip mlpPredict weights
      output = gnuplotImage f n

  appendFile (dir ++ "/all.dat") (output ++ "\n\n")

  mlpLoop dir nextWeights (n + 1)

runLoop :: forall hidden1 hidden2. (KnownNat hidden1, KnownNat hidden2) => IO ()
runLoop = do
  dir <- createTempDirectory "." "mlp"
  flip (mlpLoop @hidden1 @hidden2 dir) 0 =<< mlpInitialWeights

  writeFile (dir ++ "/mlp.gnuplot") (unlines $
                                     [ "set cbrange [0:1]"
                                     , "stats '" ++ dir ++ "/all.dat' nooutput"
                                     , "set term gif animate delay 10 loop -1"
                                     , "set output '" ++ dir ++ "/mlp.gif'"
                                     , "do for [i=1:int(STATS_blocks)] { plot '" ++ dir ++ "/all.dat' index (i-1) with image notitle, '" ++ dir ++ "/points1.dat' with points pt 7 ps 2 notitle, '" ++ dir ++ "/points2.dat' with points pt 7 ps 2 notitle }"
                                     ])
  putStrLn ("gnuplot " ++ dir ++ "/mlp.gnuplot")
  putStrLn ("firefox -P default --new-window " ++ dir ++ "/mlp.gif")

gnuplotImage ::
  (OS.Shape sh, OS.Size sh ~ 3) =>
  (OS.Array sh Double -> Double) ->
  Int ->
  String
gnuplotImage f n = unlines $
  do
    x <- [-3, -2.9 .. 3]

    ( do
        y <- [-3, -2.9 .. 3]
        pure (printf "%.3f %.3f %.3f %.3d" x y (f (OS.fromList [1, x, y])) n)
      )
