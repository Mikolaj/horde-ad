{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-missing-export-lists -Wno-orphans #-}
-- | Two implementations of the monad in which our dual numbers live,
-- an implementation of deriving a gradient and several gradient descent
-- schemes.
module HordeAd.Core.Engine where

import Prelude

import           Control.Monad (foldM)
import           Control.Monad.ST.Strict (runST)
import           Control.Monad.Trans.State.Strict
import           Data.Functor.Identity
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import           Numeric.LinearAlgebra
  (Element, Matrix, Numeric, Vector, konst, rows, size, tr')
import qualified Numeric.LinearAlgebra
import           Numeric.LinearAlgebra.Data (flatten)
import           Numeric.LinearAlgebra.Devel
  (MatrixOrder (..), liftMatrix, liftMatrix2, matrixFromVector, orderOf)

import HordeAd.Core.Delta
import HordeAd.Core.DualNumber (DeltaMonad (..), DualNumber (..))
import HordeAd.Core.PairOfVectors (DualNumberVariables, makeDualNumberVariables)

-- import Debug.Trace

type Domain r = Vector r

type Domain' r = Domain r

type DomainV r = Data.Vector.Vector (Vector r)

type DomainV' r = DomainV r

type DomainL r = Data.Vector.Vector (Matrix r)

type DomainL' r = DomainL r

type Domains r = (Domain r, DomainV r, DomainL r)

type Domains' r = (Domain' r, DomainV' r, DomainL' r)

-- * First comes the dummy monad implementation that does not collect deltas.
-- It's intended for efficiently calculating the value of the function only.

type DeltaMonadValue r = Identity

instance DeltaMonad r (DeltaMonadValue r) where
  returnLet (D u _u') = Identity $ D u Zero
  returnLetV (D u _u') = Identity $ D u Zero
  returnLetL (D u _u') = Identity $ D u Zero

-- The general case, needed for old, hacky tests before 'Delta' extension.
--
-- Small enough that inline won't hurt.
primalValueGeneric :: Numeric r
                   => (DualNumberVariables r -> DeltaMonadValue r a)
                   -> Domains r
                   -> a
{-# INLINE primalValueGeneric #-}
primalValueGeneric f (params, paramsV, paramsL) =
  let variables = makeDualNumberVariables
                    (params, paramsV, paramsL)
                    ( V.replicate (V.length params) Zero  -- dummy
                    , V.replicate (V.length paramsV) Zero
                    , V.replicate (V.length paramsL) Zero )
  in runIdentity $ f variables

-- Small enough that inline won't hurt.
primalValue :: Numeric r
            => (DualNumberVariables r -> DeltaMonadValue r (DualNumber a))
            -> Domains r
            -> a
{-# INLINE primalValue #-}
primalValue f parameters =
  let D value _ = primalValueGeneric f parameters
  in value

-- * Here's the fully-fledged monad implementation for gradients
-- and the code that uses it to compute single gradients and to do
-- gradient descent.

newtype DeltaMonadGradient r a = DeltaMonadGradient
  { runDeltaMonadGradient :: State (DeltaState r) a }
  deriving (Monad, Functor, Applicative)

instance DeltaMonad r (DeltaMonadGradient r) where
  returnLet (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = DScalar u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)
  returnLetV (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = DVector u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)
  returnLetL (D u u') = DeltaMonadGradient $ do
    DeltaId i <- gets deltaCounter
    modify $ \s ->
      s { deltaCounter = DeltaId $ succ i
        , deltaBindings = DMatrix u' : deltaBindings s
        }
    return $! D u (Var $ DeltaId i)

-- The functions in which it inlines and which are used in client code
-- are not inlined there, so the bloat is limited.
generalDf :: (Eq r, Numeric r, Num (Vector r))
          => DualNumberVariables r
          -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
          -> (Domains' r, r)
{-# INLINE generalDf #-}
generalDf variables@(params, _, paramsV, _, paramsL, _) f =
  let dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      initialState = DeltaState
        { deltaCounter = DeltaId $ dim + dimV + dimL
        , deltaBindings = []
        }
      (D value d, st) = runState (runDeltaMonadGradient (f variables))
                                 initialState
      gradient = evalBindings dim dimV dimL st d
  in (gradient, value)

df :: forall r. (Eq r, Numeric r, Num (Vector r))
   => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
   -> Domains r
   -> (Domains' r, r)
df f parameters =
  let varDeltas = generateDeltaVars parameters
      variables = makeDualNumberVariables parameters varDeltas
  in generalDf variables f

generateDeltaVars :: Numeric r
                  => Domains r -> ( Data.Vector.Vector (Delta r)
                                  , Data.Vector.Vector (Delta (Vector r))
                                  , Data.Vector.Vector (Delta (Matrix r)) )
generateDeltaVars (params, paramsV, paramsL) =
  let dim = V.length params
      dimV = V.length paramsV
      dimL = V.length paramsL
      vVar = V.generate dim (Var . DeltaId)
      vVarV = V.generate dimV (Var . DeltaId . (+ dim))
      vVarL = V.generate dimL (Var . DeltaId . (+ (dim + dimV)))
  in (vVar, vVarV, vVarL)

{-
60% of heap allocation in matrix- and vector-based MNIST is performed
by @updateWithGradient.updateVector@ below

  let updateVector i r = i - Numeric.LinearAlgebra.scale gamma r

due to allocating once in @scale@ and again in @-@
(and there seems to be one more allocation judging by the numbers).
Something like the following code would be needed to eliminate
one allocation, but it would requre the hmatrix maintainer to expose
internal modules.

import           Internal.Vectorized
  ( FunCodeSV (Scale), FunCodeVV (Sub), applyRaw, c_vectorMapValR
  , c_vectorZipR, createVector )

minusTimesGamma :: Storable r => r -> Vector r -> Vector r -> Vector r
minusTimesGamma gamma u v = unsafePerformIO $ do
  r <- createVector (dim u)
  pval <- newArray [gamma]
  (v `applyRaw` (r `applyRaw` id))
    (c_vectorMapValR (fromei Scale) pval)
    #| "minusTimesGamma1"
  free pval
  (u `applyRaw` (v `applyRaw` (r `applyRaw` id)))
    (c_vectorZipR (fromei Sub))
    #| "minusTimesGamma2"
  return r

BTW, a version with Numeric.LinearAlgebra.Devel.zipVectorWith makes
the test twice slower and allocate twice more

  let updateVector = zipVectorWith (\i r -> i - gamma * r)

and a version with Vector.Storable makes the test thrice slower
and allocate thrice more

  let updateVector = V.zipWith (\i r -> i - gamma * r)

which is probably a bug in stream fusion which, additionally in this case,
can't fuse with anything and so can't pay for its overhead.

-}

updateWithGradient :: (Numeric r, Num (Vector r))
                   => r
                   -> Domains r
                   -> Domains' r
                   -> Domains r
updateWithGradient gamma (params, paramsV, paramsL)
                         (gradient, gradientV, gradientL) =
  let updateVector i r = i - Numeric.LinearAlgebra.scale gamma r
      paramsNew = updateVector params gradient
      updateV i r = if V.null r  -- eval didn't update it, would crash
                    then i
                    else updateVector i r
      paramsVNew = V.zipWith updateV paramsV gradientV
      updateL i r = if rows r <= 0  -- eval didn't update it, would crash
                    then i
                    else liftMatrix2 updateVector i r
      paramsLNew = V.zipWith updateL paramsL gradientL
  in (paramsNew, paramsVNew, paramsLNew)

gradientIsNil :: (Eq r, Numeric r) => Domains' r -> Bool
gradientIsNil (gradient, gradientV, gradientL) =
  V.all (== 0) gradient
  && V.all V.null gradientV
  && V.all (\r -> rows r <= 0) gradientL

-- | Simple Gradient Descent.
gdSimple :: forall r. (Eq r, Numeric r, Num (Vector r))
         => r
         -> (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
         -> Int  -- ^ requested number of iterations
         -> Domains r  -- ^ initial parameters
         -> Domains r
gdSimple gamma f n0 parameters0 = go n0 parameters0 where
  -- Pre-allocating the vars once, vs gradually allocating on the spot in each
  -- gradient computation, initially incurs overhead (looking up in a vector),
  -- but pays off greatly as soon as the working set doesn't fit in any cache
  -- and so allocations are made in RAM.
  varDeltas = generateDeltaVars parameters0
  go :: Int -> Domains r -> Domains' r
  go 0 parameters = parameters
  go n parameters =
    let variables = makeDualNumberVariables parameters varDeltas
        gradients = fst $ generalDf variables f
        parametersNew = updateWithGradient gamma parameters gradients
    in go (pred n) parametersNew

-- | Stochastic Gradient Descent.
sgd :: forall r a. (Eq r, Numeric r, Num (Vector r))
    => r
    -> (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
    -> [a]  -- ^ training data
    -> Domains r  -- ^ initial parameters
    -> Domains r
sgd gamma f trainingData parameters0 = go trainingData parameters0 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r -> Domains' r
  go [] parameters = parameters
  go (a : rest) parameters =
    let variables = makeDualNumberVariables parameters varDeltas
        gradients = fst $ generalDf variables (f a)
        parametersNew = updateWithGradient gamma parameters gradients
    in go rest parametersNew

_minimumGradient :: (Ord r, Numeric r) => Domains' r -> r
_minimumGradient (gradient, gradientV, gradientL) =
  min (if V.null gradient then 0 else V.minimum gradient)
      (min (if V.null gradientV then 0
            else V.minimum (V.map Numeric.LinearAlgebra.minElement gradientV))
           (if V.null gradientL then 0
            else V.minimum (V.map Numeric.LinearAlgebra.minElement gradientL)))

_maximumGradient :: (Ord r, Numeric r) => Domains' r -> r
_maximumGradient (gradient, gradientV, gradientL) =
  max (if V.null gradient then 0 else V.maximum gradient)
      (max (if V.null gradientV then 0
            else V.maximum (V.map Numeric.LinearAlgebra.maxElement gradientV))
           (if V.null gradientL then 0
            else V.maximum (V.map Numeric.LinearAlgebra.maxElement gradientL)))

-- | Stochastic Gradient Descent with mini-batches, taking the mean
-- of the results from each mini-batch.
--
-- TODO: vectorize and only then take the mean of the vector of results
-- and also parallelize taking advantage of vectorization (but currently
-- we have a global state, so that's tricky).
sgdBatch :: forall r a. (
--                          Show r,
                          Ord r, Numeric r, Fractional r, Num (Vector r)
                        )
         => Int  -- ^ batch size
         -> r  -- ^ gamma (learning_rate?)
         -> (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
         -> [a]  -- ^ training data
         -> Domains r  -- ^ initial parameters
         -> Domains r
sgdBatch batchSize gamma f trainingData parameters0 =
  go trainingData parameters0
 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r -> Domains' r
  go [] parameters = parameters
  go l parameters =
    let variables = makeDualNumberVariables parameters varDeltas
        (batch, rest) = splitAt batchSize l
        fAdd :: DualNumberVariables r -> DualNumber r -> a
             -> DeltaMonadGradient r (DualNumber r)
        fAdd vars !acc a = do
          res <- f a vars
          return $! acc + res
        fBatch :: DualNumberVariables r
               -> DeltaMonadGradient r (DualNumber r)
        fBatch vars = do
          resBatch <- foldM (fAdd vars) 0 batch
          return $! resBatch / (fromIntegral $ length batch)
        gradients = fst $ generalDf variables fBatch
--        !_ = traceShow (fromIntegral (length l) / fromIntegral batchSize
--                          :: Double) $
--             traceShow (_minimumGradient gradients) $
--             traceShow (_maximumGradient gradients) $ ()
        parametersNew = updateWithGradient gamma parameters gradients
    in go rest parametersNew

data ArgsAdam r = ArgsAdam
  { alpha   :: r
  , beta1   :: r
  , beta2   :: r
  , epsilon :: r
  }

-- The defaults taken from
-- https://www.tensorflow.org/api_docs/python/tf/keras/optimizers/Adam
defaultArgsAdam :: Fractional r => ArgsAdam r
defaultArgsAdam = ArgsAdam
  { alpha = 0.001
  , beta1 = 0.9
  , beta2 = 0.999
  , epsilon = 1e-7
  }

data StateAdam r = StateAdam
  { tAdam :: Int  -- iteration count
  , mAdam :: Domains' r
  , vAdam :: Domains' r
  }

zeroParameters :: Numeric r => Domains r -> Domains r
zeroParameters (params, paramsV, paramsL) =  -- sample params, for dimensions
  let zeroVector v = runST $ do
        vThawed <- V.thaw v
        VM.set vThawed 0
        V.unsafeFreeze vThawed
  in ( zeroVector params
     , V.map zeroVector paramsV
     , V.map (liftMatrix zeroVector) paramsL )

initialStateAdam :: Numeric r => Domains r -> StateAdam r
initialStateAdam parameters0 =
  let zeroP = zeroParameters parameters0
  in StateAdam
       { tAdam = 0
       , mAdam = zeroP
       , vAdam = zeroP
       }

-- | Application of a vector function on the flattened matrices elements.
liftMatrix43 :: ( Numeric a, Numeric b, Numeric c, Numeric d
                , Element x, Element y, Element z )
             => (Vector a -> Vector b -> Vector c -> Vector d
                 -> (Vector x, Vector y, Vector z))
             -> Matrix a -> Matrix b -> Matrix c -> Matrix d
             -> (Matrix x, Matrix y, Matrix z)
liftMatrix43 f m1 m2 m3 m4 =
  let sz@(r, c) = size m1
      rowOrder = orderOf m1
  in if sz == size m2 && sz == size m3 && sz == size m4
     then
       let (vx, vy, vz) = case rowOrder of
             RowMajor -> f (flatten m1) (flatten m2) (flatten m3) (flatten m4)
             ColumnMajor -> f (flatten (tr' m1)) (flatten (tr' m2))
                              (flatten (tr' m3)) (flatten (tr' m4))
               -- TODO: check if keeping RowMajor is faster
       in ( matrixFromVector rowOrder r c vx
          , matrixFromVector rowOrder r c vy
          , matrixFromVector rowOrder r c vz
          )
     else error $ "nonconformant matrices in liftMatrix43: "
                  ++ show (size m1, size m2, size m3, size m4)

updateWithGradientAdam :: forall r. (Floating r, Numeric r, Floating (Vector r))
                       => ArgsAdam r
                       -> StateAdam r
                       -> Domains r
                       -> Domains' r
                       -> (Domains r, StateAdam r)
updateWithGradientAdam ArgsAdam{..}
                       StateAdam{ tAdam
                                , mAdam = (mAdam, mAdamV, mAdamL)
                                , vAdam = (vAdam, vAdamV, vAdamL)
                                }
                       (params, paramsV, paramsL)
                       (gradient, gradientV, gradientL) =
  let tAdamNew = tAdam + 1
      oneMinusBeta1 = 1 - beta1
      oneMinusBeta2 = 1 - beta2
      updateVector :: Vector r -> Vector r -> Vector r -> Vector r
                   -> (Vector r, Vector r, Vector r)
      updateVector mA vA p g =
        let mANew = Numeric.LinearAlgebra.scale beta1 mA
                    + Numeric.LinearAlgebra.scale oneMinusBeta1 g
            vANew = Numeric.LinearAlgebra.scale beta2 vA
                    + Numeric.LinearAlgebra.scale oneMinusBeta2 (g * g)
            alphat = alpha * sqrt (1 - beta2 ^ tAdamNew)
                             / (1 - beta1 ^ tAdamNew)
        in ( mANew
           , vANew
           , p - Numeric.LinearAlgebra.scale alphat mANew
                 / (sqrt vANew + konst epsilon (V.length vANew)) )
                      -- @addConstant@ would be better, but it's not exposed
      (mAdamNew, vAdamNew, paramsNew) = updateVector mAdam vAdam params gradient
      updateV mA vA p g = if V.null g  -- eval didn't update it, would crash
                          then (mA, vA, p)
                          else updateVector mA vA p g
      (mAdamVNew, vAdamVNew, paramsVNew) =
        V.unzip3 $ V.zipWith4 updateV mAdamV vAdamV paramsV gradientV
      updateL mA vA p g = if rows g <= 0  -- eval didn't update it, would crash
                          then (mA, vA, p)
                          else liftMatrix43 updateVector mA vA p g
      (mAdamLNew, vAdamLNew, paramsLNew) =
        V.unzip3 $ V.zipWith4 updateL mAdamL vAdamL paramsL gradientL
  in ( (paramsNew, paramsVNew, paramsLNew)
     , StateAdam { tAdam = tAdamNew
                 , mAdam = (mAdamNew, mAdamVNew, mAdamLNew)
                 , vAdam = (vAdamNew, vAdamVNew, vAdamLNew)
                 }
     )

sgdAdam :: forall r a. (Eq r, Floating r, Numeric r, Floating (Vector r))
        => (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
        -> [a]
        -> Domains r
        -> StateAdam r
        -> (Domains r, StateAdam r)
sgdAdam = sgdAdamArgs defaultArgsAdam

sgdAdamArgs :: forall r a. (Eq r, Floating r, Numeric r, Floating (Vector r))
            => ArgsAdam r
            -> (a -> DualNumberVariables r
                -> DeltaMonadGradient r (DualNumber r))
            -> [a]
            -> Domains r
            -> StateAdam r
            -> (Domains r, StateAdam r)
sgdAdamArgs argsAdam f trainingData parameters0 stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r-> StateAdam r -> (Domains r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go (a : rest) parameters stateAdam =
    let variables = makeDualNumberVariables parameters varDeltas
        gradients = fst $ generalDf variables (f a)
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew

sgdAdamBatch
  :: forall r a. (Eq r, Floating r, Numeric r, Floating (Vector r))
  => Int  -- ^ batch size
  -> (a -> DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
  -> [a]
  -> Domains r
  -> StateAdam r
  -> (Domains r, StateAdam r)
sgdAdamBatch = sgdAdamBatchArgs defaultArgsAdam

sgdAdamBatchArgs
  :: forall r a. (Eq r, Floating r, Numeric r, Floating (Vector r))
  => ArgsAdam r
  -> Int  -- ^ batch size
  -> (a -> DualNumberVariables r
      -> DeltaMonadGradient r (DualNumber r))
  -> [a]
  -> Domains r
  -> StateAdam r
  -> (Domains r, StateAdam r)
sgdAdamBatchArgs argsAdam batchSize f trainingData parameters0 stateAdam0 =
  go trainingData parameters0 stateAdam0
 where
  varDeltas = generateDeltaVars parameters0
  go :: [a] -> Domains r-> StateAdam r -> (Domains r, StateAdam r)
  go [] parameters stateAdam = (parameters, stateAdam)
  go l parameters stateAdam =
    let variables = makeDualNumberVariables parameters varDeltas
        (batch, rest) = splitAt batchSize l
        fAdd :: DualNumberVariables r -> DualNumber r -> a
             -> DeltaMonadGradient r (DualNumber r)
        fAdd vars !acc a = do
          res <- f a vars
          return $! acc + res
        fBatch :: DualNumberVariables r
               -> DeltaMonadGradient r (DualNumber r)
        fBatch vars = do
          resBatch <- foldM (fAdd vars) 0 batch
          return $! resBatch / (fromIntegral $ length batch)
        gradients = fst $ generalDf variables fBatch
        (parametersNew, stateAdamNew) =
          updateWithGradientAdam argsAdam stateAdam parameters gradients
    in go rest parametersNew stateAdamNew

-- | Relatively Smart Gradient Descent.
-- Based on @gradientDescent@ from package @ad@ which is in turn based
-- on the one from the VLAD compiler.
gdSmart :: forall r. (
--                     Show r,
                       Ord r, Fractional r, Numeric r
                     , Num (Vector r)
                     )
        => (DualNumberVariables r -> DeltaMonadGradient r (DualNumber r))
        -> Int  -- ^ requested number of iterations
        -> Domains r  -- ^ initial parameters
        -> (Domains r, r)
gdSmart f n0 parameters0 = go n0 parameters0 0.1 gradients0 value0 0 where
  varDeltas = generateDeltaVars parameters0
  variables0 = makeDualNumberVariables parameters0 varDeltas
  (gradients0, value0) = generalDf variables0 f
  go :: Int -> Domains r -> r -> Domains' r -> r -> Int -> (Domains' r, r)
  go 0 parameters !gamma _gradientsPrev _valuePrev !_i = (parameters, gamma)
  go _ parameters 0 _ _ _ = (parameters, 0)
  go n parameters gamma gradientsPrev valuePrev i =
--    traceShow (n, gamma, valuePrev, i) $
--    traceShow ("parameters" :: String, parameters) $
--    traceShow ("gradients" :: String, gradientsPrev) $
    --
    -- The trick is that we use the previous gradient here,
    -- and the new gradient is only computed by accident together
    -- with the new value that is needed now to revert if we overshoot.
    let parametersNew = updateWithGradient gamma parameters gradientsPrev
        variables = makeDualNumberVariables parametersNew varDeltas
        (gradients, value) = generalDf variables f
    in if | gradientIsNil gradientsPrev -> (parameters, gamma)
          | value > valuePrev ->
--              traceShow ("value > valuePrev" :: String, value, valuePrev) $
              go n parameters (gamma / 2) gradientsPrev valuePrev 0  -- overshot
          | i == 10 -> go (pred n) parametersNew (gamma * 2) gradients value 0
          | otherwise -> go (pred n) parametersNew gamma gradients value (i + 1)
