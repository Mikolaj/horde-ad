-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.Core.OptimizerTools
  ( updateWithGradient
  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), zeroParameters, initialStateAdam
  , liftMatrix43, updateWithGradientAdam
  ) where

import Prelude

import           Control.Monad.ST.Strict (runST)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import           Numeric.LinearAlgebra (Element, Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM
import           Numeric.LinearAlgebra.Data (flatten)
import           Numeric.LinearAlgebra.Devel
  (MatrixOrder (..), liftMatrix, liftMatrix2, matrixFromVector, orderOf)

import HordeAd.Core.Engine

{-
60% of heap allocation in matrix- and vector-based MNIST is performed
by @updateWithGradient.updateVector@ below

  let updateVector i r = i - HM.scale gamma r

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

BTW, a version with HM.Devel.zipVectorWith makes
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
  let updateVector i r = i - HM.scale gamma r
      paramsNew = updateVector params gradient
      updateV i r = if V.null r  -- eval didn't update it, would crash
                    then i
                    else updateVector i r
      paramsVNew = V.zipWith updateV paramsV gradientV
      updateL i r = if HM.rows r <= 0  -- eval didn't update it, would crash
                    then i
                    else liftMatrix2 updateVector i r
      paramsLNew = V.zipWith updateL paramsL gradientL
  in (paramsNew, paramsVNew, paramsLNew)

gradientIsNil :: (Eq r, Numeric r) => Domains' r -> Bool
gradientIsNil (gradient, gradientV, gradientL) =
  V.all (== 0) gradient
  && V.all V.null gradientV
  && V.all (\r -> HM.rows r <= 0) gradientL

minimumGradient :: (Ord r, Numeric r) => Domains' r -> r
minimumGradient (gradient, gradientV, gradientL) =
  min (if V.null gradient then 0 else V.minimum gradient)
      (min (if V.null gradientV then 0
            else V.minimum (V.map HM.minElement gradientV))
           (if V.null gradientL then 0
            else V.minimum (V.map HM.minElement gradientL)))

maximumGradient :: (Ord r, Numeric r) => Domains' r -> r
maximumGradient (gradient, gradientV, gradientL) =
  max (if V.null gradient then 0 else V.maximum gradient)
      (max (if V.null gradientV then 0
            else V.maximum (V.map HM.maxElement gradientV))
           (if V.null gradientL then 0
            else V.maximum (V.map HM.maxElement gradientL)))

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
  let sz@(r, c) = HM.size m1
      rowOrder = orderOf m1
  in if sz == HM.size m2 && sz == HM.size m3 && sz == HM.size m4
     then
       let (vx, vy, vz) = case rowOrder of
             RowMajor -> f (flatten m1) (flatten m2) (flatten m3) (flatten m4)
             ColumnMajor -> f (flatten (HM.tr' m1)) (flatten (HM.tr' m2))
                              (flatten (HM.tr' m3)) (flatten (HM.tr' m4))
               -- TODO: check if keeping RowMajor is faster
       in ( matrixFromVector rowOrder r c vx
          , matrixFromVector rowOrder r c vy
          , matrixFromVector rowOrder r c vz
          )
     else error $ "nonconformant matrices in liftMatrix43: "
                  ++ show (HM.size m1, HM.size m2, HM.size m3, HM.size m4)

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
        let mANew = HM.scale beta1 mA + HM.scale oneMinusBeta1 g
            vANew = HM.scale beta2 vA + HM.scale oneMinusBeta2 (g * g)
            alphat = alpha * sqrt (1 - beta2 ^ tAdamNew)
                             / (1 - beta1 ^ tAdamNew)
        in ( mANew
           , vANew
           , p - HM.scale alphat mANew
                 / (sqrt vANew + HM.konst epsilon (V.length vANew)) )
                      -- @addConstant@ would be better, but it's not exposed
      (mAdamNew, vAdamNew, paramsNew) = updateVector mAdam vAdam params gradient
      updateV mA vA p g = if V.null g  -- eval didn't update it, would crash
                          then (mA, vA, p)
                          else updateVector mA vA p g
      (mAdamVNew, vAdamVNew, paramsVNew) =
        V.unzip3 $ V.zipWith4 updateV mAdamV vAdamV paramsV gradientV
      updateL mA vA p g = if HM.rows g <= 0  -- eval didn't update it; crash
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
