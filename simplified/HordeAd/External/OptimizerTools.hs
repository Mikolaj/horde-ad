{-# LANGUAGE TypeFamilies #-}
-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient
  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), initialStateAdam
  , updateWithGradientAdam
  ) where

import Prelude

import           Control.Monad.ST.Strict (runST)
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Internal.Delta (Domains)

updateWithGradient :: (Numeric r, Floating (Vector r))
                   => r -> Domains r -> Domains r -> Domains r
updateWithGradient gamma (params0, params1)
                         (gradient0, gradient1) =
  let updateVector i r = i - HM.scale gamma r
      !params0New = updateVector params0 gradient0
      update1 i r = if V.null r  -- eval didn't update it, would crash
                    then i
                    else updateVector i r
      !params1New = V.zipWith update1 params1 gradient1
  in (params0New, params1New)
{-# SPECIALIZE updateWithGradient :: Double -> Domains Double -> Domains Double -> Domains Double #-}

gradientIsNil :: (Eq r, Numeric r) => Domains r -> Bool
gradientIsNil (gradient0, gradient1) =
  V.all (== 0) gradient0
  && V.all V.null gradient1

minimumGradient :: (Ord r, Numeric r) => Domains r -> r
minimumGradient (gradient0, gradient1) =
  min (if V.null gradient0 then 0 else HM.minElement gradient0)
      (if V.null gradient1 then 0
       else V.minimum (V.map HM.minElement gradient1))

maximumGradient :: (Ord r, Numeric r) => Domains r -> r
maximumGradient (gradient0, gradient1) =
  max (if V.null gradient0 then 0 else HM.maxElement gradient0)
      (if V.null gradient1 then 0
       else V.maximum (V.map HM.maxElement gradient1))

data ArgsAdam r = ArgsAdam
  { alpha   :: r
  , betaOne :: r
  , betaTwo :: r
  , epsilon :: r
  }

-- The defaults taken from
-- https://www.tensorflow.org/api_docs/python/tf/keras/optimizers/Adam
defaultArgsAdam :: Fractional r => ArgsAdam r
defaultArgsAdam = ArgsAdam
  { alpha = 0.001
  , betaOne = 0.9
  , betaTwo = 0.999
  , epsilon = 1e-7
  }

data StateAdam r = StateAdam
  { tAdam :: Int  -- iteration count
  , mAdam :: Domains r
  , vAdam :: Domains r
  }

-- The arguments are just sample params0, for dimensions.
zeroParameters :: Numeric r
               => Domains r -> Domains r
zeroParameters (params0, params1) =
  let zeroVector v = runST $ do
        vThawed <- V.thaw v
        VM.set vThawed 0
        V.unsafeFreeze vThawed
  in ( zeroVector params0
     , V.map zeroVector params1 )

initialStateAdam :: Numeric r
                 => Domains r -> StateAdam r
initialStateAdam parameters0 =
  let zeroP = zeroParameters parameters0
  in StateAdam
       { tAdam = 0
       , mAdam = zeroP
       , vAdam = zeroP
       }

updateWithGradientAdam
  :: forall r. (Numeric r, Floating r, Floating (Vector r))
  => ArgsAdam r -> StateAdam r -> Domains r -> Domains r
  -> (Domains r, StateAdam r)
updateWithGradientAdam ArgsAdam{..}
                       StateAdam{ tAdam
                                , mAdam = (mAdam0, mAdam1)
                                , vAdam = (vAdam0, vAdam1)
                                }
                       (params0, params1)
                       (gradient0, gradient1) =
  let tAdamNew = tAdam + 1
      oneMinusBeta1 = 1 - betaOne
      oneMinusBeta2 = 1 - betaTwo
      updateVector :: Vector r -> Vector r
                   -> Vector r -> Vector r
                   -> (Vector r, Vector r, Vector r)
      updateVector mA vA p g =
        let mANew = HM.scale betaOne mA + HM.scale oneMinusBeta1 g
            vANew = HM.scale betaTwo vA + HM.scale oneMinusBeta2 (g * g)
            alphat = alpha * sqrt (1 - betaTwo ^ tAdamNew)
                             / (1 - betaOne ^ tAdamNew)
        in ( mANew
           , vANew
           , p - HM.scale alphat mANew
                 / (sqrt vANew + HM.scalar epsilon) )  -- the @scalar@ is safe
                      -- @addConstant@ would be better, but it's not exposed
      (!mAdam0New, !vAdam0New, !params0New) =
        updateVector mAdam0 vAdam0 params0 gradient0
      update1 mA vA p g = if V.null g  -- eval didn't update it, would crash
                          then (mA, vA, p)
                          else updateVector mA vA p g
      (!mAdam1New, !vAdam1New, !params1New) =
        V.unzip3 $ V.zipWith4 update1 mAdam1 vAdam1 params1 gradient1
  in ( (params0New, params1New)
     , StateAdam { tAdam = tAdamNew
                 , mAdam = (mAdam0New, mAdam1New)
                 , vAdam = (vAdam0New, vAdam1New)
                 }
     )
