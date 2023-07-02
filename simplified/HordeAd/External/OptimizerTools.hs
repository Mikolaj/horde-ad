-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient, updateWithGradientR
--  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), initialStateAdam
  , updateWithGradientAdam
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA

import HordeAd.Core.Adaptor
import HordeAd.Core.TensorOps (isTensorDummy)
import HordeAd.Internal.OrthotopeOrphanInstances (liftVD2)

updateWithGradient
  :: (Numeric r, Fractional r, Show r, Floating (Vector r))
  => Double -> DomainsOD r -> DomainsOD r -> DomainsOD r
updateWithGradient gamma paramsR gradientR =
  let updateVector i r = i - LA.scale (realToFrac gamma) r
      updateR i r = if isTensorDummy r  -- eval didn't update it, would crash
                    then i
                    else liftVD2 updateVector i r
  in V.zipWith updateR paramsR gradientR
{-# SPECIALIZE updateWithGradient :: Double -> DomainsOD Double -> DomainsOD Double -> DomainsOD Double #-}

updateWithGradientR
  :: (Numeric r, Fractional r, Show r, Floating (Vector r))
  => Double -> DomainsOD r -> DomainsOD r -> DomainsOD r
updateWithGradientR gamma params gradient =
  let updateVector i r = i - LA.scale (realToFrac gamma) r
      updateR i r = if isTensorDummy r  -- eval didn't update it, would crash
                    then i
                    else liftVD2 updateVector i r
  in V.zipWith updateR params gradient
{-# SPECIALIZE updateWithGradientR :: Double -> DomainsOD Double -> DomainsOD Double -> DomainsOD Double #-}

{-
gradientIsNil :: (Eq r, Numeric r) => DomainsOD r -> Bool
gradientIsNil (DomainsOD gradient0 gradientR) =
  V.all (== 0) gradient0
  && V.all isTensorDummy gradientR

minimumGradient :: (Ord r, Numeric r) => DomainsOD r -> r
minimumGradient (DomainsOD gradient0 gradientR) =
  min (if V.null gradient0 then 0 else LA.minElement gradient0)
      (if V.null gradientR then 0
       else V.minimum (V.map OD.minimumA gradientR))

maximumGradient :: (Ord r, Numeric r) => DomainsOD r -> r
maximumGradient (DomainsOD gradient0 gradientR) =
  max (if V.null gradient0 then 0 else LA.maxElement gradient0)
      (if V.null gradientR then 0
       else V.maximum (V.map OD.maximumA gradientR))
-}

data ArgsAdam = ArgsAdam
  { alpha   :: Double
  , betaOne :: Double
  , betaTwo :: Double
  , epsilon :: Double
  }

-- The defaults taken from
-- https://www.tensorflow.org/api_docs/python/tf/keras/optimizers/Adam
defaultArgsAdam :: ArgsAdam
defaultArgsAdam = ArgsAdam
  { alpha = 0.001
  , betaOne = 0.9
  , betaTwo = 0.999
  , epsilon = 1e-7
  }

data StateAdam r = StateAdam
  { tAdam :: Int  -- iteration count
  , mAdam :: DomainsOD r
  , vAdam :: DomainsOD r
  }

-- The arguments are just sample params0, for dimensions.
zeroParameters
  :: Numeric r
  => DomainsOD r -> DomainsOD r
zeroParameters params = V.map (\a -> OD.constant (OD.shapeL a) 0) params

initialStateAdam
  :: Numeric r
  => DomainsOD r -> StateAdam r
initialStateAdam parameters0 =
  let zeroP = zeroParameters parameters0
  in StateAdam
       { tAdam = 0
       , mAdam = zeroP
       , vAdam = zeroP
       }

-- TOOD: make sure this is not worse that OD.zipWith3A when transposing
-- between each application or that we never encounter such situations
--
-- | Application of a vector function on the flattened arrays elements.
liftArray43 :: ( Numeric a, Numeric b, Numeric c, Numeric d
               , Numeric x, Numeric y, Numeric z )
            => (Vector a -> Vector b -> Vector c -> Vector d
                -> (Vector x, Vector y, Vector z))
            -> OD.Array a -> OD.Array b -> OD.Array c -> OD.Array d
            -> (OD.Array x, OD.Array y, OD.Array z)
liftArray43 f m1 m2 m3 m4 =
  let sz = OD.shapeL m1
  in if sz == OD.shapeL m2 && sz == OD.shapeL m3 && sz == OD.shapeL m4
     then let (vx, vy, vz) = f (OD.toVector m1) (OD.toVector m2)
                               (OD.toVector m3) (OD.toVector m4)
          in ( OD.fromVector sz vx
             , OD.fromVector sz vy
             , OD.fromVector sz vz
             )
     else error
          $ "nonconformant arrays in liftArray43: "
            ++ show (OD.shapeL m1, OD.shapeL m2, OD.shapeL m3, OD.shapeL m4)

updateWithGradientAdam
  :: forall r.
     (Numeric r, Floating r, Floating (Vector r))
  => ArgsAdam -> StateAdam r -> DomainsOD r -> DomainsOD r
  -> (DomainsOD r, StateAdam r)
updateWithGradientAdam ArgsAdam{..} StateAdam{tAdam, mAdam, vAdam}
                       paramsR gradientR =
  let mAdamR = mAdam
      vAdamR = vAdam
      tAdamNew = tAdam + 1
      oneMinusBeta1 = 1 - betaOne
      oneMinusBeta2 = 1 - betaTwo
      updateVector :: Vector r -> Vector r
                   -> Vector r -> Vector r
                   -> (Vector r, Vector r, Vector r)
      updateVector mA vA p g =
        let mANew = LA.scale (realToFrac betaOne) mA
                    + LA.scale (realToFrac oneMinusBeta1) g
            vANew = LA.scale (realToFrac betaTwo) vA
                    + LA.scale (realToFrac oneMinusBeta2) (g * g)
            alphat = alpha * sqrt (1 - betaTwo ^ tAdamNew)
                             / (1 - betaOne ^ tAdamNew)
        in ( mANew
           , vANew
           , p - LA.scale (realToFrac alphat) mANew
                 / (sqrt vANew + LA.scalar (realToFrac epsilon)) )
                      -- the @scalar@ is safe here;
                      -- @addConstant@ would be better, but it's not exposed
      updateR mA vA p g = if isTensorDummy g  -- eval didn't update it
                          then (mA, vA, p)
                          else liftArray43 updateVector mA vA p g
      (!mAdamRNew, !vAdamRNew, !paramsRNew) =
        V.unzip3 $ V.zipWith4 updateR mAdamR vAdamR paramsR gradientR
  in ( paramsRNew
     , StateAdam
         { tAdam = tAdamNew
         , mAdam = mAdamRNew
         , vAdam = vAdamRNew
         }
     )
