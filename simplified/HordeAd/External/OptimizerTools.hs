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

import HordeAd.Core.Domains
import HordeAd.Internal.OrthotopeOrphanInstances (liftVT2)
import HordeAd.Internal.TensorOps (isTensorDummy)

updateWithGradient
  :: ( Numeric r, Floating (Vector r)
     , DomainsCollection r, DTensorOf r ~ OD.Array r )
  => r -> Domains r -> Domains r -> Domains r
updateWithGradient gamma params gradient =
  let paramsR = toVectorDoms params
      gradientR = toVectorDoms gradient
      updateVector i r = i - LA.scale gamma r
      updateR i r = if isTensorDummy r  -- eval didn't update it, would crash
                    then i
                    else liftVT2 updateVector i r
      !paramsRNew = V.zipWith updateR paramsR gradientR
  in fromVectorDoms paramsRNew
{-# SPECIALIZE updateWithGradient :: Double -> Domains Double -> Domains Double -> Domains Double #-}

updateWithGradientR
  :: ( Numeric r, Floating (Vector r), DTensorOf r ~ OD.Array r
     , DomainsCollection r )
  => r -> Domains r -> Domains r -> Domains r
updateWithGradientR gamma params gradient =
  let updateVector i r = i - LA.scale gamma r
      updateR i r = if isTensorDummy r  -- eval didn't update it, would crash
                    then i
                    else liftVT2 updateVector i r
  in fromVectorDoms
     $ V.zipWith updateR (toVectorDoms params) (toVectorDoms gradient)
{-# SPECIALIZE updateWithGradientR :: Double -> Domains Double -> Domains Double -> Domains Double #-}

{-
gradientIsNil :: (Eq r, Numeric r) => Domains r -> Bool
gradientIsNil (Domains gradient0 gradientR) =
  V.all (== 0) gradient0
  && V.all isTensorDummy gradientR

minimumGradient :: (Ord r, Numeric r) => Domains r -> r
minimumGradient (Domains gradient0 gradientR) =
  min (if V.null gradient0 then 0 else LA.minElement gradient0)
      (if V.null gradientR then 0
       else V.minimum (V.map OD.minimumA gradientR))

maximumGradient :: (Ord r, Numeric r) => Domains r -> r
maximumGradient (Domains gradient0 gradientR) =
  max (if V.null gradient0 then 0 else LA.maxElement gradient0)
      (if V.null gradientR then 0
       else V.maximum (V.map OD.maximumA gradientR))
-}

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
zeroParameters
  :: ( Numeric r, DTensorOf r ~ OD.Array r, DomainsCollection r )
  => Domains r -> Domains r
zeroParameters params =
  fromVectorDoms (V.map (\a -> OD.constant (OD.shapeL a) 0) (toVectorDoms params))

initialStateAdam
  :: ( Numeric r, DTensorOf r ~ OD.Array r
     , DomainsCollection r )
  => Domains r -> StateAdam r
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
     ( Numeric r, Floating r, Floating (Vector r)
     , DomainsCollection r, DTensorOf r ~ OD.Array r )
  => ArgsAdam r -> StateAdam r -> Domains r -> Domains r
  -> (Domains r, StateAdam r)
updateWithGradientAdam ArgsAdam{..} StateAdam{tAdam, mAdam, vAdam}
                       params gradient =
  let mAdamR = toVectorDoms mAdam
      vAdamR = toVectorDoms vAdam
      paramsR = toVectorDoms params
      gradientR = toVectorDoms gradient
      tAdamNew = tAdam + 1
      oneMinusBeta1 = 1 - betaOne
      oneMinusBeta2 = 1 - betaTwo
      updateVector :: Vector r -> Vector r
                   -> Vector r -> Vector r
                   -> (Vector r, Vector r, Vector r)
      updateVector mA vA p g =
        let mANew = LA.scale betaOne mA + LA.scale oneMinusBeta1 g
            vANew = LA.scale betaTwo vA + LA.scale oneMinusBeta2 (g * g)
            alphat = alpha * sqrt (1 - betaTwo ^ tAdamNew)
                             / (1 - betaOne ^ tAdamNew)
        in ( mANew
           , vANew
           , p - LA.scale alphat mANew
                 / (sqrt vANew + LA.scalar epsilon) )  -- the @scalar@ is safe
                      -- @addConstant@ would be better, but it's not exposed
      updateR mA vA p g = if isTensorDummy g  -- eval didn't update it
                          then (mA, vA, p)
                          else liftArray43 updateVector mA vA p g
      (!mAdamRNew, !vAdamRNew, !paramsRNew) =
        V.unzip3 $ V.zipWith4 updateR mAdamR vAdamR paramsR gradientR
  in ( fromVectorDoms paramsRNew
     , StateAdam
         { tAdam = tAdamNew
         , mAdam = fromVectorDoms mAdamRNew
         , vAdam = fromVectorDoms vAdamRNew
         }
     )
