-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient
--  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), initialStateAdam
  , updateWithGradientAdam
  ) where

import Prelude

import           Control.Monad.ST.Strict (runST)
import qualified Data.Array.DynamicS as OT
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA

import HordeAd.Core.Delta (Domains (..))
import HordeAd.Core.TensorClass
import HordeAd.Internal.OrthotopeOrphanInstances (liftVT2)
import HordeAd.Internal.TensorOps (isTensorDummy)

updateWithGradient
  :: (Numeric r, Floating (Vector r), DynamicTensor r ~ OT.Array r)
  => r -> Domains r -> Domains r -> Domains r
updateWithGradient gamma (Domains params0 params1)
                         (Domains gradient0 gradient1) =
  let updateVector i r = i - LA.scale gamma r
      !params0New = updateVector params0 gradient0
      update1 i r = if isTensorDummy r  -- eval didn't update it, would crash
                    then i
                    else liftVT2 updateVector i r
      !params1New = V.zipWith update1 params1 gradient1
  in Domains params0New params1New
{-# SPECIALIZE updateWithGradient :: Double -> Domains Double -> Domains Double -> Domains Double #-}

{-
gradientIsNil :: (Eq r, Numeric r) => Domains r -> Bool
gradientIsNil (Domains gradient0 gradient1) =
  V.all (== 0) gradient0
  && V.all isTensorDummy gradient1

minimumGradient :: (Ord r, Numeric r) => Domains r -> r
minimumGradient (Domains gradient0 gradient1) =
  min (if V.null gradient0 then 0 else LA.minElement gradient0)
      (if V.null gradient1 then 0
       else V.minimum (V.map OT.minimumA gradient1))

maximumGradient :: (Ord r, Numeric r) => Domains r -> r
maximumGradient (Domains gradient0 gradient1) =
  max (if V.null gradient0 then 0 else LA.maxElement gradient0)
      (if V.null gradient1 then 0
       else V.maximum (V.map OT.maximumA gradient1))
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
zeroParameters :: (Numeric r, DynamicTensor r ~ OT.Array r)
               => Domains r -> Domains r
zeroParameters Domains{..} =
  let zeroVector v = runST $ do
        vThawed <- V.thaw v
        VM.set vThawed 0
        V.unsafeFreeze vThawed
  in Domains (zeroVector domains0)
             (V.map (\a -> OT.constant (OT.shapeL a) 0) domains1)

initialStateAdam :: (Numeric r, DynamicTensor r ~ OT.Array r)
                 => Domains r -> StateAdam r
initialStateAdam parameters0 =
  let zeroP = zeroParameters parameters0
  in StateAdam
       { tAdam = 0
       , mAdam = zeroP
       , vAdam = zeroP
       }

-- TOOD: make sure this is not worse that OT.zipWith3A when transposing
-- between each application or that we never encounter such situations
--
-- | Application of a vector function on the flattened arrays elements.
liftArray43 :: ( Numeric a, Numeric b, Numeric c, Numeric d
               , Numeric x, Numeric y, Numeric z )
            => (Vector a -> Vector b -> Vector c -> Vector d
                -> (Vector x, Vector y, Vector z))
            -> OT.Array a -> OT.Array b -> OT.Array c -> OT.Array d
            -> (OT.Array x, OT.Array y, OT.Array z)
liftArray43 f m1 m2 m3 m4 =
  let sz = OT.shapeL m1
  in if sz == OT.shapeL m2 && sz == OT.shapeL m3 && sz == OT.shapeL m4
     then let (vx, vy, vz) = f (OT.toVector m1) (OT.toVector m2)
                               (OT.toVector m3) (OT.toVector m4)
          in ( OT.fromVector sz vx
             , OT.fromVector sz vy
             , OT.fromVector sz vz
             )
     else error
          $ "nonconformant arrays in liftArray43: "
            ++ show (OT.shapeL m1, OT.shapeL m2, OT.shapeL m3, OT.shapeL m4)

updateWithGradientAdam
  :: forall r.
     (Numeric r, Floating r, Floating (Vector r), DynamicTensor r ~ OT.Array r)
  => ArgsAdam r -> StateAdam r -> Domains r -> Domains r
  -> (Domains r, StateAdam r)
updateWithGradientAdam ArgsAdam{..}
                       StateAdam{ tAdam
                                , mAdam = Domains mAdam0 mAdam1
                                , vAdam = Domains vAdam0 vAdam1
                                }
                       (Domains params0 params1)
                       (Domains gradient0 gradient1) =
  let tAdamNew = tAdam + 1
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
      (!mAdam0New, !vAdam0New, !params0New) =
        updateVector mAdam0 vAdam0 params0 gradient0
      update1 mA vA p g = if isTensorDummy g  -- eval didn't update it
                          then (mA, vA, p)
                          else liftArray43 updateVector mA vA p g
      (!mAdam1New, !vAdam1New, !params1New) =
        V.unzip3 $ V.zipWith4 update1 mAdam1 vAdam1 params1 gradient1
  in ( Domains params0New params1New
     , StateAdam { tAdam = tAdamNew
                 , mAdam = Domains mAdam0New mAdam1New
                 , vAdam = Domains vAdam0New vAdam1New
                 }
     )
