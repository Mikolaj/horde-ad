-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient
--  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), initialStateAdam
  , updateWithGradientAdam
  ) where

import Prelude

import qualified Data.Array.DynamicS as OD
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Type.Reflection (typeRep)

import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances (liftVD2)
import HordeAd.Internal.TensorOps (isTensorDummyD)

updateWithGradient :: Double -> DomainsOD -> DomainsOD -> DomainsOD
updateWithGradient gamma params gradient =
  let updateVector :: (Numeric r, Fractional r, Num (Vector r))
                   => Vector r -> Vector r -> Vector r
      updateVector i r = i - LA.scale (realToFrac gamma) r
      updateR :: DynamicExists OD.Array -> DynamicExists OD.Array
              -> DynamicExists OD.Array
      updateR ei@(DynamicExists @r1 i) (DynamicExists @r2 r) =
        if isTensorDummyD r  -- eval didn't update it, would crash
        then ei
        else ifDifferentiable @r1
          (case testEquality (typeRep @r1) (typeRep @r2) of
             Just Refl -> DynamicExists $ liftVD2 updateVector i r
             _ -> error "updateWithGradient: type mismatch")
          ei
  in V.zipWith updateR params gradient

{-
gradientIsNil :: (Eq r, Numeric r) => DomainsOD -> Bool
gradientIsNil (DomainsOD gradient0 gradientR) =
  V.all (== 0) gradient0
  && V.all isTensorDummyD gradientR

minimumGradient :: (Ord r, Numeric r) => DomainsOD -> r
minimumGradient (DomainsOD gradient0 gradientR) =
  min (if V.null gradient0 then 0 else LA.minElement gradient0)
      (if V.null gradientR then 0
       else V.minimum (V.map OD.minimumA gradientR))

maximumGradient :: (Ord r, Numeric r) => DomainsOD -> r
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

data StateAdam = StateAdam
  { tAdam :: Int  -- iteration count
  , mAdam :: DomainsOD
  , vAdam :: DomainsOD
  }

-- The arguments are just sample params0, for dimensions.
zeroParameters :: DomainsOD -> DomainsOD
zeroParameters params =
  V.map (\(DynamicExists @r a) -> DynamicExists @r
                                  $ OD.constant (OD.shapeL a) 0)
        params

initialStateAdam :: DomainsOD -> StateAdam
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
  :: ArgsAdam -> StateAdam -> DomainsOD -> DomainsOD
  -> (DomainsOD, StateAdam)
updateWithGradientAdam ArgsAdam{..} StateAdam{tAdam, mAdam, vAdam}
                       paramsR gradientR =
  let mAdamR = mAdam
      vAdamR = vAdam
      tAdamNew = tAdam + 1
      oneMinusBeta1 = 1 - betaOne
      oneMinusBeta2 = 1 - betaTwo
      updateVector :: (Numeric r, Fractional r, Floating (Vector r))
                   => Vector r -> Vector r
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
      updateR :: DynamicExists OD.Array -> DynamicExists OD.Array
              -> DynamicExists OD.Array -> DynamicExists OD.Array
              -> ( DynamicExists OD.Array
                 , DynamicExists OD.Array
                 , DynamicExists OD.Array )
      updateR emA@(DynamicExists @r1 mA) evA@(DynamicExists @r2 vA)
              ep@(DynamicExists @r3 p) (DynamicExists @r4 g) =
        if isTensorDummyD g  -- eval didn't update it
        then (emA, evA, ep)
        else ifDifferentiable @r1
          (case ( testEquality (typeRep @r1) (typeRep @r2)
                , testEquality (typeRep @r2) (typeRep @r3)
                , testEquality (typeRep @r3) (typeRep @r4) ) of
             (Just Refl, Just Refl, Just Refl) ->
               let (od1, od2, od3) = liftArray43 updateVector mA vA p g
               in (DynamicExists od1, DynamicExists od2, DynamicExists od3)
             _ -> error "updateWithGradientAdam: type mismatch")
          (emA, evA, ep)
      (!mAdamRNew, !vAdamRNew, !paramsRNew) =
        V.unzip3 $ V.zipWith4 updateR mAdamR vAdamR paramsR gradientR
  in ( paramsRNew
     , StateAdam
         { tAdam = tAdamNew
         , mAdam = mAdamRNew
         , vAdam = vAdamRNew
         }
     )
