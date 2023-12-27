-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient
--  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), initialStateAdam
  , updateWithGradientAdam
  ) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Type.Reflection (typeRep)

import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances

updateWithGradient :: Double -> DomainsOD -> DomainsOD -> DomainsOD
updateWithGradient gamma params gradient =
  let updateVector :: (Numeric r, Fractional r, Num (Vector r))
                   => Vector r -> Vector r -> Vector r
      updateVector i r = i - LA.scale (realToFrac gamma) r
      updateR :: DynamicTensor (Flip OR.Array) -> DynamicTensor (Flip OR.Array)
              -> DynamicTensor (Flip OR.Array)
      updateR i r = case (i, r) of
        (DynamicRanked @r1 @n1 t1, DynamicRanked @r2 @n2 t2) ->
          ifDifferentiable @r1
            (case sameNat (Proxy @n1) (Proxy @n2) of
               Just Refl -> case testEquality (typeRep @r1) (typeRep @r2) of
                 Just Refl ->
                   DynamicRanked $ Flip
                   $ liftVR2 updateVector (runFlip t1) (runFlip t2)
                 _ -> error "updateWithGradient: scalar mismatch"
               _ -> error "updateWithGradient: rank mismatch")
          i
        (DynamicShaped @r1 @sh1 t1, DynamicShaped @r2 @sh2 t2) ->
          ifDifferentiable @r1
            (case sameShape @sh1 @sh2 of
               Just Refl -> case testEquality (typeRep @r1) (typeRep @r2) of
                 Just Refl ->
                   DynamicShaped $ Flip
                   $ liftVS2 updateVector (runFlip t1) (runFlip t2)
                 _ -> error "updateWithGradient: scalar mismatch"
               _ -> error "updateWithGradient: rank mismatch")
          i
        _ -> i   -- eval didn't update the gradient, save on computation
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
       else V.minimum (V.map OR.minimumA gradientR))

maximumGradient :: (Ord r, Numeric r) => DomainsOD -> r
maximumGradient (DomainsOD gradient0 gradientR) =
  max (if V.null gradient0 then 0 else LA.maxElement gradient0)
      (if V.null gradientR then 0
       else V.maximum (V.map OR.maximumA gradientR))
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
zeroParameters =
  let f (DynamicRanked @r @n t) =
        let sh = rshape @(Flip OR.Array) t
        in DynamicRanked @r @n $ rzero @(Flip OR.Array) sh
      f (DynamicShaped @r @sh _) = DynamicShaped @r @sh 0
      f DynamicRankedDummy{} = error "zeroParameters: unexpected value"
      f DynamicShapedDummy{} = error "zeroParameters: unexpected value"
  in V.map f

initialStateAdam :: DomainsOD -> StateAdam
initialStateAdam parameters0 =
  let zeroP = zeroParameters parameters0
  in StateAdam
       { tAdam = 0
       , mAdam = zeroP
       , vAdam = zeroP
       }

-- TOOD: make sure this is not worse that OR.zipWith3A when transposing
-- between each application or that we never encounter such situations
--
-- | Application of a vector function on the flattened arrays elements.
liftArray43 :: ( Numeric a, Numeric b, Numeric c, Numeric d
               , Numeric x, Numeric y, Numeric z, KnownNat n )
            => (Vector a -> Vector b -> Vector c -> Vector d
                -> (Vector x, Vector y, Vector z))
            -> OR.Array n a -> OR.Array n b -> OR.Array n c -> OR.Array n d
            -> (OR.Array n x, OR.Array n y, OR.Array n z)
liftArray43 f m1 m2 m3 m4 =
  let sz = OR.shapeL m1
  in if sz == OR.shapeL m2 && sz == OR.shapeL m3 && sz == OR.shapeL m4
     then let (vx, vy, vz) = f (OR.toVector m1) (OR.toVector m2)
                               (OR.toVector m3) (OR.toVector m4)
          in ( OR.fromVector sz vx
             , OR.fromVector sz vy
             , OR.fromVector sz vz
             )
     else error
          $ "nonconformant arrays in liftArray43: "
            ++ show (OR.shapeL m1, OR.shapeL m2, OR.shapeL m3, OR.shapeL m4)

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
      updateR :: DynamicTensor (Flip OR.Array) -> DynamicTensor (Flip OR.Array)
              -> DynamicTensor (Flip OR.Array) -> DynamicTensor (Flip OR.Array)
              -> ( DynamicTensor (Flip OR.Array)
                 , DynamicTensor (Flip OR.Array)
                 , DynamicTensor (Flip OR.Array) )
      updateR emA@(DynamicRanked @r1 @n1 mA) evA@(DynamicRanked @r2 @n2 vA)
              ep@(DynamicRanked @r3 @n3 p) (DynamicRanked @r4 @n4 g) =
        ifDifferentiable @r1
          (case ( sameNat (Proxy @n1) (Proxy @n2)
                , sameNat (Proxy @n1) (Proxy @n3)
                , sameNat (Proxy @n1) (Proxy @n4)
                , testEquality (typeRep @r1) (typeRep @r2)
                , testEquality (typeRep @r1) (typeRep @r3)
                , testEquality (typeRep @r1) (typeRep @r4) ) of
             ( Just Refl, Just Refl, Just Refl
              ,Just Refl, Just Refl, Just Refl ) ->
               let (od1, od2, od3) =
                     liftArray43 updateVector (runFlip mA) (runFlip vA)
                                              (runFlip p) (runFlip g)
               in ( DynamicRanked $ Flip od1
                  , DynamicRanked $ Flip od2
                  , DynamicRanked $ Flip od3 )
             _ -> error "updateWithGradientAdam: type mismatch")
          (emA, evA, ep)
      updateR emA evA ep _ =
        (emA, evA, ep)  -- eval didn't update the gradient, save on computation
      (!mAdamRNew, !vAdamRNew, !paramsRNew) =
        V.unzip3 $ V.zipWith4 updateR mAdamR vAdamR paramsR gradientR
  in ( paramsRNew
     , StateAdam
         { tAdam = tAdamNew
         , mAdam = mAdamRNew
         , vAdam = vAdamRNew
         }
     )
