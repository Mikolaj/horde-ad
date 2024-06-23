-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient
--  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), initialStateAdam
  , updateWithGradientAdam
  ) where

import Prelude

import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (sameNat)
import Type.Reflection (typeRep)

import Data.Array.Nested qualified as Nested

import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorConcrete ()
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray)
import HordeAd.Internal.OrthotopeOrphanInstances

updateWithGradient :: Double -> HVector ORArray -> HVector ORArray -> HVector ORArray
updateWithGradient gamma params gradient =
  let updateR :: DynamicTensor ORArray -> DynamicTensor ORArray
              -> DynamicTensor ORArray
      updateR i r = case (i, r) of
        ( DynamicRanked @r1 @n1 (FlipR i2)
         ,DynamicRanked @r2 @n2 (FlipR r2)) ->
          ifDifferentiable @r1
            (case sameNat (Proxy @n1) (Proxy @n2) of
               Just Refl -> case testEquality (typeRep @r1) (typeRep @r2) of
                 Just Refl ->
                   DynamicRanked $ FlipR
                   $ i2 - Nested.rreplicateScal (Nested.rshape i2)
                                                (realToFrac gamma)
                          * r2
                 _ -> error "updateWithGradient: scalar mismatch"
               _ -> error "updateWithGradient: rank mismatch")
          i
        ( DynamicShaped @r1 @sh1 (FlipS i2)
         ,DynamicShaped @r2 @sh2 (FlipS r2) ) ->
          ifDifferentiable @r1
            (case sameShape @sh1 @sh2 of
               Just Refl -> case testEquality (typeRep @r1) (typeRep @r2) of
                 Just Refl ->
                   DynamicShaped $ FlipS
                   $ i2 - Nested.sreplicateScal (Nested.sshape i2)
                                                (realToFrac gamma)
                          * r2
                 _ -> error "updateWithGradient: scalar mismatch"
               _ -> error "updateWithGradient: shape mismatch")
          i
        _ -> i   -- eval didn't update the gradient, save on computation
  in V.zipWith updateR params gradient

{-
gradientIsNil :: (Eq r, Numeric r) => HVector ORArray -> Bool
gradientIsNil (HVector ORArray gradient0 gradientR) =
  V.all (== 0) gradient0
  && V.all isTensorDummyD gradientR

minimumGradient :: (Ord r, Numeric r) => HVector ORArray -> r
minimumGradient (HVector ORArray gradient0 gradientR) =
  min (if V.null gradient0 then 0 else LA.minElement gradient0)
      (if V.null gradientR then 0
       else V.minimum (V.map OR.minimumA gradientR))

maximumGradient :: (Ord r, Numeric r) => HVector ORArray -> r
maximumGradient (HVector ORArray gradient0 gradientR) =
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
  , mAdam :: HVector ORArray
  , vAdam :: HVector ORArray
  }

initialStateAdam :: VoidHVector -> StateAdam
initialStateAdam parameters0 =
  let zeroP = V.map dynamicFromVoid parameters0
  in StateAdam
       { tAdam = 0
       , mAdam = zeroP
       , vAdam = zeroP
       }

updateWithGradientAdam
  :: ArgsAdam -> StateAdam -> HVector ORArray -> HVector ORArray
  -> (HVector ORArray, StateAdam)
updateWithGradientAdam ArgsAdam{..} StateAdam{tAdam, mAdam, vAdam}
                       paramsR gradientR =
  let mAdamR = mAdam
      vAdamR = vAdam
      tAdamNew = tAdam + 1
      oneMinusBeta1 = 1 - betaOne
      oneMinusBeta2 = 1 - betaTwo
      updateR :: ( Fractional r
                 , Nested.NumElt r, Nested.FloatElt r, Nested.PrimElt r )
              => Nested.Ranked n r -> Nested.Ranked n r
              -> Nested.Ranked n r -> Nested.Ranked n r
              -> (Nested.Ranked n r, Nested.Ranked n r, Nested.Ranked n r)
      updateR mA vA p g =
        let sh = Nested.rshape g
            mANew = Nested.rreplicateScal sh (realToFrac betaOne) * mA
                    + Nested.rreplicateScal sh (realToFrac oneMinusBeta1) * g
            vANew = Nested.rreplicateScal sh (realToFrac betaTwo) * vA
                    + Nested.rreplicateScal sh (realToFrac oneMinusBeta2)
                      * (g * g)
            alphat = alpha * sqrt (1 - betaTwo ^ tAdamNew)
                             / (1 - betaOne ^ tAdamNew)
        in ( mANew
           , vANew
           , p - (Nested.rreplicateScal sh (realToFrac alphat) * mANew)
                 / (sqrt vANew
                    + Nested.rreplicateScal sh (realToFrac epsilon)) )
      updateD :: DynamicTensor ORArray -> DynamicTensor ORArray
              -> DynamicTensor ORArray -> DynamicTensor ORArray
              -> ( DynamicTensor ORArray
                 , DynamicTensor ORArray
                 , DynamicTensor ORArray )
      updateD emA@(DynamicRanked @r1 @n1 mA) evA@(DynamicRanked @r2 @n2 vA)
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
               let (od1, od2, od3) = updateR (runFlipR mA) (runFlipR vA)
                                             (runFlipR p) (runFlipR g)
               in ( DynamicRanked $ FlipR od1
                  , DynamicRanked $ FlipR od2
                  , DynamicRanked $ FlipR od3 )
             _ -> error "updateWithGradientAdam: type mismatch")
          (emA, evA, ep)
      updateD emA evA ep _ =
        (emA, evA, ep)  -- eval didn't update the gradient, save on computation
      (!mAdamRNew, !vAdamRNew, !paramsRNew) =
        V.unzip3 $ V.zipWith4 updateD mAdamR vAdamR paramsR gradientR
  in ( paramsRNew
     , StateAdam
         { tAdam = tAdamNew
         , mAdam = mAdamRNew
         , vAdam = vAdamRNew
         }
     )
