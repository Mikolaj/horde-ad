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
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Storable as VS
import           GHC.TypeLits (KnownNat, sameNat)
import           Numeric.LinearAlgebra (Numeric)
import qualified Numeric.LinearAlgebra as LA
import           Type.Reflection (typeRep)

import qualified Data.Array.Mixed.Internal.Arith as Mixed.Internal.Arith
import qualified Data.Array.Nested as Nested
import qualified Data.Array.Nested.Internal.Mixed as Nested.Internal.Mixed
import qualified Data.Array.Nested.Internal.Ranked as Nested.Internal
import qualified Data.Array.Nested.Internal.Shaped as Nested.Internal

import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorConcrete ()
import HordeAd.Core.Types
import HordeAd.Internal.BackendOX (ORArray)
import HordeAd.Internal.OrthotopeOrphanInstances

updateWithGradient :: Double -> HVector ORArray -> HVector ORArray -> HVector ORArray
updateWithGradient gamma params gradient =
  let updateVector :: (Numeric r, Fractional r, Num (VS.Vector r))
                   => Either r (VS.Vector r) -> Either r (VS.Vector r)
                   -> VS.Vector r
      updateVector i' r' = let i = either VS.singleton id i'
                               r = either VS.singleton id r'
                           in i - LA.scale (realToFrac gamma) r
        -- TODO: do this on tensors instead of vectors to use ox-arrays machinery instead of LA machinery to optimize this: V.map (* realToFrac gamma)
      updateR :: DynamicTensor ORArray -> DynamicTensor ORArray
              -> DynamicTensor ORArray
      updateR i r = case (i, r) of
        (DynamicRanked @r1 @n1 t1, DynamicRanked @r2 @n2 t2) ->
          ifDifferentiable @r1
            (case sameNat (Proxy @n1) (Proxy @n2) of
               Just Refl -> case testEquality (typeRep @r1) (typeRep @r2) of
                 Just Refl ->
                   DynamicRanked $ FlipR
                   $ Nested.Internal.arithPromoteRanked2
                       (Nested.Internal.Mixed.mliftNumElt2
                          (flip Mixed.Internal.Arith.liftVEltwise2
                             updateVector))
                       (runFlipR t1) (runFlipR t2)
                 _ -> error "updateWithGradient: scalar mismatch"
               _ -> error "updateWithGradient: rank mismatch")
          i
        (DynamicShaped @r1 @sh1 t1, DynamicShaped @r2 @sh2 t2) ->
          ifDifferentiable @r1
            (case sameShape @sh1 @sh2 of
               Just Refl -> case testEquality (typeRep @r1) (typeRep @r2) of
                 Just Refl ->
                   DynamicShaped $ FlipS
                   $ Nested.Internal.arithPromoteShaped2
                       (Nested.Internal.Mixed.mliftNumElt2
                          (flip Mixed.Internal.Arith.liftVEltwise2
                             updateVector))
                       (runFlipS t1) (runFlipS t2)
                 _ -> error "updateWithGradient: scalar mismatch"
               _ -> error "updateWithGradient: rank mismatch")
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

-- TOOD: make sure this is not worse that OR.zipWith3A when transposing
-- between each application or that we never encounter such situations
--
-- | Application of a vector function on the flattened arrays elements.
liftArray43 :: ( Numeric a, Numeric b, Numeric c, Numeric d
               , Numeric x, Numeric y, Numeric z, KnownNat n )
            => (VS.Vector a -> VS.Vector b -> VS.Vector c -> VS.Vector d
                -> (VS.Vector x, VS.Vector y, VS.Vector z))
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
  :: ArgsAdam -> StateAdam -> HVector ORArray -> HVector ORArray
  -> (HVector ORArray, StateAdam)
updateWithGradientAdam ArgsAdam{..} StateAdam{tAdam, mAdam, vAdam}
                       paramsR gradientR =
  let mAdamR = mAdam
      vAdamR = vAdam
      tAdamNew = tAdam + 1
      oneMinusBeta1 = 1 - betaOne
      oneMinusBeta2 = 1 - betaTwo
      updateVector :: (Numeric r, Fractional r, Floating (VS.Vector r))
                   => VS.Vector r -> VS.Vector r
                   -> VS.Vector r -> VS.Vector r
                   -> (VS.Vector r, VS.Vector r, VS.Vector r)
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
                 / (sqrt vANew + V.singleton (realToFrac epsilon)) )
                      -- the @LA.scalar@ (V.singleton) is safe here;
                      -- @addConstant@ would be better, but it's not exposed
        -- TODO: do this on tensors instead of vectors to use ox-arrays machinery instead of LA machinery to optimize this: V.map (* realToFrac x)
      updateR :: DynamicTensor ORArray -> DynamicTensor ORArray
              -> DynamicTensor ORArray -> DynamicTensor ORArray
              -> ( DynamicTensor ORArray
                 , DynamicTensor ORArray
                 , DynamicTensor ORArray )
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
                     liftArray43 updateVector (Nested.rtoOrthotope $ runFlipR mA)
                                              (Nested.rtoOrthotope $ runFlipR vA)
                                              (Nested.rtoOrthotope $ runFlipR p)
                                              (Nested.rtoOrthotope $ runFlipR g)
               in ( DynamicRanked $ FlipR $ Nested.rfromOrthotope SNat od1
                  , DynamicRanked $ FlipR $ Nested.rfromOrthotope SNat od2
                  , DynamicRanked $ FlipR $ Nested.rfromOrthotope SNat od3 )
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
