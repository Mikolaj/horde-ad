-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient
--  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdamDeep(..), initialStateAdamDeep
  , updateWithGradientAdamDeep
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
gradientIsNil :: (Eq r) => HVector ORArray -> Bool
gradientIsNil (HVector ORArray gradient0 gradientR) =
  V.all (== 0) gradient0
  && V.all isTensorDummyD gradientR

minimumGradient :: (Ord r) => HVector ORArray -> r
minimumGradient (HVector ORArray gradient0 gradientR) =
  min (if V.null gradient0 then 0 else LA.minElement gradient0)
      (if V.null gradientR then 0
       else V.minimum (V.map OR.minimumA gradientR))

maximumGradient :: (Ord r) => HVector ORArray -> r
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

type family Triplify y where
  Triplify (TKR r n) = TKProduct (TKProduct (TKR r n) (TKR r n)) (TKR r n)
  Triplify (TKS r sh) = TKProduct (TKProduct (TKS r sh) (TKS r sh)) (TKS r sh)
  Triplify (TKX r sh) = TKProduct (TKProduct (TKX r sh) (TKX r sh)) (TKX r sh)
  Triplify (TKProduct x z) = TKProduct (Triplify x) (Triplify z)
  Triplify TKUnit = TKUnit
  Triplify TKUntyped = TKUntyped  -- this it not tripled

unzip3Rep
  :: STensorKindType y -> Rep ORArray (Triplify y)
  -> (Rep ORArray y, Rep ORArray y, Rep ORArray y)
unzip3Rep stk t = case stk of
  STKR{} -> (fst $ fst t, snd $ fst t, snd t)
  STKS{} -> (fst $ fst t, snd $ fst t, snd t)
  STKX{} -> (fst $ fst t, snd $ fst t, snd t)
  STKProduct stk1 stk2 -> let (a1, b1, c1) = unzip3Rep stk1 $ fst t
                              (a2, b2, c2) = unzip3Rep stk2 $ snd t
                          in ((a1, a2), (b1, b2), (c1, c2))
  STKUnit -> (t, t, t)
  STKUntyped -> (t, t, t)

type role StateAdamDeep nominal
data StateAdamDeep y = StateAdamDeep
  { tAdamDeep :: Int  -- iteration count
  , mAdamDeep :: Rep ORArray y
  , vAdamDeep :: Rep ORArray y
  }

initialStateAdamDeep :: TensorKindFull y -> StateAdamDeep y
initialStateAdamDeep ftk =
  StateAdamDeep { tAdamDeep = 0
                , mAdamDeep = repDeepZero ftk
                , vAdamDeep = repDeepZero ftk
                }

-- TODO: introduce and use dummies
repDeepZero :: TensorKindFull y -> Rep ORArray y
repDeepZero = \case
  FTKR sh -> FlipR $ Nested.rreplicateScal sh 0
  FTKS sh -> FlipS $ Nested.sreplicateScal sh 0
  FTKX sh -> FlipX $ Nested.mreplicateScal sh 0
  FTKProduct ftk1 ftk2 -> (repDeepZero ftk1, repDeepZero ftk2)
  FTKUnit -> RepUnit ()
  FTKUntyped{} -> error "repDeepZero: FTKUntyped"

updateWithGradientAdamDeep
  :: TensorKind y
  => ArgsAdam -> StateAdamDeep y -> Rep ORArray y -> Rep ORArray (ADTensorKind y)
  -> (Rep ORArray y, StateAdamDeep y)
updateWithGradientAdamDeep ArgsAdam{..} StateAdamDeep{..} paramsR gradientR =
  let mAdamR = mAdamDeep
      vAdamR = vAdamDeep
      tAdamNew = tAdamDeep + 1
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
      updateProd :: forall y2.
                    STensorKindType y2
                 -> Rep ORArray y2 -> Rep ORArray y2
                 -> Rep ORArray y2 -> Rep ORArray (ADTensorKind y2)
                 -> Rep ORArray (Triplify y2)
      updateProd stk mA vA p g
       | Dict <- lemTensorKindOfAD stk = case stk of
        STKR @r _ SNat ->
          case sameTensorKind @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let (mAN, vAN, pN) = updateR (runFlipR mA) (runFlipR vA)
                                              (runFlipR p) (runFlipR g)
                 in ((FlipR mAN, FlipR vAN), FlipR pN))
                ((mA, vA), p)
            _ -> ((mA, vA), p)
        STKS @r _ sh -> withKnownShS sh $
          case sameTensorKind @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let (mAN, vAN, pN) =
                       updateR (Nested.stoRanked (runFlipS mA))
                               (Nested.stoRanked (runFlipS vA))
                               (Nested.stoRanked (runFlipS p))
                               (Nested.stoRanked (runFlipS g))
                 in ( ( FlipS $ Nested.rcastToShaped mAN knownShS
                      , FlipS $ Nested.rcastToShaped vAN knownShS )
                    , FlipS $ Nested.rcastToShaped pN knownShS ))
                ((mA, vA), p)
            _ -> ((mA, vA), p)
        STKX @r _ sh -> withKnownShX sh $
          case sameTensorKind @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let (mAN, vAN, pN) =
                       updateR (Nested.mtoRanked (runFlipX mA))
                               (Nested.mtoRanked (runFlipX vA))
                               (Nested.mtoRanked (runFlipX p))
                               (Nested.mtoRanked (runFlipX g))
                 in ( ( FlipX $ Nested.mreshape (Nested.mshape (runFlipX mA))
                              $ Nested.rtoMixed mAN
                      , FlipX $ Nested.mreshape (Nested.mshape (runFlipX vA))
                              $ Nested.rtoMixed vAN )
                    , FlipX $ Nested.mreshape (Nested.mshape (runFlipX p))
                              $ Nested.rtoMixed pN ))
                ((mA, vA), p)
            _ -> ((mA, vA), p)
        STKProduct stk1 stk2 ->
          ( updateProd stk1 (fst mA) (fst vA) (fst p) (fst g)
          , updateProd stk2 (snd mA) (snd vA) (snd p) (snd g) )
        STKUnit -> RepUnit ()
        STKUntyped -> error "updateProd: STKUntyped"
      (!mAdamRNew, !vAdamRNew, !paramsRNew) =
        unzip3Rep stensorKind
        $ updateProd stensorKind mAdamR vAdamR paramsR gradientR
  in ( paramsRNew
     , StateAdamDeep
         { tAdamDeep = tAdamNew
         , mAdamDeep = mAdamRNew
         , vAdamDeep = vAdamRNew
         }
     )

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
