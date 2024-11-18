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

import Data.Array.Nested (KnownShS (..), ShR (..), pattern ZSR)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.Types

updateWithGradient :: Double -> HVector RepN -> HVector RepN -> HVector RepN
updateWithGradient gamma params gradient =
  let updateR :: DynamicTensor RepN -> DynamicTensor RepN
              -> DynamicTensor RepN
      updateR i r = case (i, r) of
        ( DynamicRanked @r1 @n1 (RepN i2)
         ,DynamicRanked @r2 @n2 (RepN r2) ) ->
          ifDifferentiable @r1
            (case sameNat (Proxy @n1) (Proxy @n2) of
               Just Refl -> case testEquality (typeRep @r1) (typeRep @r2) of
                 Just Refl ->
                   DynamicRanked $ RepN
                   $ i2 - Nested.rreplicateScal (Nested.rshape i2)
                                                (realToFrac gamma)
                          * r2
                 _ -> error "updateWithGradient: scalar mismatch"
               _ -> error "updateWithGradient: rank mismatch")
          i
        ( DynamicShaped @r1 @sh1 (RepN i2)
         ,DynamicShaped @r2 @sh2 (RepN r2) ) ->
          ifDifferentiable @r1
            (case sameShape @sh1 @sh2 of
               Just Refl -> case testEquality (typeRep @r1) (typeRep @r2) of
                 Just Refl ->
                   DynamicShaped $ RepN
                   $ i2 - Nested.sreplicateScal (Nested.sshape i2)
                                                (realToFrac gamma)
                          * r2
                 _ -> error "updateWithGradient: scalar mismatch"
               _ -> error "updateWithGradient: shape mismatch")
          i
        _ -> i   -- eval didn't update the gradient, save on computation
  in V.zipWith updateR params gradient

{-
gradientIsNil :: (Eq r) => HVector RepN -> Bool
gradientIsNil (HVector RepN gradient0 gradientR) =
  V.all (== 0) gradient0
  && V.all isTensorDummyD gradientR

minimumGradient :: (Ord r) => HVector RepN -> r
minimumGradient (HVector RepN gradient0 gradientR) =
  min (if V.null gradient0 then 0 else LA.minElement gradient0)
      (if V.null gradientR then 0
       else V.minimum (V.map OR.minimumA gradientR))

maximumGradient :: (Ord r) => HVector RepN -> r
maximumGradient (HVector RepN gradient0 gradientR) =
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
  Triplify (TKScalar r) =
    TKProduct (TKProduct (TKScalar r) (TKScalar r)) (TKScalar r)
  Triplify (TKR n r) = TKProduct (TKProduct (TKR n r) (TKR n r)) (TKR n r)
  Triplify (TKS sh r) = TKProduct (TKProduct (TKS sh r) (TKS sh r)) (TKS sh r)
  Triplify (TKX sh r) = TKProduct (TKProduct (TKX sh r) (TKX sh r)) (TKX sh r)
  Triplify (TKProduct x z) = TKProduct (Triplify x) (Triplify z)
  Triplify TKUntyped = TKUntyped  -- this it not tripled

unzip3Rep
  :: STensorKindType y -> RepN (Triplify y)
  -> (RepN y, RepN y, RepN y)
unzip3Rep stk (RepN t) = case stk of
  STKScalar{} -> (RepN $ fst $ fst t, RepN $ snd $ fst t, RepN $ snd t)
  STKR _ STKScalar{} -> (RepN $ fst $ fst t, RepN $ snd $ fst t, RepN $ snd t)
  STKS _ STKScalar{} -> (RepN $ fst $ fst t, RepN $ snd $ fst t, RepN $ snd t)
  STKX _ STKScalar{} -> (RepN $ fst $ fst t, RepN $ snd $ fst t, RepN $ snd t)
  STKProduct stk1 stk2 -> let (a1, b1, c1) = unzip3Rep stk1 $ RepN $ fst t
                              (a2, b2, c2) = unzip3Rep stk2 $ RepN $ snd t
                          in (RepN (unRepN a1, unRepN a2), RepN (unRepN b1, unRepN b2), RepN (unRepN c1, unRepN c2))
  STKUntyped -> (RepN t, RepN t, RepN t)  -- TODO: incorrect?
  _ -> error "TODO"

type role StateAdamDeep nominal
data StateAdamDeep y = StateAdamDeep
  { tAdamDeep :: Int  -- iteration count
  , mAdamDeep :: RepN y
  , vAdamDeep :: RepN y
  }

initialStateAdamDeep :: FullTensorKind y -> StateAdamDeep y
initialStateAdamDeep ftk =
  StateAdamDeep { tAdamDeep = 0
                , mAdamDeep = repDeepZero ftk
                , vAdamDeep = repDeepZero ftk
                }

-- TODO: introduce and use dummies
repDeepZero :: FullTensorKind y -> RepN y
repDeepZero = \case
  FTKScalar -> RepN $ RepScalar $ Nested.rreplicateScal ZSR 0
  FTKR sh FTKScalar -> RepN $ Nested.rreplicateScal sh 0
  FTKS sh FTKScalar -> RepN $ Nested.sreplicateScal sh 0
  FTKX sh FTKScalar -> RepN $ Nested.mreplicateScal sh 0
  FTKProduct ftk1 ftk2 -> RepN (unRepN $ repDeepZero ftk1, unRepN $ repDeepZero ftk2)
  FTKUntyped{} -> error "repDeepZero: FTKUntyped"
  _ -> error "TODO"

updateWithGradientAdamDeep
  :: TensorKind y
  => ArgsAdam -> StateAdamDeep y -> RepN y -> RepN (ADTensorKind y)
  -> (RepN y, StateAdamDeep y)
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
                 -> RepN y2 -> RepN y2
                 -> RepN y2 -> RepN (ADTensorKind y2)
                 -> RepN (Triplify y2)
      updateProd stk (RepN mA) (RepN vA) (RepN p) (RepN g)
       | Dict <- lemTensorKindOfAD stk = case stk of
        STKScalar @r _ ->
          case sameTensorKind @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let (mAN, vAN, pN) =
                       updateR (unRepScalar mA)
                               (unRepScalar vA)
                               (unRepScalar p)
                               (unRepScalar g)
                 in RepN
                    (( RepScalar mAN
                     , RepScalar vAN )
                    , RepScalar pN ))
                (RepN ((mA, vA), p))
            _ -> RepN ((mA, vA), p)
        STKR SNat (STKScalar @r _) ->
          case sameTensorKind @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let (mAN, vAN, pN) = updateR mA vA p g
                 in RepN ((mAN, vAN), pN))
                (RepN ((mA, vA), p))
            _ -> RepN ((mA, vA), p)
        STKS sh (STKScalar @r _) -> withKnownShS sh $
          case sameTensorKind @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let (mAN, vAN, pN) =
                       updateR (Nested.stoRanked mA)
                               (Nested.stoRanked vA)
                               (Nested.stoRanked p)
                               (Nested.stoRanked g)
                 in RepN
                    ( ( Nested.rcastToShaped mAN knownShS
                      , Nested.rcastToShaped vAN knownShS )
                    , Nested.rcastToShaped pN knownShS ))
                (RepN ((mA, vA), p))
            _ -> RepN ((mA, vA), p)
        STKX sh (STKScalar @r _) -> withKnownShX sh $
          case sameTensorKind @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let (mAN, vAN, pN) =
                       updateR (Nested.mtoRanked mA)
                               (Nested.mtoRanked vA)
                               (Nested.mtoRanked p)
                               (Nested.mtoRanked g)
                 in RepN
                    ( ( Nested.mreshape (Nested.mshape mA)
                        $ Nested.rtoMixed mAN
                      , Nested.mreshape (Nested.mshape vA)
                        $ Nested.rtoMixed vAN )
                    , Nested.mreshape (Nested.mshape p)
                      $ Nested.rtoMixed pN ))
                (RepN ((mA, vA), p))
            _ -> RepN ((mA, vA), p)
        STKProduct stk1 stk2 ->
          RepN
            ( unRepN $ updateProd stk1 (RepN $ fst mA) (RepN $ fst vA) (RepN $ fst p) (RepN $ fst g)
            , unRepN $ updateProd stk2 (RepN $ snd mA) (RepN $ snd vA) (RepN $ snd p) (RepN $ snd g) )
        STKUntyped -> error "updateProd: STKUntyped"
        _ -> error "TODO"
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
  , mAdam :: HVector RepN
  , vAdam :: HVector RepN
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
  :: ArgsAdam -> StateAdam -> HVector RepN -> HVector RepN
  -> (HVector RepN, StateAdam)
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
      updateD :: DynamicTensor RepN -> DynamicTensor RepN
              -> DynamicTensor RepN -> DynamicTensor RepN
              -> ( DynamicTensor RepN
                 , DynamicTensor RepN
                 , DynamicTensor RepN )
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
               let (od1, od2, od3) = updateR (unRepN mA) (unRepN vA)
                                             (unRepN p) (unRepN g)
               in ( DynamicRanked $ RepN od1
                  , DynamicRanked $ RepN od2
                  , DynamicRanked $ RepN od3 )
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
