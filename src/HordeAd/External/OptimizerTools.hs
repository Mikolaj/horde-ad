-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient
--  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), initialStateAdam
  , updateWithGradientAdam
  ) where

import Prelude

import Data.Type.Equality ((:~:) (Refl))
import Type.Reflection (typeRep)

import Data.Array.Mixed.Shape (withKnownShX)
import Data.Array.Nested (KnownShS (..))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (withKnownShS)

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Ops
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.Core.Unwind

updateWithGradient :: forall y. KnownSTK y
                   => Double -> RepN y -> RepN (ADTensorKind y) -> RepN y
updateWithGradient gamma p@(RepN params) g@(RepN gradient) = case knownSTK @y of
  STKScalar @r _ -> RepN $
    case sameSTK (knownSTK @y) (STKScalar @Z0 typeRep) of
      Just Refl -> params
      _ -> error "TODO: unexpected"
           $ case sameSTK (knownSTK @y) (adSTK $ knownSTK @y) of
        Just Refl ->
          ifDifferentiable @r
            (params - realToFrac gamma * gradient)
            params
        Nothing -> params
  STKR SNat (STKScalar @r _) -> RepN $
    case sameSTK (knownSTK @y) (adSTK $ knownSTK @y) of
      Just Refl ->
        ifDifferentiable @r
          (params - Nested.rreplicateScal (Nested.rshape params)
                                          (realToFrac gamma)
                    * gradient)
          params
      Nothing -> params
  STKS sh (STKScalar @r _) -> withKnownShS sh $ RepN $
    case sameSTK (knownSTK @y) (adSTK $ knownSTK @y) of
      Just Refl ->
        ifDifferentiable @r
          (params - Nested.sreplicateScal (Nested.sshape params)
                                          (realToFrac gamma)
                    * gradient)
          params
      Nothing -> params
  STKProduct stk1 stk2 | Dict <- lemKnownSTK stk1
                       , Dict <- lemKnownSTKOfAD stk1
                       , Dict <- lemKnownSTK stk2
                       , Dict <- lemKnownSTKOfAD stk2 ->
    tpair (updateWithGradient gamma (tproject1 p) (tproject1 g))
          (updateWithGradient gamma (tproject2 p) (tproject2 g))
  _ -> error "updateWithGradient: TODO"

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

unzip3Rep
  :: STensorKind y -> RepN (Triplify y)
  -> (RepN y, RepN y, RepN y)
unzip3Rep stk (RepN t) = case stk of
  STKScalar{} -> (RepN $ fst $ fst t, RepN $ snd $ fst t, RepN $ snd t)
  STKR _ STKScalar{} -> (RepN $ fst $ fst t, RepN $ snd $ fst t, RepN $ snd t)
  STKS _ STKScalar{} -> (RepN $ fst $ fst t, RepN $ snd $ fst t, RepN $ snd t)
  STKX _ STKScalar{} -> (RepN $ fst $ fst t, RepN $ snd $ fst t, RepN $ snd t)
  STKProduct stk1 stk2 -> let !(!a1, !b1, !c1) = unzip3Rep stk1 $ RepN $ fst t
                              !(!a2, !b2, !c2) = unzip3Rep stk2 $ RepN $ snd t
                          in ( RepN (unRepN a1, unRepN a2)
                             , RepN (unRepN b1, unRepN b2)
                             , RepN (unRepN c1, unRepN c2))
  _ -> error "TODO"

type role StateAdam nominal
data StateAdam y = StateAdam
  { tAdam :: Int  -- iteration count
  , mAdam :: RepN y
  , vAdam :: RepN y
  }

-- TODO: introduce and use something like TensorOrZero
initialStateAdam :: FullTensorKind y -> StateAdam y
initialStateAdam ftk =
  StateAdam { tAdam = 0
                , mAdam = constantTarget 0 ftk
                , vAdam = constantTarget 0 ftk
                }

updateWithGradientAdam
  :: KnownSTK y
  => ArgsAdam -> StateAdam y -> RepN y -> RepN (ADTensorKind y)
  -> (RepN y, StateAdam y)
updateWithGradientAdam ArgsAdam{..} StateAdam{..} paramsR gradientR =
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
      updateProd :: forall y2.
                    STensorKind y2
                 -> RepN y2 -> RepN y2
                 -> RepN y2 -> RepN (ADTensorKind y2)
                 -> RepN (Triplify y2)
      updateProd stk (RepN mA) (RepN vA) (RepN p) (RepN g)
       | Dict <- lemKnownSTKOfAD stk = case stk of
        STKScalar @r _ ->
          case sameKnownSTS @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let !(!mAN, !vAN, !pN) =
                       updateR (Nested.rscalar mA)
                               (Nested.rscalar vA)
                               (Nested.rscalar p)
                               (Nested.rscalar g)
                 in RepN
                    (( Nested.runScalar mAN
                     , Nested.runScalar vAN )
                    , Nested.runScalar pN ))
                (RepN ((mA, vA), p))
            _ -> RepN ((mA, vA), p)
        STKR SNat (STKScalar @r _) ->
          case sameKnownSTS @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let !(!mAN, !vAN, !pN) = updateR mA vA p g
                 in RepN ((mAN, vAN), pN))
                (RepN ((mA, vA), p))
            _ -> RepN ((mA, vA), p)
        STKS sh (STKScalar @r _) -> withKnownShS sh $
          case sameKnownSTS @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let !(!mAN, !vAN, !pN) =
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
          case sameKnownSTS @y2 @(ADTensorKind y2) of
            Just Refl ->
              ifDifferentiable @r
                (let !(!mAN, !vAN, !pN) =
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
          let !a1 = unRepN $ updateProd stk1
                (RepN $ fst mA) (RepN $ fst vA) (RepN $ fst p) (RepN $ fst g)
              !a2 = unRepN $ updateProd stk2
                (RepN $ snd mA) (RepN $ snd vA) (RepN $ snd p) (RepN $ snd g)
          in RepN (a1, a2)
        _ -> error "TODO"
      (!mAdamRNew, !vAdamRNew, !paramsRNew) =
        unzip3Rep knownSTK
        $ updateProd knownSTK mAdamR vAdamR paramsR gradientR
  in ( paramsRNew
     , StateAdam
         { tAdam = tAdamNew
         , mAdam = mAdamRNew
         , vAdam = vAdamRNew
         }
     )
