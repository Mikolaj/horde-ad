-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient
--  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), initialStateAdam
  , updateWithGradientAdam
  ) where

import Prelude

import Data.Type.Equality (gcastWith, (:~:))

import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested qualified as Nested

import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Ops
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

updateWithGradient :: forall y.
                      Double -> SingletonTK y -> Concrete y -> Concrete (ADTensorKind y)
                   -> Concrete y
updateWithGradient gamma stk p@(Concrete params) g@(Concrete gradient) = case stk of
  STKScalar @r -> Concrete $
    ifDifferentiable @r
      (gcastWith (unsafeCoerceRefl :: y :~: ADTensorKind y) $
       params - realToFrac gamma * gradient)
      params
  STKR _ (STKScalar @r) -> Concrete $
    ifDifferentiable @r
      (gcastWith (unsafeCoerceRefl :: y :~: ADTensorKind y) $
       params - Nested.rreplicateScal (Nested.rshape params)
                                      (realToFrac gamma)
                * gradient)
      params
  STKS _ (STKScalar @r) -> Concrete $
    ifDifferentiable @r
      (gcastWith (unsafeCoerceRefl :: y :~: ADTensorKind y) $
       params - Nested.sreplicateScal (Nested.sshape params)
                                      (realToFrac gamma)
                * gradient)
      params
{- TODO
  STKR _ x -> Concrete $
    case sameSTK x (adSTK x) of
      Just Refl ->
        (params - Nested.rreplicateScal (Nested.rshape params)
                                        (realToFrac gamma)
                  * gradient)
      Nothing -> params
  STKS _ x -> Concrete $
    case sameSTK x (adSTK x) of
      Just Refl ->
        (params - Nested.sreplicateScal (Nested.sshape params)
                                        (realToFrac gamma)
                  * gradient)
      Nothing -> params
-}
  STKProduct stk1 stk2 ->
    tpair (updateWithGradient gamma stk1 (tproject1 p) (tproject1 g))
          (updateWithGradient gamma stk2 (tproject2 p) (tproject2 g))
  _ -> error "updateWithGradient: TODO"

{-
gradientIsNil :: (Eq r) => HVector Concrete -> Bool
gradientIsNil (HVector Concrete gradient0 gradientR) =
  V.all (== 0) gradient0
  && V.all isTensorDummyD gradientR

minimumGradient :: (Ord r) => HVector Concrete -> r
minimumGradient (HVector Concrete gradient0 gradientR) =
  min (if V.null gradient0 then 0 else LA.minElement gradient0)
      (if V.null gradientR then 0
       else V.minimum (V.map OR.minimumA gradientR))

maximumGradient :: (Ord r) => HVector Concrete -> r
maximumGradient (HVector Concrete gradient0 gradientR) =
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
  :: SingletonTK y -> Concrete (Triplify y)
  -> (Concrete y, Concrete y, Concrete y)
unzip3Rep stk (Concrete t) = case stk of
  STKScalar -> (Concrete $ fst $ fst t, Concrete $ snd $ fst t, Concrete $ snd t)
  STKR _ STKScalar -> (Concrete $ fst $ fst t, Concrete $ snd $ fst t, Concrete $ snd t)
  STKS _ STKScalar -> (Concrete $ fst $ fst t, Concrete $ snd $ fst t, Concrete $ snd t)
  STKX _ STKScalar -> (Concrete $ fst $ fst t, Concrete $ snd $ fst t, Concrete $ snd t)
  STKProduct stk1 stk2 -> let !(!a1, !b1, !c1) = unzip3Rep stk1 $ Concrete $ fst t
                              !(!a2, !b2, !c2) = unzip3Rep stk2 $ Concrete $ snd t
                          in ( Concrete (unConcrete a1, unConcrete a2)
                             , Concrete (unConcrete b1, unConcrete b2)
                             , Concrete (unConcrete c1, unConcrete c2))
  _ -> error "TODO"

type role StateAdam nominal
data StateAdam y = StateAdam
  { tAdam :: Int  -- iteration count
  , mAdam :: Concrete y
  , vAdam :: Concrete y
  }

-- TODO: introduce and use something like TensorOrZero
initialStateAdam :: FullShapeTK y -> StateAdam y
initialStateAdam ftk =
  StateAdam { tAdam = 0
            , mAdam = tconstantTarget 0 ftk
            , vAdam = tconstantTarget 0 ftk
            }

updateWithGradientAdam
  :: ArgsAdam -> StateAdam y -> SingletonTK y -> Concrete y -> Concrete (ADTensorKind y)
  -> (Concrete y, StateAdam y)
updateWithGradientAdam ArgsAdam{..} StateAdam{..} stk0 paramsR gradientR =
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
                    SingletonTK y2
                 -> Concrete y2 -> Concrete y2
                 -> Concrete y2 -> Concrete (ADTensorKind y2)
                 -> Concrete (Triplify y2)
      updateProd stk (Concrete mA) (Concrete vA) (Concrete p) (Concrete g) = case stk of
        -- TODO: short-circuit like in updateWithGradient
        STKScalar @r ->
          ifDifferentiable @r
            (gcastWith (unsafeCoerceRefl :: y2 :~: ADTensorKind y2) $
             let !(!mAN, !vAN, !pN) =
                   updateR (Nested.rscalar mA)
                           (Nested.rscalar vA)
                           (Nested.rscalar p)
                           (Nested.rscalar g)
             in Concrete
                (( Nested.runScalar mAN
                 , Nested.runScalar vAN )
                , Nested.runScalar pN ))
            (Concrete ((mA, vA), p))
        STKR SNat (STKScalar @r) ->
          ifDifferentiable @r
            (gcastWith (unsafeCoerceRefl :: y2 :~: ADTensorKind y2) $
             let !(!mAN, !vAN, !pN) = updateR mA vA p g
             in Concrete ((mAN, vAN), pN))
            (Concrete ((mA, vA), p))
        STKS sh (STKScalar @r) ->
          ifDifferentiable @r
            (gcastWith (unsafeCoerceRefl :: y2 :~: ADTensorKind y2) $
             let !(!mAN, !vAN, !pN) =
                   updateR (Nested.stoRanked mA)
                           (Nested.stoRanked vA)
                           (Nested.stoRanked p)
                           (Nested.stoRanked g)
             in Concrete
                ( ( Nested.rcastToShaped mAN sh
                  , Nested.rcastToShaped vAN sh )
                , Nested.rcastToShaped pN sh ))
            (Concrete ((mA, vA), p))
        STKX _ (STKScalar @r) ->
          ifDifferentiable @r
            (gcastWith (unsafeCoerceRefl :: y2 :~: ADTensorKind y2) $
             let !(!mAN, !vAN, !pN) =
                   updateR (Nested.mtoRanked mA)
                           (Nested.mtoRanked vA)
                           (Nested.mtoRanked p)
                           (Nested.mtoRanked g)
             in Concrete
                ( ( Nested.mreshape (Nested.mshape mA)
                    $ Nested.rtoMixed mAN
                  , Nested.mreshape (Nested.mshape vA)
                    $ Nested.rtoMixed vAN )
                , Nested.mreshape (Nested.mshape p)
                  $ Nested.rtoMixed pN ))
            (Concrete ((mA, vA), p))
{- TODO
        STKR SNat (STKScalar @r) ->
          case sameSTK stk (adSTK stk) of
            Just Refl ->
              ifDifferentiable @r
                (let !(!mAN, !vAN, !pN) = updateR mA vA p g
                 in Concrete ((mAN, vAN), pN))
                (Concrete ((mA, vA), p))
            _ -> Concrete ((mA, vA), p)
        STKS sh (STKScalar @r) ->
          case sameSTK stk (adSTK stk) of
            Just Refl ->
              ifDifferentiable @r
                (let !(!mAN, !vAN, !pN) =
                       updateR (Nested.stoRanked mA)
                               (Nested.stoRanked vA)
                               (Nested.stoRanked p)
                               (Nested.stoRanked g)
                 in Concrete
                    ( ( Nested.rcastToShaped mAN sh
                      , Nested.rcastToShaped vAN sh )
                    , Nested.rcastToShaped pN sh ))
                (Concrete ((mA, vA), p))
            _ -> Concrete ((mA, vA), p)
        STKX _ (STKScalar @r) ->
          case sameSTK stk (adSTK stk) of
            Just Refl ->
              ifDifferentiable @r
                (let !(!mAN, !vAN, !pN) =
                       updateR (Nested.mtoRanked mA)
                               (Nested.mtoRanked vA)
                               (Nested.mtoRanked p)
                               (Nested.mtoRanked g)
                 in Concrete
                    ( ( Nested.mreshape (Nested.mshape mA)
                        $ Nested.rtoMixed mAN
                      , Nested.mreshape (Nested.mshape vA)
                        $ Nested.rtoMixed vAN )
                    , Nested.mreshape (Nested.mshape p)
                      $ Nested.rtoMixed pN ))
                (Concrete ((mA, vA), p))
            _ -> Concrete ((mA, vA), p)
-}
        STKProduct stk1 stk2 ->
          let !a1 = unConcrete $ updateProd stk1
                (Concrete $ fst mA) (Concrete $ fst vA) (Concrete $ fst p) (Concrete $ fst g)
              !a2 = unConcrete $ updateProd stk2
                (Concrete $ snd mA) (Concrete $ snd vA) (Concrete $ snd p) (Concrete $ snd g)
          in Concrete (a1, a2)
        _ -> error "TODO"
      (!mAdamRNew, !vAdamRNew, !paramsRNew) =
        unzip3Rep stk0 $ updateProd stk0 mAdamR vAdamR paramsR gradientR
  in ( paramsRNew
     , StateAdam
         { tAdam = tAdamNew
         , mAdam = mAdamRNew
         , vAdam = vAdamRNew
         }
     )
