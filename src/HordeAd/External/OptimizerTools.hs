{-# LANGUAGE TypeFamilies #-}
-- | Tools for implementing (and debugging the use of) gradient descent schemes.
module HordeAd.External.OptimizerTools
  ( updateWithGradient
  , gradientIsNil, minimumGradient, maximumGradient
  , ArgsAdam(..), defaultArgsAdam
  , StateAdam(..), initialStateAdam
  , liftMatrix43, updateWithGradientAdam
  ) where

import Prelude

import           Control.Monad.ST.Strict (runST)
import qualified Data.Array.DynamicS as OT
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import           Numeric.LinearAlgebra (Element, Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           Numeric.LinearAlgebra.Data (flatten)
import           Numeric.LinearAlgebra.Devel
  (MatrixOrder (..), liftMatrix, liftMatrix2, matrixFromVector, orderOf)

import HordeAd.Internal.Delta (Domains (..))
import HordeAd.Internal.OrthotopeOrphanInstances (liftVT2)
import HordeAd.Internal.TensorOps (isTensorDummy)

updateWithGradient :: (Numeric r, Floating (Vector r))
                   => r -> Domains r -> Domains r -> Domains r
updateWithGradient gamma (Domains params0 params1 params2 paramsX)
                         (Domains gradient0 gradient1 gradient2 gradientX) =
  let updateVector i r = i - LA.scale gamma r
      !params0New = updateVector params0 gradient0
      update1 i r = if V.null r  -- eval didn't update it, would crash
                    then i
                    else updateVector i r
      !params1New = V.zipWith update1 params1 gradient1
      update2 i r = if LA.rows r <= 0  -- eval didn't update it, would crash
                    then i
                    else liftMatrix2 updateVector i r
      !params2New = V.zipWith update2 params2 gradient2
      updateX i r = if isTensorDummy r  -- eval didn't update it, would crash
                    then i
                    else liftVT2 updateVector i r
      !paramsXNew = V.zipWith updateX paramsX gradientX
  in Domains params0New params1New params2New paramsXNew
{-# SPECIALIZE updateWithGradient :: Double -> Domains Double -> Domains Double -> Domains Double #-}

gradientIsNil :: (Eq r, Numeric r) => Domains r -> Bool
gradientIsNil (Domains gradient0 gradient1 gradient2 gradientX) =
  V.all (== 0) gradient0
  && V.all V.null gradient1
  && V.all (\r -> LA.rows r <= 0) gradient2
  && V.all isTensorDummy gradientX

minimumGradient :: (Ord r, Numeric r) => Domains r -> r
minimumGradient (Domains gradient0 gradient1 gradient2 gradientX) =
  min (if V.null gradient0 then 0 else LA.minElement gradient0)
      (min (if V.null gradient1 then 0
            else V.minimum (V.map LA.minElement gradient1))
           (min (if V.null gradient2 then 0
                 else V.minimum (V.map LA.minElement gradient2))
                (if V.null gradientX then 0
                 else V.minimum (V.map OT.minimumA gradientX))))

maximumGradient :: (Ord r, Numeric r) => Domains r -> r
maximumGradient (Domains gradient0 gradient1 gradient2 gradientX) =
  max (if V.null gradient0 then 0 else LA.maxElement gradient0)
      (max (if V.null gradient1 then 0
            else V.maximum (V.map LA.maxElement gradient1))
           (max (if V.null gradient2 then 0
                 else V.maximum (V.map LA.maxElement gradient2))
                (if V.null gradientX then 0
                 else V.maximum (V.map OT.maximumA gradientX))))

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
zeroParameters :: Numeric r
               => Domains r -> Domains r
zeroParameters Domains{..} =
  let zeroVector v = runST $ do
        vThawed <- V.thaw v
        VM.set vThawed 0
        V.unsafeFreeze vThawed
  in Domains (zeroVector domains0)
             (V.map zeroVector domains1)
             (V.map (liftMatrix zeroVector) domains2)
             (V.map (\a -> OT.constant (OT.shapeL a) 0) domainsX)
                -- fast allright

initialStateAdam :: Numeric r
                 => Domains r -> StateAdam r
initialStateAdam parameters0 =
  let zeroP = zeroParameters parameters0
  in StateAdam
       { tAdam = 0
       , mAdam = zeroP
       , vAdam = zeroP
       }

-- | Application of a vector function on the flattened matrices elements.
liftMatrix43 :: ( Numeric a, Numeric b, Numeric c, Numeric d
                , Element x, Element y, Element z )
             => (Vector a -> Vector b -> Vector c -> Vector d
                 -> (Vector x, Vector y, Vector z))
             -> Matrix a -> Matrix b -> Matrix c -> Matrix d
             -> (Matrix x, Matrix y, Matrix z)
liftMatrix43 f m1 m2 m3 m4 =
  let sz@(r, c) = LA.size m1
      rowOrder = orderOf m1
        -- checking @m4@ (gradient) makes RNN LL test much faster and BB slower
        -- so this needs much more benchmarking and understading to tweak
  in if sz == LA.size m2 && sz == LA.size m3 && sz == LA.size m4
     then
       let (vx, vy, vz) = case rowOrder of
             RowMajor -> f (flatten m1) (flatten m2) (flatten m3) (flatten m4)
             ColumnMajor -> f (flatten (LA.tr' m1)) (flatten (LA.tr' m2))
                              (flatten (LA.tr' m3)) (flatten (LA.tr' m4))
       in ( matrixFromVector rowOrder r c vx
          , matrixFromVector rowOrder r c vy
          , matrixFromVector rowOrder r c vz
          )
     else error $ "nonconformant matrices in liftMatrix43: "
                  ++ show (LA.size m1, LA.size m2, LA.size m3, LA.size m4)

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
  :: forall r. (Numeric r, Floating r, Floating (Vector r))
  => ArgsAdam r -> StateAdam r -> Domains r -> Domains r
  -> (Domains r, StateAdam r)
updateWithGradientAdam ArgsAdam{..}
                       StateAdam{ tAdam
                                , mAdam = Domains mAdam0 mAdam1 mAdam2 mAdamX
                                , vAdam = Domains vAdam0 vAdam1 vAdam2 vAdamX
                                }
                       (Domains params0 params1 params2 paramsX)
                       (Domains gradient0 gradient1 gradient2 gradientX) =
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
      update1 mA vA p g = if V.null g  -- eval didn't update it, would crash
                          then (mA, vA, p)
                          else updateVector mA vA p g
      (!mAdam1New, !vAdam1New, !params1New) =
        V.unzip3 $ V.zipWith4 update1 mAdam1 vAdam1 params1 gradient1
      update2 mA vA p g = if LA.rows g <= 0  -- eval didn't update it; crash
                          then (mA, vA, p)
                          else liftMatrix43 updateVector mA vA p g
      (!mAdam2New, !vAdam2New, !params2New) =
        V.unzip3 $ V.zipWith4 update2 mAdam2 vAdam2 params2 gradient2
      updateX mA vA p g = if isTensorDummy g  -- eval didn't update it
                          then (mA, vA, p)
                          else liftArray43 updateVector mA vA p g
      (!mAdamXNew, !vAdamXNew, !paramsXNew) =
        V.unzip3 $ V.zipWith4 updateX mAdamX vAdamX paramsX gradientX
  in ( Domains params0New params1New params2New paramsXNew
     , StateAdam { tAdam = tAdamNew
                 , mAdam = Domains mAdam0New mAdam1New mAdam2New mAdamXNew
                 , vAdam = Domains vAdam0New vAdam1New vAdam2New vAdamXNew
                 }
     )
