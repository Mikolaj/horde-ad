module MnistCnnRanked2 where

import Prelude

import Data.Vector.Generic qualified as V
import Data.Vector.Storable (Vector)
import GHC.TypeLits (type (*), type (+), type Div)
import Numeric.LinearAlgebra (Numeric)

import Data.Array.Nested qualified as Nested

import HordeAd.Core.Adaptor
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import HordeAd.Internal.BackendOX (RepN (..))
import HordeAd.Internal.OrthotopeOrphanInstances (FlipR (..))
import HordeAd.Util.SizedList
import MnistData

type ADCnnMnistParametersShaped (target :: Target) r =
  target (TKS r '[1, 1, 2, 2])

type ADCnnMnistParameters (target :: Target) r =
  target (TKR r 4)

convMnistTwoR
  :: (ADReady target, GoodScalar r)
  => PrimalOf target (TKR r 4)  -- [batch_size, 1, SizeMnistHeight, SizeMnistWidth]
  -> ADCnnMnistParameters target r
  -> target (TKR r 2)  -- [SizeMnistLabel, batch_size]
convMnistTwoR input ker1 =
  let t1 = maxPool2dUnpadded 2 2 $ conv2dUnpadded ker1 (rfromPrimal input)
  in rreshape (1 :$: 1 :$: ZSR) t1
