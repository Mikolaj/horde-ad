-- | An API of the library that should be sufficient for general use.
-- To (ab)use implementation details or to access ready tools for specific
-- applications, such as fully connect neural networks operating on MNIST
-- data, some extra imports may be needed not covered here.
module HordeAd
  ( module HordeAd.Core.Delta
  , module HordeAd.Core.DualNumber
  , module HordeAd.Core.Engine
  , module HordeAd.Core.HasDual
  , module HordeAd.Core.Optimizer
  , module HordeAd.Core.PairOfVectors
 ) where

import Prelude ()

import HordeAd.Core.Delta (Delta0)
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.HasDual
import HordeAd.Core.Optimizer
import HordeAd.Core.PairOfVectors
