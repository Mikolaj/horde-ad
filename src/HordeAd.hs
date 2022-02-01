-- | An API of the library that should be sufficient for general use.
-- To (ab)use implementation details or to access ready tools for specific
-- applications, such as fully connect neural networks operating on MNIST
-- data, some extra imports may be needed not covered here.
module HordeAd
  ( module HordeAd.DualNumber
  , module HordeAd.Engine
  , module HordeAd.PairOfVectors
  ) where

import Prelude ()

import HordeAd.DualNumber
import HordeAd.Engine
import HordeAd.PairOfVectors
