-- | An API of the library that should be sufficient for general use.
-- To (ab)use implementation details or to access ready tools for specific
-- applications, such as fully connect neural networks operating on MNIST
-- data, some extra imports may be needed not covered here.
module HordeAd
  ( module HordeAd.Core.ADValTensor
  , module HordeAd.Core.Ast
  , module HordeAd.Core.DualNumber2
  , module HordeAd.Core.Engine2
  , module HordeAd.Core.PairOfVectors
  , module HordeAd.Core.SizedIndex
  , module HordeAd.Core.TensorClass
  , module HordeAd.External.Adaptor2
  , module HordeAd.External.Optimizer
  ) where

import Prelude ()

import HordeAd.Core.ADValTensor
import HordeAd.Core.Ast
import HordeAd.Core.DualNumber2
import HordeAd.Core.Engine2
import HordeAd.Core.PairOfVectors
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor2
import HordeAd.External.Optimizer
