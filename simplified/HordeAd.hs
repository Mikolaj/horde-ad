-- | An API of the library that should be sufficient for general use.
-- To (ab)use implementation details or to access ready tools for specific
-- applications, such as fully connect neural networks operating on MNIST
-- data, some extra imports may be needed not covered here.
module HordeAd
  ( module HordeAd.Core.Ast
  , module HordeAd.Core.AstInterpret
  , module HordeAd.Core.DualNumber
  , module HordeAd.Core.Engine
  , module HordeAd.Core.SizedIndex
  , module HordeAd.Core.TensorADVal
  , module HordeAd.Core.TensorClass
  , module HordeAd.External.CommonRankedOps
  , module HordeAd.External.Optimizer
  ) where

import Prelude ()

import HordeAd.Core.Ast
import HordeAd.Core.AstInterpret
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass
import HordeAd.External.CommonRankedOps
import HordeAd.External.Optimizer
