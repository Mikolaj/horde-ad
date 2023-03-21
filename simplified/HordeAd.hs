-- | An API of the library that should be sufficient for general use.
-- To (ab)use implementation details or to access ready tools for specific
-- applications, such as fully connect neural networks operating on MNIST
-- data, some extra imports may be needed not covered here.
module HordeAd
  ( module HordeAd.Core.Ast
  , module HordeAd.Core.AstInterpret
  , module HordeAd.Core.DualNumber2
  , module HordeAd.Core.Engine
  , module HordeAd.Core.SizedIndex
  , module HordeAd.Core.TensorClass
  , module HordeAd.External.Adaptor
  , module HordeAd.External.Optimizer
  ) where

import Prelude ()

import HordeAd.Core.Ast
import HordeAd.Core.AstInterpret
import HordeAd.Core.DualNumber2
import HordeAd.Core.Engine hiding (ADInputs, revOnADInputs, revOnDomains)
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.External.Adaptor
import HordeAd.External.Optimizer
