-- | A subset of the API of the horde-ad library that should be
-- sufficient for general use.
-- To (ab)use implementation details or to access ready tools for specific
-- applications, such as neural networks operating on MNIST data,
-- you may need some extra imports not covered here.
--
-- If you are interested mainly in using multi-dimensional arrays,
-- start with "HordeAd.OpsTensor" (or use directly
-- https://hackage.haskell.org/package/ox-arrays
-- that doesn't have the capability nor the overhead of term rewriting
-- over the symbolic represenation of array operations).
-- For Automatic Differentiation, start with "HordeAd.ADEngine".
module HordeAd
  ( -- * The main array API
    module HordeAd.OpsTensor
  , module HordeAd.OpsTensorRanked
  , module HordeAd.OpsTensorShaped
  , module HordeAd.OpsTensorMixed
  , module HordeAd.Core.ConvertTensor
    -- * The main AD API
  , module HordeAd.ADEngine
  , module HordeAd.Core.AstEngine
  , module HordeAd.Core.PPEngine
    -- * Additional support types and operations
  , module HordeAd.Core.Ast
  , module HordeAd.Core.CarriersADVal
  , module HordeAd.Core.CarriersConcrete
  , module HordeAd.Core.TensorKind
  , module HordeAd.Core.Types
  , module HordeAd.External.CommonRankedOps
  , module HordeAd.External.CommonShapedOps
  , module HordeAd.External.Optimizer
  ) where

import Prelude ()

import HordeAd.ADEngine
import HordeAd.Core.Ast
import HordeAd.Core.AstEngine
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.PPEngine
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import HordeAd.External.CommonShapedOps
import HordeAd.External.Optimizer
import HordeAd.OpsTensor
import HordeAd.OpsTensorMixed
import HordeAd.OpsTensorRanked
import HordeAd.OpsTensorShaped
