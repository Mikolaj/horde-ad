-- | An API of the horde-ad library that should be sufficient for general use.
-- To (ab)use implementation details or to access ready tools for specific
-- applications, such as neural networks operating on MNIST data,
-- extra imports may be needed that are not covered here.
module HordeAd
  ( -- * The main array API
    module HordeAd.OpsTensor
  , module HordeAd.OpsTensorRanked
  , module HordeAd.OpsTensorShaped
  , module HordeAd.OpsTensorMixed
  , module HordeAd.Core.ConvertTensor
    -- * The main AD API
  , module HordeAd.ADEngine
  , module HordeAd.AstEngine
    -- * Additional support types and operations
  , module HordeAd.Core.Ast
  , module HordeAd.Core.CarriersADVal
  , module HordeAd.Core.CarriersConcrete
  , module HordeAd.Core.TensorKind
  , module HordeAd.Core.Types
  , module HordeAd.External.CommonRankedOps
  , module HordeAd.External.CommonShapedOps
  , module HordeAd.External.Optimizer
  , Boolean (..)
  ) where

import Prelude ()

import Data.Boolean (Boolean (..))
import HordeAd.ADEngine
import HordeAd.AstEngine
import HordeAd.Core.Ast
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import HordeAd.External.CommonShapedOps
import HordeAd.External.Optimizer
import HordeAd.OpsTensor
import HordeAd.OpsTensorMixed
import HordeAd.OpsTensorRanked
import HordeAd.OpsTensorShaped
