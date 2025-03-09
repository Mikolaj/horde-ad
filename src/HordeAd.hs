-- | An API of the library that should be sufficient for general use.
-- To (ab)use implementation details or to access ready tools for specific
-- applications, such as fully connect neural networks operating on MNIST
-- data, some extra imports may be needed that are not covered here.
module HordeAd
  ( -- * The main array API
    module HordeAd.OpsTensor
  , module HordeAd.Core.ConvertTensor
    -- * The main AD API
  , module HordeAd.Core.Engine
    -- * Additional support types and operations
  , module HordeAd.Core.Ast
  , module HordeAd.Core.AstInline
  , module HordeAd.Core.AstPrettyPrint
  , module HordeAd.Core.CarriersADVal
  , module HordeAd.Core.CarriersConcrete
  , module HordeAd.Core.TensorKind
  , module HordeAd.Core.Types
  , module HordeAd.External.CommonRankedOps
  , module HordeAd.External.CommonShapedOps
  , module HordeAd.External.Optimizer
  ) where

import Prelude ()

import HordeAd.Core.Ast
import HordeAd.Core.AstInline
import HordeAd.Core.AstPrettyPrint
import HordeAd.Core.CarriersADVal
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Engine
import HordeAd.Core.TensorKind
import HordeAd.Core.Types
import HordeAd.External.CommonRankedOps
import HordeAd.External.CommonShapedOps
import HordeAd.External.Optimizer
import HordeAd.OpsTensor
