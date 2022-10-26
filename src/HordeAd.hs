{-# LANGUAGE CPP #-}
-- | An API of the library that should be sufficient for general use.
-- To (ab)use implementation details or to access ready tools for specific
-- applications, such as fully connect neural networks operating on MNIST
-- data, some extra imports may be needed not covered here.
module HordeAd
  ( module HordeAd.Core.DualNumber
  , module HordeAd.Core.Engine
  , module HordeAd.Core.PairOfVectors
  , module HordeAd.External.Optimizer
#if defined(VERSION_ghc_typelits_natnormalise)
  , module HordeAd.External.Adaptor
#endif
  ) where

import Prelude ()

import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.PairOfVectors
import HordeAd.External.Optimizer

#if defined(VERSION_ghc_typelits_natnormalise)
import HordeAd.External.Adaptor
#endif
