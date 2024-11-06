module HordeAd.Core.TensorADVal
  ( ) where

import Prelude

import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

instance LetTensor (ADVal ranked) where
  dlet :: forall x z. TensorKind x
       => Rep (ADVal ranked) x
       -> (RepDeep (ADVal ranked) x -> Rep (ADVal ranked) z)
       -> Rep (ADVal ranked) z
  dlet = case stensorKind @x of
  tlet :: forall x z. TensorKind x
       => Rep (ADVal ranked) x
       -> (RepShallow (ADVal ranked) x -> Rep (ADVal ranked) z)
       -> Rep (ADVal ranked) z
  tlet = case stensorKind @x of
  blet :: forall x z. TensorKind x
       => Rep (ADVal ranked) x
       -> (Rep (ADVal ranked) x -> Rep (ADVal ranked) z)
       -> Rep (ADVal ranked) z
  blet = case stensorKind @x of

  tconstant = undefined
