{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Data.Array.Nested.Lemmas where

import Data.Proxy
import Data.Type.Equality
import GHC.TypeLits

import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types


-- * Lemmas about numbers and lists

-- ** Nat

lemLeqSuccSucc :: k + 1 <= n => Proxy k -> Proxy n -> (k <=? n - 1) :~: True
lemLeqSuccSucc _ _ = unsafeCoerceRefl

lemLeqPlus :: n <= m => Proxy n -> Proxy m -> Proxy k -> (n <=? (m + k)) :~: 'True
lemLeqPlus _ _ _ = Refl

-- ** Append

lemAppNil :: l ++ '[] :~: l
lemAppNil = unsafeCoerceRefl

lemAppAssoc :: Proxy a -> Proxy b -> Proxy c -> (a ++ b) ++ c :~: a ++ (b ++ c)
lemAppAssoc _ _ _ = unsafeCoerceRefl

lemAppLeft :: Proxy l -> a :~: b -> a ++ l :~: b ++ l
lemAppLeft _ Refl = Refl

-- ** Simple type families

lemReplicatePlusApp :: forall n m a. SNat n -> Proxy m -> Proxy a
                    -> Replicate (n + m) a :~: Replicate n a ++ Replicate m a
{- for now, the plugins can't derive a type for this code, see
   https://github.com/clash-lang/ghc-typelits-natnormalise/pull/98#issuecomment-3332842214
lemReplicatePlusApp sn _ _ = go sn
  where
    go :: SNat n' -> Replicate (n' + m) a :~: Replicate n' a ++ Replicate m a
    go SZ = Refl
    go (SS (n :: SNat n'm1))
      | Refl <- lemReplicateSucc @a n
      , Refl <- go n
      = sym (lemReplicateSucc @a (SNat @(n'm1 + m)))
-}
lemReplicatePlusApp _ _ _ = unsafeCoerceRefl

lemReplicateEmpty :: proxy n -> Replicate n (Nothing @Nat) :~: '[] -> n :~: 0
lemReplicateEmpty _ Refl = unsafeCoerceRefl

-- TODO: make less ad-hoc and rename these three:
lemReplicateCons :: proxy sh -> proxy' n1 -> Nothing : sh :~: Replicate n1 Nothing -> n1 :~: Rank sh + 1
lemReplicateCons _ _ Refl = unsafeCoerceRefl

lemReplicateCons2 :: proxy sh -> proxy' n1 -> Nothing : sh :~: Replicate n1 Nothing -> sh :~: Replicate (Rank sh) Nothing
lemReplicateCons2 _ _ Refl = unsafeCoerceRefl

lemReplicateSucc2 :: forall n1 n proxy.
                     proxy n1 -> n + 1 :~: n1 -> Nothing @Nat : Replicate n Nothing :~: Replicate n1 Nothing
lemReplicateSucc2 _ _ = unsafeCoerceRefl

lemDropLenApp :: Rank l1 <= Rank l2
              => Proxy l1 -> Proxy l2 -> Proxy rest
              -> DropLen l1 l2 ++ rest :~: DropLen l1 (l2 ++ rest)
lemDropLenApp _ _ _ = unsafeCoerceRefl

lemTakeLenApp :: Rank l1 <= Rank l2
              => Proxy l1 -> Proxy l2 -> Proxy rest
              -> TakeLen l1 l2 :~: TakeLen l1 (l2 ++ rest)
lemTakeLenApp _ _ _ = unsafeCoerceRefl

lemInitApp :: Proxy l -> Proxy x -> Init (l ++ '[x]) :~: l
lemInitApp _ _ = unsafeCoerceRefl

lemLastApp :: Proxy l -> Proxy x -> Last (l ++ '[x]) :~: x
lemLastApp _ _ = unsafeCoerceRefl


-- ** KnownNat

lemKnownNatSucc :: KnownNat n => Dict KnownNat (n + 1)
lemKnownNatSucc = Dict

lemKnownNatRank :: ShX sh i -> Dict KnownNat (Rank sh)
lemKnownNatRank ZSX = Dict
lemKnownNatRank (_ :$% sh) | Dict <- lemKnownNatRank sh = Dict

lemKnownNatRankSSX :: StaticShX sh -> Dict KnownNat (Rank sh)
lemKnownNatRankSSX ZKX = Dict
lemKnownNatRankSSX (_ :!% ssh) | Dict <- lemKnownNatRankSSX ssh = Dict


-- * Lemmas about shapes

-- ** Known shapes

lemKnownReplicate :: SNat n -> Dict KnownShX (Replicate n Nothing)
lemKnownReplicate sn = lemKnownShX (ssxFromSNat sn)

lemKnownShX :: StaticShX sh -> Dict KnownShX sh
lemKnownShX ZKX = Dict
lemKnownShX (SKnown SNat :!% ssh) | Dict <- lemKnownShX ssh = Dict
lemKnownShX (SUnknown () :!% ssh) | Dict <- lemKnownShX ssh = Dict

lemKnownMapJust :: forall sh. KnownShS sh => Proxy sh -> Dict KnownShX (MapJust sh)
lemKnownMapJust _ = lemKnownShX (go (knownShS @sh))
  where
    go :: ShS sh' -> StaticShX (MapJust sh')
    go ZSS = ZKX
    go (n :$$ sh) = SKnown n :!% go sh

-- ** Rank

lemRankApp :: forall sh1 sh2.
              StaticShX sh1 -> StaticShX sh2
           -> Rank (sh1 ++ sh2) :~: Rank sh1 + Rank sh2
lemRankApp ZKX _ = Refl
lemRankApp (_ :!% (ssh1 :: StaticShX sh1T)) ssh2
  = lem (Proxy @(Rank sh1T)) Proxy Proxy $
      sym (lemRankApp ssh1 ssh2)
  where
    lem :: proxy a -> proxy b -> proxy c
        -> (a + b :~: c)
        -> c + 1 :~: (a + 1 + b)
    lem _ _ _ Refl = Refl

lemRankAppComm :: proxy sh1 -> proxy sh2
               -> Rank (sh1 ++ sh2) :~: Rank (sh2 ++ sh1)
lemRankAppComm _ _ = unsafeCoerceRefl

lemRankReplicate :: proxy n -> Rank (Replicate n (Nothing @Nat)) :~: n
lemRankReplicate _ = unsafeCoerceRefl

lemRankMapJust :: ShS sh -> Rank (MapJust sh) :~: Rank sh
lemRankMapJust ZSS = Refl
lemRankMapJust (_ :$$ sh') | Refl <- lemRankMapJust sh' = Refl

-- ** Related to MapJust and/or Permutation

lemTakeLenMapJust :: Perm is -> ShS sh -> TakeLen is (MapJust sh) :~: MapJust (TakeLen is sh)
lemTakeLenMapJust PNil _ = Refl
lemTakeLenMapJust (_ `PCons` is) (_ :$$ sh) | Refl <- lemTakeLenMapJust is sh = Refl
lemTakeLenMapJust (_ `PCons` _) ZSS = error "TakeLen of empty"

lemDropLenMapJust :: Perm is -> ShS sh -> DropLen is (MapJust sh) :~: MapJust (DropLen is sh)
lemDropLenMapJust PNil _ = Refl
lemDropLenMapJust (_ `PCons` is) (_ :$$ sh) | Refl <- lemDropLenMapJust is sh = Refl
lemDropLenMapJust (_ `PCons` _) ZSS = error "DropLen of empty"

lemIndexMapJust :: SNat i -> ShS sh -> Index i (MapJust sh) :~: Just (Index i sh)
lemIndexMapJust SZ (_ :$$ _) = Refl
lemIndexMapJust (SS (i :: SNat i')) ((_ :: SNat n) :$$ (sh :: ShS sh'))
  | Refl <- lemIndexMapJust i sh
  , Refl <- lemIndexSucc (Proxy @i') (Proxy @(Just n)) (Proxy @(MapJust sh'))
  , Refl <- lemIndexSucc (Proxy @i') (Proxy @n) (Proxy @sh')
  = Refl
lemIndexMapJust _ ZSS = error "Index of empty"

lemPermuteMapJust :: Perm is -> ShS sh -> Permute is (MapJust sh) :~: MapJust (Permute is sh)
lemPermuteMapJust PNil _ = Refl
lemPermuteMapJust (i `PCons` is) sh
  | Refl <- lemPermuteMapJust is sh
  , Refl <- lemIndexMapJust i sh
  = Refl

lemMapJustApp :: ShS sh1 -> Proxy sh2
              -> MapJust (sh1 ++ sh2) :~: MapJust sh1 ++ MapJust sh2
lemMapJustApp ZSS _ = Refl
lemMapJustApp (_ :$$ sh) p | Refl <- lemMapJustApp sh p = Refl
