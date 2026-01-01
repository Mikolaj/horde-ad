{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module Data.Array.Nested.Types (
  -- * Reasoning helpers
  subst1, subst2,

  -- * Reified evidence of a type class
  Dict(..),

  -- * Type-level naturals
  pattern SZ, pattern SS,
  fromSNat', sameNat',
  snatPlus, snatMinus, snatMul,
  snatSucc,

  -- * Type-level lists
  type (++),
  Replicate,
  lemReplicateSucc,
  MapJust,
  lemMapJustEmpty, lemMapJustCons,
  Head,
  Tail,
  Init,
  Last,

  -- * Unsafe
  unsafeCoerceRefl,
) where

import Data.Proxy
import Data.Type.Equality
import GHC.TypeLits
import GHC.TypeNats qualified as TN
import Unsafe.Coerce qualified

-- Reasoning helpers

subst1 :: forall f a b. a :~: b -> f a :~: f b
subst1 Refl = Refl

subst2 :: forall f c a b. a :~: b -> f a c :~: f b c
subst2 Refl = Refl

-- | Evidence for the constraint @c a@.
data Dict c a where
  Dict :: c a => Dict c a

{-# INLINE fromSNat' #-}
fromSNat' :: SNat n -> Int
fromSNat' = fromEnum . TN.fromSNat

sameNat' :: SNat n -> SNat m -> Maybe (n :~: m)
sameNat' n@SNat m@SNat = sameNat n m

pattern SZ :: () => (n ~ 0) => SNat n
pattern SZ <- ((\sn -> testEquality sn (SNat @0)) -> Just Refl)
  where SZ = SNat

pattern SS :: forall np1. () => forall n. (n + 1 ~ np1) => SNat n -> SNat np1
pattern SS sn <- (snatPred -> Just (SNatPredResult sn Refl))
  where SS = snatSucc

{-# COMPLETE SZ, SS #-}

snatSucc :: SNat n -> SNat (n + 1)
snatSucc SNat = SNat

data SNatPredResult np1 = forall n. SNatPredResult (SNat n) (n + 1 :~: np1)
snatPred :: forall np1. SNat np1 -> Maybe (SNatPredResult np1)
snatPred snp1 =
  withKnownNat snp1 $
    case cmpNat (Proxy @1) (Proxy @np1) of
      LTI -> Just (SNatPredResult (SNat @(np1 - 1)) Refl)
      EQI -> Just (SNatPredResult (SNat @(np1 - 1)) Refl)
      GTI -> Nothing

-- This should be a function in base
snatPlus :: SNat n -> SNat m -> SNat (n + m)
snatPlus n m = TN.withSomeSNat (TN.fromSNat n + TN.fromSNat m) Unsafe.Coerce.unsafeCoerce

-- This should be a function in base
snatMinus :: SNat n -> SNat m -> SNat (n - m)
snatMinus n m = let res = TN.fromSNat n - TN.fromSNat m in res `seq` TN.withSomeSNat res Unsafe.Coerce.unsafeCoerce

-- This should be a function in base
snatMul :: SNat n -> SNat m -> SNat (n * m)
snatMul n m = TN.withSomeSNat (TN.fromSNat n * TN.fromSNat m) Unsafe.Coerce.unsafeCoerce


-- | Type-level list append.
type family l1 ++ l2 where
  '[] ++ l2 = l2
  (x : xs) ++ l2 = x : xs ++ l2

type family Replicate n a where
  Replicate 0 a = '[]
  Replicate n a = a : Replicate (n - 1) a

lemReplicateSucc :: forall a n proxy.
                    proxy n -> a : Replicate n a :~: Replicate (n + 1) a
lemReplicateSucc _ = unsafeCoerceRefl

type family MapJust l = r | r -> l where
  MapJust '[] = '[]
  MapJust (x : xs) = Just x : MapJust xs

lemMapJustEmpty :: MapJust sh :~: '[] -> sh :~: '[]
lemMapJustEmpty Refl = unsafeCoerceRefl

lemMapJustCons :: MapJust sh :~: Just n : sh' -> sh :~: n : Tail sh
lemMapJustCons Refl = unsafeCoerceRefl

type family Head l where
  Head (x : _) = x

type family Tail l where
  Tail (_ : xs) = xs

type family Init l where
  Init (x : y : xs) = x : Init (y : xs)
  Init '[x] = '[]

type family Last l where
  Last (x : y : xs) = Last (y : xs)
  Last '[x] = x


-- | This is just @'Unsafe.Coerce.unsafeCoerce' 'Refl'@, but specialised to
-- only typecheck for actual type equalities. One cannot, e.g. accidentally
-- write this:
--
-- @
-- foo :: Proxy a -> Proxy b -> a :~: b
-- foo = unsafeCoerceRefl
-- @
--
-- which would have been permitted with normal 'Unsafe.Coerce.unsafeCoerce',
-- but would have resulted in interesting memory errors at runtime.
unsafeCoerceRefl :: a :~: b
unsafeCoerceRefl = Unsafe.Coerce.unsafeCoerce Refl
