{-# LANGUAGE AllowAmbiguousTypes, CPP, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
-- | Some numeric classes and (orphan) instances for orthotope and ox-arrays
-- tensors.
module HordeAd.Internal.OrthotopeOrphanInstances
  ( -- * Numeric classes and instances for tensors
    IntegralF(..), RealFloatF(..), FlipR(..), FlipS(..), FlipX(..), valueOf
  ) where

import Prelude

import Control.DeepSeq (NFData)
import Data.Int (Int64)
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat, fromSNat, pattern SNat, sameNat)

import Data.Array.Mixed.Internal.Arith qualified as Mixed.Internal.Arith
  (liftVEltwise2)
import Data.Array.Nested (KnownShS (..), KnownShX, MapJust, Replicate)
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Mixed qualified as Nested.Internal.Mixed
import Data.Array.Nested.Internal.Ranked qualified as Nested.Internal
import Data.Array.Nested.Internal.Shaped qualified as Nested.Internal

-- stolen from orthotope, with obfuscation; TODO: move elsewhere
{-# INLINE valueOf #-}
valueOf :: forall n r. (KnownNat n, Num r) => r
valueOf = fromInteger $ fromSNat (SNat @n)

-- * Numeric classes and instances for tensors

class IntegralF a where
  quotF, remF :: a -> a -> a

instance IntegralF Int64 where
  quotF = quot
  remF = rem

instance (Nested.PrimElt r, Integral r)
         => IntegralF (Nested.Ranked n r) where
  -- These can't be partial, because our conditionals are not lazy
  -- and so the counterfactual branches, with zeros, may get executed
  -- even though they are subsequently ignored.
  quotF = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quot a b) x y)))
                            -- TODO: do better somehow
  remF = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else rem a b) x y)))
                            -- TODO: do better somehow

instance (Nested.PrimElt r, Integral r)
         => IntegralF (Nested.Shaped sh r) where
  quotF = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quot a b) x y)))
                            -- TODO: do better somehow
  remF = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else rem a b) x y)))
                            -- TODO: do better somehow

instance (Nested.PrimElt r, Integral r)
         => IntegralF (Nested.Mixed sh r) where
  quotF =   (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else quot a b) x y)))
                            -- TODO: do better somehow
  remF =    (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith
                          (\a b -> if b == 0 then 0 else rem a b) x y)))
                            -- TODO: do better somehow

class Floating a => RealFloatF a where
  atan2F :: a -> a -> a

instance (Nested.NumElt r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r)
         => RealFloatF (Nested.Ranked n r) where
  atan2F = Nested.Internal.arithPromoteRanked2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2 x y)))  -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r)
         => RealFloatF (Nested.Shaped sh r) where
  atan2F = Nested.Internal.arithPromoteShaped2
            (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2 x y)))  -- TODO: do better somehow

instance (Nested.NumElt r, Nested.PrimElt r, RealFloat r, Nested.FloatElt r)
         => RealFloatF (Nested.Mixed sh r) where
  atan2F =   (Nested.Internal.Mixed.mliftNumElt2
               (flip Mixed.Internal.Arith.liftVEltwise2
                  (\x' y' ->
                     let (x, y) = case (x', y') of
                           (Left x2, Left y2) ->
                             (V.singleton x2, V.singleton y2)
                           _ ->
                             ( either (V.replicate (V.length y)) id x'
                             , either (V.replicate (V.length x)) id y' )
                     in V.zipWith atan2 x y)))  -- TODO: do better somehow

type role FlipR nominal nominal nominal
type FlipR :: forall {k}. (Nat -> k -> Type) -> k -> Nat -> Type
newtype FlipR p a (b :: Nat) = FlipR { runFlipR :: p b a }

instance (Nested.Elt r, Show r, Show (Nested.Mixed (Replicate n Nothing) r))
         => Show (FlipR Nested.Ranked r n) where
  showsPrec :: Int -> FlipR Nested.Ranked r n -> ShowS
  showsPrec d (FlipR u) =
    showString "Flip " . showParen True (showsPrec d u)

instance (Eq r, KnownNat n, Eq (Nested.Mixed (Replicate n Nothing) r)) => Eq (FlipR Nested.Ranked r n) where
  (==) :: FlipR Nested.Ranked r n -> FlipR Nested.Ranked r n -> Bool
  FlipR u == FlipR v = u == v

instance (Ord r, KnownNat n, Eq (Nested.Mixed (Replicate n Nothing) r), Ord (Nested.Mixed (Replicate n Nothing) r)) => Ord (FlipR Nested.Ranked r n) where
  FlipR u <= FlipR v = u <= v

-- TODO: This is only to ensure fromInteger crashes promptly if not rank 0.
-- deriving instance Num (f a b) => Num (FlipR f b a)
instance (Nested.NumElt r, Nested.PrimElt r, Nested.Elt r, KnownNat n, Num r)
         => Num (FlipR Nested.Ranked r n) where
  (FlipR t) + (FlipR u) = FlipR $ t + u
  (FlipR t) - (FlipR u) = FlipR $ t - u
  (FlipR t) * (FlipR u) = FlipR $ t * u
  negate (FlipR t) = FlipR $ negate t
  abs (FlipR t) = FlipR $ abs t
  signum (FlipR t) = FlipR $ signum t
  fromInteger = case sameNat (Proxy @n) (Proxy @0) of
    Just Refl -> FlipR . Nested.rscalar . fromInteger
    Nothing -> error $ "FlipR(Nested.Ranked).fromInteger: shape unknown at rank "
                       ++ show (valueOf @n :: Int)

deriving instance IntegralF (f a b) => IntegralF (FlipR f b a)

deriving instance (Num (FlipR f b a), Fractional (f a b)) => Fractional (FlipR f b a)

deriving instance (Num (FlipR f b a), Floating (f a b)) => Floating (FlipR f b a)

deriving instance (Num (FlipR f b a), RealFloatF (f a b)) => RealFloatF (FlipR f b a)

deriving instance NFData (f a b) => NFData (FlipR f b a)

type role FlipS nominal nominal nominal
type FlipS :: forall {k}. ([Nat] -> k -> Type) -> k -> [Nat] -> Type
newtype FlipS p a (b :: [Nat]) = FlipS { runFlipS :: p b a }

instance (Nested.Elt r, Show r, Show (Nested.Mixed (MapJust sh) r))
         => Show (FlipS Nested.Shaped r sh) where
  showsPrec :: Int -> FlipS Nested.Shaped r sh -> ShowS
  showsPrec d (FlipS u) =
    showString "FlipS " . showParen True (showsPrec d u)

instance (Eq r, KnownShS sh, Eq (Nested.Mixed (MapJust sh) r)) => Eq (FlipS Nested.Shaped r sh) where
  (==) :: FlipS Nested.Shaped r sh -> FlipS Nested.Shaped r sh -> Bool
  FlipS u == FlipS v = u == v

instance (Ord r, KnownShS sh, Eq (Nested.Mixed (MapJust sh) r), Ord (Nested.Mixed (MapJust sh) r)) => Ord (FlipS Nested.Shaped r sh) where
  FlipS u <= FlipS v = u <= v

deriving instance Num (f a b) => Num (FlipS f b a)

deriving instance IntegralF (f a b) => IntegralF (FlipS f b a)

deriving instance Fractional (f a b) => Fractional (FlipS f b a)

deriving instance Floating (f a b) => Floating (FlipS f b a)

deriving instance RealFloatF (f a b) => RealFloatF (FlipS f b a)

deriving instance NFData (f a b) => NFData (FlipS f b a)

type role FlipX nominal nominal nominal
type FlipX :: forall {k}. ([Maybe Nat] -> k -> Type) -> k -> [Maybe Nat] -> Type
newtype FlipX p a (b :: [Maybe Nat]) = FlipX { runFlipX :: p b a }

instance (Nested.Elt r, Show r, Show (Nested.Mixed sh r))
         => Show (FlipX Nested.Mixed r sh) where
  showsPrec :: Int -> FlipX Nested.Mixed r sh -> ShowS
  showsPrec d (FlipX u) =
    showString "FlipX " . showParen True (showsPrec d u)

instance (Eq r, KnownShX sh, Eq (Nested.Mixed sh r)) => Eq (FlipX Nested.Mixed r sh) where
  (==) :: FlipX Nested.Mixed r sh -> FlipX Nested.Mixed r sh -> Bool
  FlipX u == FlipX v = u == v

instance (Ord r, KnownShX sh, Eq (Nested.Mixed sh r), Ord (Nested.Mixed sh r)) => Ord (FlipX Nested.Mixed r sh) where
  FlipX u <= FlipX v = u <= v

deriving instance Num (f a b) => Num (FlipX f b a)

deriving instance IntegralF (f a b) => IntegralF (FlipX f b a)

deriving instance Fractional (f a b) => Fractional (FlipX f b a)

deriving instance Floating (f a b) => Floating (FlipX f b a)

deriving instance RealFloatF (f a b) => RealFloatF (FlipX f b a)

deriving instance NFData (f a b) => NFData (FlipX f b a)
