{-# LANGUAGE CPP #-}
#if MIN_VERSION_GLASGOW_HASKELL(9,12,1,0)
{-# OPTIONS_GHC -fno-expose-overloaded-unfoldings #-}
#endif
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Arithmetic instances for AST with sharing method AstMethodShare.
module HordeAd.Core.AstMethodShare
  ( astShareNoSimplify
  ) where

import Prelude

import Data.Type.Equality (testEquality, (:~:) (Refl))
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (typeRep)

import Data.Array.Nested (type (++))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Convert (withShsFromShR, withShsFromShX)
import Data.Array.Nested.Mixed qualified as Mixed
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersAst
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.Conversion
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Unlawful numeric instances for AST scalars; they are lawful modulo evaluation

-- The normal form has AstConcreteK or AstFromPlain (AstConcreteK),
-- if any, as the first argument of the constructor.
-- No flattening is performed beyond that.
instance (NumScalar r, KnownSpan s)
         => Num (AstTensor AstMethodShare s (TKScalar r)) where
  AstPrimalPart u + AstPrimalPart v = primalPart $ u + v
  AstDualPart u + AstDualPart v = dualPart $ u + v
  AstPlainPart @_ @s1 u + AstPlainPart @_ @s2 v
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
      plainPart $ u + v
  AstFromPrimal u + AstFromPrimal v = fromPrimal $ u + v
  AstFromDual u + AstFromDual v = fromDual $ u + v
  AstFromPlain u + AstFromPlain v = fromPlain $ u + v
  AstConcreteK 0 + u = u
  u + AstConcreteK 0 = u
  AstFromPlain (AstConcreteK 0) + u = u
  u + AstFromPlain (AstConcreteK 0) = u
  AstConcreteK n + AstConcreteK k = AstConcreteK (n + k)
  AstConcreteK n + AstPlusK (AstConcreteK k) u = AstConcreteK (n + k) + u
  AstPlusK (AstConcreteK n) u + AstConcreteK k = AstConcreteK (n + k) + u
  AstPlusK (AstConcreteK n) u + AstPlusK (AstConcreteK k) v =
    AstConcreteK (n + k) + AstPlusK u v  -- u and v can cancel, but unlikely
  AstFromPlain (AstConcreteK n) + AstPlusK (AstFromPlain (AstConcreteK k)) u =
    AstFromPlain (AstConcreteK (n + k)) + u
  AstPlusK (AstFromPlain (AstConcreteK n)) u + AstFromPlain (AstConcreteK k) =
    AstFromPlain (AstConcreteK (n + k)) + u
  AstPlusK (AstFromPlain (AstConcreteK n)) u
    + AstPlusK (AstFromPlain (AstConcreteK k)) v =
      AstFromPlain (AstConcreteK (n + k)) + AstPlusK u v

  -- Unfortunately, these only fire if the required subterms are at the top
  -- of the reduced term, which happens rarely except in small terms.
  -- We could keep variables at the top, but they'd compete with AstConcreteK.
  AstN1K NegateOp (AstVar var) + AstVar var'
    | var == var' = 0
  AstN1K NegateOp (AstConvert _ (AstVar var))
    + AstConvert _ (AstVar var')
    | varNameToAstVarId var == varNameToAstVarId var' = 0
  AstN1K NegateOp (AstVar var) + AstPlusK (AstVar var') u
    | var == var' = u
  AstN1K NegateOp (AstConvert _ (AstVar var))
    + AstPlusK (AstConvert _ (AstVar var')) u
    | varNameToAstVarId var == varNameToAstVarId var' = u
  AstVar var' + AstN1K NegateOp (AstVar var)
    | var == var' = 0
  AstConvert _ (AstVar var')
    + AstN1K NegateOp (AstConvert _ (AstVar var))
    | varNameToAstVarId var == varNameToAstVarId var' = 0
  AstVar var' + AstPlusK (AstN1K NegateOp (AstVar var)) u
    | var == var' = u
  AstConvert _ (AstVar var')
    + AstPlusK (AstN1K NegateOp (AstConvert _ (AstVar var))) u
    | varNameToAstVarId var == varNameToAstVarId var' = u

  AstI2K RemOp (AstN1K NegateOp (AstVar var)) (AstConcreteK n)
   + AstI2K RemOp (AstVar var') (AstConcreteK n')
     | var == var' && n == n' = 0
  AstI2K RemOp (AstN1K NegateOp (AstConvert _ (AstVar var)))
               (AstConcreteK n)
   + AstI2K RemOp (AstConvert _ (AstVar var')) (AstConcreteK n')
     | varNameToAstVarId var == varNameToAstVarId var' && n == n' = 0
  AstI2K RemOp (AstN1K NegateOp (AstVar var)) (AstConcreteK n)
   + AstPlusK (AstI2K RemOp (AstVar var') (AstConcreteK n')) u
     | var == var' && n == n' = u
  AstI2K RemOp (AstN1K NegateOp (AstConvert _ (AstVar var)))
               (AstConcreteK n)
   + AstPlusK (AstI2K RemOp (AstConvert _ (AstVar var'))
                            (AstConcreteK n')) u
     | varNameToAstVarId var == varNameToAstVarId var' && n == n' = u
  AstI2K RemOp (AstVar var') (AstConcreteK n')
   + AstI2K RemOp (AstN1K NegateOp (AstVar var)) (AstConcreteK n)
     | var == var' && n == n' = 0
  AstI2K RemOp (AstConvert _ (AstVar var')) (AstConcreteK n')
   + AstI2K RemOp (AstN1K NegateOp (AstConvert _ (AstVar var)))
                                   (AstConcreteK n)
     | varNameToAstVarId var == varNameToAstVarId var' && n == n' = 0
  AstI2K RemOp (AstVar var') (AstConcreteK n')
   + AstPlusK (AstI2K RemOp (AstN1K NegateOp (AstVar var)) (AstConcreteK n)) u
     | var == var' && n == n' = u
  AstI2K RemOp (AstConvert _ (AstVar var')) (AstConcreteK n')
   + AstPlusK (AstI2K RemOp (AstN1K NegateOp (AstConvert _ (AstVar var)))
                            (AstConcreteK n)) u
     | varNameToAstVarId var == varNameToAstVarId var' && n == n' = u

  AstPlusK u@AstConcreteK{} v + w = AstPlusK u (AstPlusK v w)  -- as above
  u + v@AstConcreteK{} = AstPlusK v u
  u + AstPlusK v@AstConcreteK{} w = AstPlusK v (AstPlusK u w)  -- as above
  AstPlusK u@(AstFromPlain (AstConcreteK{})) v + w =
    AstPlusK u (AstPlusK v w)  -- as above
  u + v@(AstFromPlain (AstConcreteK{})) = AstPlusK v u
  u + AstPlusK v@(AstFromPlain (AstConcreteK{})) w =
    AstPlusK v (AstPlusK u w)  -- as above
  t1 + t2 | eqK t1 t2 = 2 * t1
  t1 + AstTimesK (AstConcreteK n) t2 | eqK t1 t2 = AstConcreteK (n + 1) * t1
  AstTimesK (AstConcreteK n) t2 + t1 | eqK t1 t2 = AstConcreteK (n + 1) * t1
  AstTimesK (AstConcreteK n1) t1 + AstTimesK (AstConcreteK n2) t2
    | eqK t1 t2 = AstConcreteK (n1 + n2) * t1
  t1 + AstTimesK (AstFromPlain (AstConcreteK n)) t2 | eqK t1 t2 =
    AstFromPlain (AstConcreteK (n + 1)) * t1
  AstTimesK (AstFromPlain (AstConcreteK n)) t2 + t1 | eqK t1 t2 =
    AstFromPlain (AstConcreteK (n + 1)) * t1
  AstTimesK (AstFromPlain (AstConcreteK n1)) t1
    + AstTimesK (AstFromPlain (AstConcreteK n2)) t2 | eqK t1 t2 =
      AstFromPlain (AstConcreteK (n1 + n2)) * t1
  u + v = AstPlusK u v

  AstPrimalPart u * AstPrimalPart v = primalPart $ u * v
  AstPlainPart @_ @s1 u * AstPlainPart @_ @s2 v
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
      plainPart $ u * v
  AstFromPrimal u * AstFromPrimal v = fromPrimal $ u * v
  AstFromDual{} * AstFromDual{} = 0
  AstFromPlain u * AstFromPlain v = fromPlain $ u * v
  AstConcreteK 0 * _ = 0
  _ * AstConcreteK 0 = 0
  AstConcreteK 1 * u = u
  u * AstConcreteK 1 = u
  AstFromPlain (AstConcreteK 0) * _ = 0
  _ * AstFromPlain (AstConcreteK 0) = 0
  AstFromPlain (AstConcreteK 1) * u = u
  u * AstFromPlain (AstConcreteK 1) = u
  AstConcreteK n * AstConcreteK k = AstConcreteK (n * k)
  AstConcreteK n * AstTimesK (AstConcreteK k) u = AstConcreteK (n * k) * u
  AstTimesK (AstConcreteK n) u * AstConcreteK k = AstConcreteK (n * k) * u
  AstTimesK (AstConcreteK n) u * AstTimesK (AstConcreteK k) v =
    AstConcreteK (n * k) * AstTimesK u v  -- u and v can cancel, but unlikely
  AstFromPlain (AstConcreteK n) * AstTimesK (AstFromPlain (AstConcreteK k)) u =
    AstFromPlain (AstConcreteK (n * k)) * u
  AstTimesK (AstFromPlain (AstConcreteK n)) u * AstFromPlain (AstConcreteK k) =
    AstFromPlain (AstConcreteK (n * k)) * u
  AstTimesK (AstFromPlain (AstConcreteK n)) u
    * AstTimesK (AstFromPlain (AstConcreteK k)) v =
      AstFromPlain (AstConcreteK (n * k)) * AstTimesK u v

  -- This breaks sharing, because although u is concrete and so doesn't
  -- have to be shared, the multiplication is not shared --- we end up
  -- with one addition and two multiplications, not one. Similarly below.
  -- However, three instead of two cheap scalar operations is benign
  -- and there's no risk of exponential blowup via duplicating
  -- variables, so the ability to simplify better is worth the overhead.
  -- OTOH, we don't declare scalar operations small in astIsSmall,
  -- because that could lead to such operations being inlined an unbounded
  -- number of times into expressions.
  -- Note that due to non-scalar versions of these rules being banned,
  -- we get different terms depending on the form of conversions
  -- and rank 0 arrays.
  u@AstConcreteK{} * AstPlusK v w = AstPlusK (u * v) (u * w)
  AstTimesK u@AstConcreteK{} x * AstPlusK v w =
    AstTimesK x (AstPlusK (u * v) (u * w))
  AstPlusK v w * u@AstConcreteK{} = AstPlusK (v * u) (w * u)
  AstPlusK v w * AstTimesK u@AstConcreteK{} x =
    AstTimesK (AstPlusK (v * u) (w * u)) x
  u@(AstFromPlain (AstConcreteK{})) * AstPlusK v w = AstPlusK (u * v) (u * w)
  AstTimesK u@(AstFromPlain (AstConcreteK{})) x * AstPlusK v w =
    AstTimesK x (AstPlusK (u * v) (u * w))
  AstPlusK v w * u@(AstFromPlain (AstConcreteK{})) = AstPlusK (v * u) (w * u)
  AstPlusK v w * AstTimesK u@(AstFromPlain (AstConcreteK{})) x =
    AstTimesK (AstPlusK (v * u) (w * u)) x

  AstN1K NegateOp u * AstN1K NegateOp v = AstTimesK u v

  {- TODO: these rules increase the number of occurrences of a variable
     and trade multiplication and quotient for an equally problematic remnant,
     so they are disabled until we find a way to profit from them.
  -- With static shapes, the second argument to QuotOp and RemOp
  -- is often a constant, which makes such rules worth including,
  -- since they are likely to fire. To help them fire, we avoid changing
  -- that constant, if possible, e.g., in rules for NegateOp.
  AstConcreteK n * AstI2K QuotOp (AstVar var) (AstConcreteK n')
    | n == n' =
      AstPlusK
        (AstVar var)
        (negate (AstI2K RemOp (AstVar var) (AstConcreteK n)))
  AstTimesK (AstConcreteK n) x * AstI2K QuotOp (AstVar var)
                                               (AstConcreteK n')
    | n == n' =
      AstTimesK
        x
        (AstPlusK
           (AstVar var)
           (negate (AstI2K RemOp (AstVar var) (AstConcreteK n))))
  AstI2K QuotOp (AstVar var) (AstConcreteK n') * AstConcreteK n
    | n == n' =
      AstPlusK
        (AstVar var)
        (negate (AstI2K RemOp (AstVar var) (AstConcreteK n)))
  AstI2K QuotOp (AstVar var)
                (AstConcreteK n') * AstTimesK (AstConcreteK n) x
    | n == n' =
      AstTimesK
        (AstPlusK
           (AstVar var)
           (negate (AstI2K RemOp (AstVar var) (AstConcreteK n))))
        x
  -}

  AstTimesK u@AstConcreteK{} v * w = AstTimesK u (AstTimesK v w)  -- as above
  u * v@AstConcreteK{} = AstTimesK v u
  u * AstTimesK v@AstConcreteK{} w = AstTimesK v (AstTimesK u w)  -- as above
  AstTimesK u@(AstFromPlain (AstConcreteK{})) v * w =
    AstTimesK u (AstTimesK v w)  -- as above
  u * v@(AstFromPlain (AstConcreteK{})) = AstTimesK v u
  u * AstTimesK v@(AstFromPlain (AstConcreteK{})) w =
    AstTimesK v (AstTimesK u w)  -- as above
  u * v = AstTimesK u v

  negate (AstCond b n k) = AstCond b (negate n) (negate k)
  negate (AstPrimalPart n) = primalPart (negate n)
  negate (AstDualPart n) = dualPart (negate n)
  negate (AstPlainPart n) = plainPart (negate n)
  negate (AstFromPrimal n) = fromPrimal (negate n)
  negate (AstFromDual n) = fromDual (negate n)
  negate (AstFromPlain n) = fromPlain (negate n)
  negate (AstPlusK u v) = AstPlusK (negate u) (negate v)
  negate (AstTimesK u v) = negate u * v
  negate (AstN1K NegateOp u) = u
  negate (AstN1K SignumOp u) = AstN1K SignumOp (negate u)
  negate (AstI2K QuotOp u v) = AstI2K QuotOp (negate u) v
    -- v is likely positive and let's keep it so
  negate (AstI2K RemOp u v) = AstI2K RemOp (negate u) v
    -- v is likely positive and let's keep it so
  negate (AstConcreteK n) = AstConcreteK (negate n)
  negate u = AstN1K NegateOp u
  abs (AstPrimalPart n) = primalPart (abs n)
  abs (AstDualPart n) = dualPart (abs n)
  abs (AstPlainPart n) = plainPart (abs n)
  abs (AstFromPrimal n) = fromPrimal (abs n)
  abs (AstFromDual n) = fromDual (abs n)
  abs (AstFromPlain n) = fromPlain (abs n)
  abs (AstConcreteK n) = AstConcreteK (abs n)
  abs (AstN1K AbsOp u) = AstN1K AbsOp u
  abs (AstN1K NegateOp u) = abs u
  abs u = AstN1K AbsOp u
  signum (AstPrimalPart n) = primalPart (signum n)
  signum (AstDualPart n) = dualPart (signum n)
  signum (AstPlainPart n) = plainPart (signum n)
  signum (AstFromPrimal n) = fromPrimal (signum n)
  signum (AstFromDual n) = fromDual (signum n)
  signum (AstFromPlain n) = fromPlain (signum n)
  signum (AstConcreteK n) = AstConcreteK (signum n)
  signum (AstN1K SignumOp u) = AstN1K SignumOp u
  signum u = AstN1K SignumOp u
  {-# INLINE fromInteger #-}
  fromInteger i = fromPlain $ AstConcreteK (fromInteger i)

-- An approximation. False doesn't imply terms have different semantics,
-- but True implies they have equal semantics.
eqK :: AstTensor AstMethodShare s (TKScalar r)
    -> AstTensor AstMethodShare s (TKScalar r)
    -> Bool
-- This is wrong for <=. but correct for this approximation:
eqK (AstVar var1) (AstVar var2) = var1 == var2
eqK (AstPrimalPart u1) (AstPrimalPart u2) = eqK u1 u2
eqK (AstPlainPart @_ @s1 u1) (AstPlainPart @_ @s2 u2)
  | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
    eqK u1 u2
eqK (AstFromPrimal u1) (AstFromPrimal u2) = eqK u1 u2
eqK AstFromDual{} AstFromDual{} = True
eqK (AstFromPlain u1) (AstFromPlain u2) = eqK u1 u2
eqK (AstPlusK u1 v1) (AstPlusK u2 v2) =
  eqK u1 u2 && eqK v1 v2 || eqK u1 v2 && eqK v1 u2
eqK (AstTimesK u1 v1) (AstTimesK u2 v2) =
  eqK u1 u2 && eqK v1 v2 || eqK u1 v2 && eqK v1 u2
eqK (AstN1K opCode1 u1) (AstN1K opCode2 u2) = opCode1 == opCode2 && eqK u1 u2
eqK (AstR1K opCode1 u1) (AstR1K opCode2 u2) = opCode1 == opCode2 && eqK u1 u2
eqK (AstR2K opCode1 u1 v1) (AstR2K opCode2 u2 v2) =
  opCode1 == opCode2 && eqK u1 u2 && eqK v1 v2
eqK (AstI2K opCode1 u1 v1) (AstI2K opCode2 u2 v2) =
  opCode1 == opCode2 && eqK u1 u2 && eqK v1 v2
eqK (AstConcreteK u1) (AstConcreteK u2) = u1 == u2
eqK (AstFloorK @r1 u1) (AstFloorK @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) = eqK u1 u2
eqK (AstFromIntegralK @r1 u1) (AstFromIntegralK @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) = eqK u1 u2
eqK (AstCastK @r1 u1) (AstCastK @r2 u2)
  | Just Refl <- testEquality (typeRep @r1) (typeRep @r2) = eqK u1 u2
eqK (AstConvert _ (AstVar u)) (AstConvert _ (AstVar v)) =
  varNameToAstVarId u == varNameToAstVarId v
eqK _ _ = False

-- Div and mod operations are very costly (simplifying them requires
-- constructing conditionals, etc), so they are not included in IntegralH.
instance (NumScalar r, IntegralH r, Nested.IntElt r, KnownSpan s)
         => IntegralH (AstTensor AstMethodShare s (TKScalar r)) where
  quotH (AstPrimalPart n) (AstPrimalPart k) = primalPart (quotH n k)
  quotH (AstPlainPart @_ @s1 n) (AstPlainPart @_ @s2 k)
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
      plainPart (quotH n k)
  quotH (AstFromPrimal n) (AstFromPrimal k) = fromPrimal (quotH n k)
  quotH (AstFromPlain n) (AstFromPlain k) = fromPlain (quotH n k)
  quotH (AstConcreteK n) (AstConcreteK k) = AstConcreteK (quotH n k)
  quotH (AstConcreteK 0) _ = 0
  quotH u (AstFromPlain (AstConcreteK 1)) = u
  quotH (AstFromPlain (AstConcreteK 0)) _ = 0
  quotH u (AstConcreteK 1) = u
  quotH (AstI2K RemOp _ (AstConcreteK k)) (AstConcreteK k')
    | k' >= k && k >= 0 = 0
  quotH (AstI2K QuotOp u v) w = quotH u (v * w)
  quotH (AstTimesK (AstConcreteK n) v) (AstConcreteK n')
    | n == n' = v
  quotH u v =
    let t = AstI2K QuotOp u v
    in case bounds t of
      Just (u1, u2) | u1 == u2 -> fromPlain $ AstConcreteK u1
      _ -> t

  remH (AstPrimalPart n) (AstPrimalPart k) = primalPart (remH n k)
  remH (AstPlainPart @_ @s1 n) (AstPlainPart @_ @s2 k)
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
      plainPart (remH n k)
  remH (AstFromPrimal n) (AstFromPrimal k) = fromPrimal (remH n k)
  remH (AstFromPlain n) (AstFromPlain k) = fromPlain (remH n k)
  remH (AstConcreteK n) (AstConcreteK k) = AstConcreteK (remH n k)
  remH (AstConcreteK 0) _ = 0
  remH _ (AstConcreteK 1) = 0
  remH (AstFromPlain (AstConcreteK 0)) _ = 0
  remH _ (AstFromPlain (AstConcreteK 1)) = 0
  remH (AstI2K RemOp u (AstConcreteK k)) (AstConcreteK k')
    | k' >= k && k >= 0 = AstI2K RemOp u (AstConcreteK k)
  remH (AstI2K RemOp u (AstConcreteK k)) (AstConcreteK k')
    | remH k k' == 0 && k > 0 = remH u (AstConcreteK k')
  remH (AstTimesK (AstConcreteK n) _) (AstConcreteK n')
    | remH n n' == 0 = 0
  remH u v =
    let t = AstI2K RemOp u v
    in case bounds t of
      Just (u1, u2) | u1 == u2 -> fromPlain $ AstConcreteK u1
      _ -> t

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Fractional (AstTensor AstMethodShare s (TKScalar r)) where
  (/) = astR2K DivideOp
  recip = astR1K RecipOp
  {-# INLINE fromRational #-}
  fromRational r = fromPlain $ AstConcreteK (fromRational r)

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Floating (AstTensor AstMethodShare s (TKScalar r)) where
  pi = error "pi is not defined for tensors"
  exp = astR1K ExpOp
  log = astR1K LogOp
  sqrt = astR1K SqrtOp
  (**) = astR2K PowerOp
  logBase = astR2K LogBaseOp
  sin = astR1K SinOp
  cos = astR1K CosOp
  tan = astR1K TanOp
  asin = astR1K AsinOp
  acos = astR1K AcosOp
  atan = astR1K AtanOp
  sinh = astR1K SinhOp
  cosh = astR1K CoshOp
  tanh = astR1K TanhOp
  asinh = astR1K AsinhOp
  acosh = astR1K AcoshOp
  atanh = astR1K AtanhOp

instance (NumScalar r, Differentiable r, KnownSpan s)
         => RealFloatH (AstTensor AstMethodShare s (TKScalar r)) where
  atan2H = astR2K Atan2Op

astR1K :: (NumScalar r, Differentiable r, KnownSpan s)
       => OpCode1 -> AstTensor AstMethodShare s (TKScalar r)
       -> AstTensor AstMethodShare s (TKScalar r)
astR1K opCode = \case
  AstCond b n k -> AstCond b (astR1K opCode n) (astR1K opCode k)
  AstPrimalPart u -> primalPart $ astR1K opCode u
  AstPlainPart u -> plainPart $ astR1K opCode u
  AstFromPrimal u -> fromPrimal $ astR1K opCode u
  AstFromPlain u -> fromPlain $ astR1K opCode u
  AstConcreteK u -> case opCode of
    RecipOp -> AstConcreteK $ recip u
    ExpOp -> AstConcreteK $ exp u
    LogOp -> AstConcreteK $ log u
    SqrtOp -> AstConcreteK $ sqrt u
    SinOp -> AstConcreteK $ sin u
    CosOp -> AstConcreteK $ cos u
    TanOp -> AstConcreteK $ tan u
    AsinOp -> AstConcreteK $ asin u
    AcosOp -> AstConcreteK $ acos u
    AtanOp -> AstConcreteK $ atan u
    SinhOp -> AstConcreteK $ sinh u
    CoshOp -> AstConcreteK $ cosh u
    TanhOp -> AstConcreteK $ tanh u
    AsinhOp -> AstConcreteK $ asinh u
    AcoshOp -> AstConcreteK $ acosh u
    AtanhOp -> AstConcreteK $ atanh u
  u -> AstR1K opCode u

astR2K :: (NumScalar r, Differentiable r, KnownSpan s)
       => OpCode2 -> AstTensor AstMethodShare s (TKScalar r)
       -> AstTensor AstMethodShare s (TKScalar r)
       -> AstTensor AstMethodShare s (TKScalar r)
astR2K opCode = \cases
  (AstPrimalPart u) (AstPrimalPart v) -> primalPart $ astR2K opCode u v
  (AstPlainPart @_ @s1 u) (AstPlainPart @_ @s2 v)
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) ->
      plainPart $ astR2K opCode u v
  (AstFromPrimal u) (AstFromPrimal v) -> fromPrimal $ astR2K opCode u v
  (AstFromPlain u) (AstFromPlain v) -> fromPlain $ astR2K opCode u v
  (AstConcreteK u) (AstConcreteK v) -> case opCode of
    DivideOp -> AstConcreteK $ u / v
    PowerOp -> AstConcreteK $ u ** v
    LogBaseOp -> AstConcreteK $ logBase u v
    Atan2Op -> AstConcreteK $ atan2H u v
  u v -> AstR2K opCode u v


-- * Unlawful numeric instances for shaped AST; lawful modulo evaluation

instance (NumScalar r, KnownSpan s)
         => Num (AstTensor AstMethodShare s (TKS sh r)) where
  u + v | FTKS (snat :$$ sh) x <- ftkAst u
        , Just u0 <- unRepl1 u
        , Just v0 <- unRepl1 v =
    AstReplicate snat (STKS sh (ftkToSTK x)) $ u0 + v0
  AstPrimalPart u + AstPrimalPart v = primalPart $ u + v
  AstDualPart u + AstDualPart v = dualPart $ u + v
  AstPlainPart @_ @s1 u + AstPlainPart @_ @s2 v
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
      plainPart $ u + v
  AstFromPrimal u + AstFromPrimal v = fromPrimal $ u + v
  AstFromDual u + AstFromDual v = fromDual $ u + v
  AstFromPlain u + AstFromPlain v = fromPlain $ u + v
  z + u | Just 0 <- unReplC z = u
  u + z | Just 0 <- unReplC z = u
  AstConcreteS n + AstConcreteS k = AstConcreteS (n + k)
  AstConcreteS n + AstPlusS (AstConcreteS k) u =
    AstPlusS (AstConcreteS (n + k)) u
  AstPlusS (AstConcreteS n) u + AstConcreteS k =
    AstPlusS (AstConcreteS (n + k)) u
  AstPlusS (AstConcreteS n) u + AstPlusS (AstConcreteS k) v =
    AstPlusS (AstConcreteS (n + k)) (AstPlusS u v)
  AstFromPlain (AstConcreteS n) + AstPlusS (AstFromPlain (AstConcreteS k)) u =
    AstPlusS (AstFromPlain (AstConcreteS (n + k))) u
  AstPlusS (AstFromPlain (AstConcreteS n)) u + AstFromPlain (AstConcreteS k) =
    AstPlusS (AstFromPlain (AstConcreteS (n + k))) u
  AstPlusS (AstFromPlain (AstConcreteS n)) u
    + AstPlusS (AstFromPlain (AstConcreteS k)) v =
      AstPlusS (AstFromPlain (AstConcreteS (n + k))) (AstPlusS u v)
  AstConvUpSFromK u + AstConvUpSFromK v = cAstConvUpSFromK $ u + v
  u + AstConvUpSFromK v = cAstConvUpSFromK $ cAstConvDownKFromS u + v
  AstConvUpSFromK u + v = cAstConvUpSFromK $ u + cAstConvDownKFromS v

--  AstN1S NegateOp (AstVar var) + AstVar var'
--    | var == var' = 0
  AstN1S NegateOp (AstVar var) + AstPlusS (AstVar var') u
    | var == var' = u
--  AstVar var' + AstN1S NegateOp (AstVar var)
--    | var == var' = 0
  AstVar var' + AstPlusS (AstN1S NegateOp (AstVar var)) u
    | var == var' = u

  AstPlusS u@AstConcreteS{} v + w = AstPlusS u (AstPlusS v w)
  u + v@AstConcreteS{} = AstPlusS v u
  u + AstPlusS v@AstConcreteS{} w = AstPlusS v (AstPlusS u w)
  AstPlusS u@(AstFromPlain (AstConcreteS{})) v + w = AstPlusS u (AstPlusS v w)
  u + v@(AstFromPlain (AstConcreteS{})) = AstPlusS v u
  u + AstPlusS v@(AstFromPlain (AstConcreteS{})) w = AstPlusS v (AstPlusS u w)
  u + v = AstPlusS u v

  u * v | FTKS (snat :$$ sh) x <- ftkAst u
        , Just u0 <- unRepl1 u
        , Just v0 <- unRepl1 v =
    AstReplicate snat (STKS sh (ftkToSTK x)) $ u0 * v0
  AstPrimalPart u * AstPrimalPart v = primalPart $ u * v
  AstPlainPart @_ @s1 u * AstPlainPart @_ @s2 v
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
      plainPart $ u * v
  AstFromPrimal u * AstFromPrimal v = fromPrimal $ u * v
--  AstFromDual{} * AstFromDual{} = 0
  AstFromPlain u * AstFromPlain v = fromPlain $ u * v
  z * _ | Just 0 <- unReplC z = z
  _ * z | Just 0 <- unReplC z = z
  s * u | Just 1 <- unReplC s = u
  u * s | Just 1 <- unReplC s = u
  AstConcreteS n * AstConcreteS k = AstConcreteS (n * k)
  AstConcreteS n * AstTimesS (AstConcreteS k) u =
    AstTimesS (AstConcreteS (n * k)) u
  AstTimesS (AstConcreteS n) u * AstConcreteS k =
    AstTimesS (AstConcreteS (n * k)) u
  AstTimesS (AstConcreteS n) u * AstTimesS (AstConcreteS k) v =
    AstTimesS (AstConcreteS (n * k)) (AstTimesS u v)
  AstFromPlain (AstConcreteS n) * AstTimesS (AstFromPlain (AstConcreteS k)) u =
    AstTimesS (AstFromPlain (AstConcreteS (n * k))) u
  AstTimesS (AstFromPlain (AstConcreteS n)) u * AstFromPlain (AstConcreteS k) =
    AstTimesS (AstFromPlain (AstConcreteS (n * k))) u
  AstTimesS (AstFromPlain (AstConcreteS n)) u
    * AstTimesS (AstFromPlain (AstConcreteS k)) v =
      AstTimesS (AstFromPlain (AstConcreteS (n * k))) (AstTimesS u v)
  AstScatterS shm shn shp v (vars, ix) * u
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      AstScatterS shm shn shp (v * cAstReplicateNS0 shv w) (vars, ix)
  AstScatterS shm shn shp v (vars, ix) * AstTimesS u a
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      AstScatterS shm shn shp (v * cAstReplicateNS0 shv w) (vars, ix) * a
  AstTimesS a (AstScatterS shm shn shp v (vars, ix)) * u
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      a * AstScatterS shm shn shp (v * cAstReplicateNS0 shv w) (vars, ix)
  u * AstScatterS shm shn shp v (vars, ix)
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      AstScatterS shm shn shp (cAstReplicateNS0 shv w * v) (vars, ix)
  u * AstTimesS (AstScatterS shm shn shp v (vars, ix)) a
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      AstScatterS shm shn shp (cAstReplicateNS0 shv w * v) (vars, ix) * a
  AstTimesS a u * AstScatterS shm shn shp v (vars, ix)
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      a * AstScatterS shm shn shp (cAstReplicateNS0 shv w * v) (vars, ix)
  AstGatherS shm shn shp v (vars, ix) * u
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      AstGatherS shm shn shp (v * cAstReplicateNS0 shv w) (vars, ix)
  AstGatherS shm shn shp v (vars, ix) * AstTimesS u a
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      AstGatherS shm shn shp (v * cAstReplicateNS0 shv w) (vars, ix) * a
  AstTimesS a (AstGatherS shm shn shp v (vars, ix)) * u
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      a * AstGatherS shm shn shp (v * cAstReplicateNS0 shv w) (vars, ix)
  u * AstGatherS shm shn shp v (vars, ix)
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      AstGatherS shm shn shp (cAstReplicateNS0 shv w * v) (vars, ix)
  u * AstTimesS (AstGatherS shm shn shp v (vars, ix)) a
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      AstGatherS shm shn shp (cAstReplicateNS0 shv w * v) (vars, ix) * a
  AstTimesS a u * AstGatherS shm shn shp v (vars, ix)
    | Just w <- unRepl u, FTKS shv _ <- ftkAst v =
      a * AstGatherS shm shn shp (cAstReplicateNS0 shv w * v) (vars, ix)
  AstConvUpSFromK u * AstConvUpSFromK v = cAstConvUpSFromK $ u * v
  u * AstConvUpSFromK v = cAstConvUpSFromK $ cAstConvDownKFromS u * v
  AstConvUpSFromK u * v = cAstConvUpSFromK $ u * cAstConvDownKFromS v

  -- This breaks sharing, because although u is concrete and so doesn't
  -- have to be shared, the multiplication is not shared --- we end up
  -- with one addition and two multiplications, not one. Similarly below.
  -- u@AstConcreteS{} * AstPlusS v w = AstPlusS (u * v) (u * w)
  -- AstTimesS u@AstConcreteS{} x * AstPlusS v w =
  --   AstTimesS x (AstPlusS (u * v) (u * w))
  -- AstPlusS v w * u@AstConcreteS{} = AstPlusS (v * u) (w * u)
  -- AstPlusS v w * AstTimesS u@AstConcreteS{} x =
  --   AstTimesS (AstPlusS (v * u) (w * u)) x
  -- u@(AstFromPlain (AstConcreteS{})) * AstPlusS v w = AstPlusS (u * v) (u * w)
  -- AstTimesS u@(AstFromPlain (AstConcreteS{})) x * AstPlusS v w =
  --   AstTimesS x (AstPlusS (u * v) (u * w))
  -- AstPlusS v w * u@(AstFromPlain (AstConcreteS{})) = AstPlusS (v * u) (w * u)
  -- AstPlusS v w * AstTimesS u@(AstFromPlain (AstConcreteS{})) x =
  --   AstTimesS (AstPlusS (v * u) (w * u)) x

  AstN1S NegateOp u * AstN1S NegateOp v = AstTimesS u v

  AstTimesS u@AstConcreteS{} v * w = AstTimesS u (AstTimesS v w)
  u * v@AstConcreteS{} = AstTimesS v u
  u * AstTimesS v@AstConcreteS{} w = AstTimesS v (AstTimesS u w)
  AstTimesS u@(AstFromPlain (AstConcreteS{})) v * w =
    AstTimesS u (AstTimesS v w)
  u * v@(AstFromPlain (AstConcreteS{})) = AstTimesS v u
  u * AstTimesS v@(AstFromPlain (AstConcreteS{})) w =
    AstTimesS v (AstTimesS u w)
  u * v = AstTimesS u v

  negate u | FTKS (snat :$$ sh) x <- ftkAst u
           , Just u0 <- unRepl1 u =
    AstReplicate snat (STKS sh (ftkToSTK x)) (negate u0)
  negate (AstCond b n k) = AstCond b (negate n) (negate k)
-- TODO: negate (AstBuild1 k stk (var, v)) = AstBuild1 k stk (var, negate v)
  negate (AstPrimalPart n) = primalPart (negate n)
  negate (AstDualPart n) = dualPart (negate n)
  negate (AstPlainPart n) = plainPart (negate n)
  negate (AstFromPrimal n) = fromPrimal (negate n)
  negate (AstFromDual n) = fromDual (negate n)
  negate (AstFromPlain n) = fromPlain (negate n)
  negate (AstPlusS u v) = AstPlusS (negate u) (negate v)
  negate (AstTimesS u v) = AstTimesS (negate u) v
  negate (AstN1S NegateOp u) = u
  negate (AstN1S SignumOp u) = AstN1S SignumOp (negate u)
  negate (AstI2S QuotOp u v) = AstI2S QuotOp (negate u) v
    -- v is likely positive and let's keep it so
  negate (AstI2S RemOp u v) = AstI2S RemOp (negate u) v
    -- v is likely positive and let's keep it so
  negate (AstConcreteS n) = AstConcreteS (negate n)
  negate (AstScatterS shm shn shp v (vars, ix)) =
    AstScatterS shm shn shp (negate v) (vars, ix)
  negate (AstGatherS shm shn shp v (vars, ix)) =
    AstGatherS shm shn shp (negate v) (vars, ix)
  negate (AstConvUpSFromK n) = cAstConvUpSFromK $ negate n
  negate u = AstN1S NegateOp u
  abs u | FTKS (snat :$$ sh) x <- ftkAst u
        , Just u0 <- unRepl1 u =
    AstReplicate snat (STKS sh (ftkToSTK x)) (abs u0)
  abs (AstPrimalPart n) = primalPart (abs n)
  abs (AstDualPart n) = dualPart (abs n)
  abs (AstPlainPart n) = plainPart (abs n)
  abs (AstFromPrimal n) = fromPrimal (abs n)
  abs (AstFromDual n) = fromDual (abs n)
  abs (AstFromPlain n) = fromPlain (abs n)
  abs (AstN1S NegateOp u) = abs u
  abs (AstN1S AbsOp u) = AstN1S AbsOp u
  abs (AstConcreteS u) = AstConcreteS (abs u)
  abs (AstConvUpSFromK n) = cAstConvUpSFromK $ abs n
  abs u = AstN1S AbsOp u
  signum u | FTKS (snat :$$ sh) x <- ftkAst u
           , Just u0 <- unRepl1 u =
    AstReplicate snat (STKS sh (ftkToSTK x)) (signum u0)
  signum (AstPrimalPart n) = primalPart (signum n)
  signum (AstDualPart n) = dualPart (signum n)
  signum (AstPlainPart n) = plainPart (signum n)
  signum (AstFromPrimal n) = fromPrimal (signum n)
  signum (AstFromDual n) = fromDual (signum n)
  signum (AstFromPlain n) = fromPlain (signum n)
  signum (AstN1S SignumOp u) = AstN1S SignumOp u
  signum (AstConcreteS u) = AstConcreteS (signum u)
  signum (AstConvUpSFromK n) = cAstConvUpSFromK $ signum n
  signum u = AstN1S SignumOp u
  fromInteger i = error $ "fromInteger is not defined for shaped tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r, KnownSpan s)
         => IntegralH (AstTensor AstMethodShare s (TKS sh r)) where
  quotH u v | FTKS (SNat :$$ sh) x <- ftkAst u
            , Just u0 <- unRepl1 u
            , Just v0 <- unRepl1 v =
    AstReplicate SNat (STKS sh (ftkToSTK x)) $ quotH u0 v0
  quotH (AstPrimalPart n) (AstPrimalPart k) = primalPart (quotH n k)
  quotH (AstPlainPart @_ @s1 n) (AstPlainPart @_ @s2 k)
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
      plainPart (quotH n k)
  quotH (AstFromPrimal n) (AstFromPrimal k) = fromPrimal (quotH n k)
  quotH (AstFromPlain n) (AstFromPlain k) = fromPlain (quotH n k)
  quotH z _ | Just 0 <- unReplC z = z
  quotH u s | Just 1 <- unReplC s = u
  quotH (AstConcreteS n) (AstConcreteS k) = AstConcreteS (quotH n k)
  quotH (AstConvUpSFromK n) (AstConvUpSFromK k) = cAstConvUpSFromK $ quotH n k
  quotH n (AstConvUpSFromK k) =
    cAstConvUpSFromK $ quotH (cAstConvDownKFromS n) k
  quotH (AstConvUpSFromK n) k =
    cAstConvUpSFromK $ quotH n (cAstConvDownKFromS k)
  quotH (AstI2S QuotOp u v) w = quotH u (v * w)
  quotH u v = AstI2S QuotOp u v

  remH u v | FTKS (SNat :$$ sh) x <- ftkAst u
           , Just u0 <- unRepl1 u
           , Just v0 <- unRepl1 v =
    AstReplicate SNat (STKS sh (ftkToSTK x)) $ remH u0 v0
  remH (AstPrimalPart n) (AstPrimalPart k) = primalPart (remH n k)
  remH (AstPlainPart @_ @s1 n) (AstPlainPart @_ @s2 k)
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) =
      plainPart (remH n k)
  remH (AstFromPrimal n) (AstFromPrimal k) = fromPrimal (remH n k)
  remH (AstFromPlain n) (AstFromPlain k) = fromPlain (remH n k)
  remH z _ | Just 0 <- unReplC z = z
  remH (AstConcreteS n) (AstConcreteS k) = AstConcreteS (remH n k)
  remH (AstConvUpSFromK n) (AstConvUpSFromK k) = cAstConvUpSFromK $ remH n k
  remH n (AstConvUpSFromK k) = cAstConvUpSFromK $ remH (cAstConvDownKFromS n) k
  remH (AstConvUpSFromK n) k = cAstConvUpSFromK $ remH n (cAstConvDownKFromS k)
--  remH _ (AstConcreteS s) | Just 1 <- sunReplicatePrim s = AstConcreteS 0
  remH u v = AstI2S RemOp u v

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Fractional (AstTensor AstMethodShare s (TKS sh r)) where
  (/) = astR2S DivideOp
  recip = astR1S RecipOp
  fromRational r = error $ "fromRational is not defined for shaped tensors: "
                           ++ show r

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Floating (AstTensor AstMethodShare s (TKS sh r)) where
  pi = error "pi is not defined for tensors"
  exp = astR1S ExpOp
  log = astR1S LogOp
  sqrt = astR1S SqrtOp
  (**) = astR2S PowerOp
  logBase = astR2S LogBaseOp
  sin = astR1S SinOp
  cos = astR1S CosOp
  tan = astR1S TanOp
  asin = astR1S AsinOp
  acos = astR1S AcosOp
  atan = astR1S AtanOp
  sinh = astR1S SinhOp
  cosh = astR1S CoshOp
  tanh = astR1S TanhOp
  asinh = astR1S AsinhOp
  acosh = astR1S AcoshOp
  atanh = astR1S AtanhOp

instance (NumScalar r, Differentiable r, KnownSpan s)
         => RealFloatH (AstTensor AstMethodShare s (TKS sh r)) where
  atan2H = astR2S Atan2Op

astR1S :: (NumScalar r, Differentiable r, KnownSpan s)
       => OpCode1 -> AstTensor AstMethodShare s (TKS sh r)
       -> AstTensor AstMethodShare s (TKS sh r)
astR1S opCode = \case
  u | FTKS (snat :$$ sh) x <- ftkAst u
    , Just u0 <- unRepl1 u ->
      AstReplicate snat (STKS sh (ftkToSTK x)) $ astR1S opCode u0
  AstCond b n k -> AstCond b (astR1S opCode n) (astR1S opCode k)
  AstPrimalPart u -> primalPart $ astR1S opCode u
  AstPlainPart u -> plainPart $ astR1S opCode u
  AstFromPrimal u -> fromPrimal $ astR1S opCode u
  AstFromPlain u -> fromPlain $ astR1S opCode u
  AstConvUpSFromK n -> cAstConvUpSFromK $ astR1K opCode n
  AstConcreteS u -> case opCode of
    RecipOp -> AstConcreteS $ recip u
    ExpOp -> AstConcreteS $ exp u
    LogOp -> AstConcreteS $ log u
    SqrtOp -> AstConcreteS $ sqrt u
    SinOp -> AstConcreteS $ sin u
    CosOp -> AstConcreteS $ cos u
    TanOp -> AstConcreteS $ tan u
    AsinOp -> AstConcreteS $ asin u
    AcosOp -> AstConcreteS $ acos u
    AtanOp -> AstConcreteS $ atan u
    SinhOp -> AstConcreteS $ sinh u
    CoshOp -> AstConcreteS $ cosh u
    TanhOp -> AstConcreteS $ tanh u
    AsinhOp -> AstConcreteS $ asinh u
    AcoshOp -> AstConcreteS $ acosh u
    AtanhOp -> AstConcreteS $ atanh u
  u -> AstR1S opCode u

astR2S :: (NumScalar r, Differentiable r, KnownSpan s)
       => OpCode2 -> AstTensor AstMethodShare s (TKS sh r)
       -> AstTensor AstMethodShare s (TKS sh r)
       -> AstTensor AstMethodShare s (TKS sh r)
astR2S opCode = \cases
  u v | FTKS (SNat :$$ sh) x <- ftkAst u
      , Just u0 <- unRepl1 u
      , Just v0 <- unRepl1 v ->
        AstReplicate SNat (STKS sh (ftkToSTK x)) $ astR2S opCode u0 v0
  (AstPrimalPart u) (AstPrimalPart v) -> primalPart $ astR2S opCode u v
  (AstPlainPart @_ @s1 u) (AstPlainPart @_ @s2 v)
    | Just Refl <- testEquality (knownSpan @s1) (knownSpan @s2) ->
      plainPart $ astR2S opCode u v
  (AstFromPrimal u) (AstFromPrimal v) -> fromPrimal $ astR2S opCode u v
  (AstFromPlain u) (AstFromPlain v) -> fromPlain $ astR2S opCode u v
  (AstConvUpSFromK n) (AstConvUpSFromK k) ->
    cAstConvUpSFromK $ astR2K opCode n k
  n (AstConvUpSFromK k) ->
    cAstConvUpSFromK $ astR2K opCode (cAstConvDownKFromS n) k
  (AstConvUpSFromK n) k ->
    cAstConvUpSFromK $ astR2K opCode n (cAstConvDownKFromS k)
  (AstConcreteS u) (AstConcreteS v) -> case opCode of
    DivideOp -> AstConcreteS $ u / v
    PowerOp -> AstConcreteS $ u ** v
    LogBaseOp -> AstConcreteS $ logBase u v
    Atan2Op -> AstConcreteS $ atan2H u v
  u v -> AstR2S opCode u v


-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

-- Simple variable comparisons, if any, come first.
instance Boolean (AstBool AstMethodShare) where
  true = AstConcreteK True
  false = AstConcreteK False
  notB = AstBoolNotK
  (&&*) = AstBoolAndK
  b ||* c = notB (notB b &&* notB c)

-- Since u and v are duplicated here, they need to be shared.
-- We share their difference, which would most likely appear in the
-- inequalities once they are rewritten, to ensure it's shared and whatever
-- vectorization substitutes into it is shared as well.
-- Otherwise, if u and v are variables, the sharing would vanish
-- before vectoriation complicates the expression a bit, making it
-- worth sharing.
instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodShare s) (TKScalar r) where
  v ==. u | eqK v u = true
  vUnshared ==. uUnshared =
    let uv = astShareNoSimplify (uUnshared - vUnshared)
    in 0 <=. uv &&* uv <=. 0

instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodShare s) (TKS sh r) where
  vUnshared ==. uUnshared =
    let uv = astShareNoSimplify (uUnshared - vUnshared)
        zero = fromPlain $ AstConcreteS $ defTargetRep $ ftkAst vUnshared
    in zero <=. uv &&* uv <=. zero

instance (KnownSpan s, NumScalar r)
         => OrdH (AstTensor AstMethodShare s) (TKScalar r) where
  v <=. u = AstLeqK (plainPart v) (plainPart u)

instance (KnownSpan s, NumScalar r)
         => OrdH (AstTensor AstMethodShare s) (TKS sh r) where
  v <=. u = AstLeq (plainPart v) (plainPart u)


-- * Unlawful numeric instances for ranked AST; lawful modulo evaluation

instance (NumScalar r, KnownSpan s)
         => Num (AstTensor AstMethodShare s (TKR n r)) where
  (+) = liftRFromS2 (+)
  (-) = liftRFromS2 (-)
  (*) = liftRFromS2 (*)
  negate = liftRFromS1 negate
  abs = liftRFromS1 abs
  signum = liftRFromS1 signum
  fromInteger i = error $ "fromInteger is not defined for ranked tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r, KnownSpan s)
         => IntegralH (AstTensor AstMethodShare s (TKR n r)) where
  quotH = liftRFromS2 quotH
  remH = liftRFromS2 remH

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Fractional (AstTensor AstMethodShare s (TKR n r)) where
  (/) = liftRFromS2 (/)
  recip = liftRFromS1 recip
  fromRational r = error $ "fromRational is not defined for ranked tensors: "
                           ++ show r

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Floating (AstTensor AstMethodShare s (TKR n r)) where
  pi = error "pi is not defined for tensors"
  exp = liftRFromS1 exp
  log = liftRFromS1 log
  sqrt = liftRFromS1 sqrt
  (**) = liftRFromS2 (**)
  logBase = liftRFromS2 logBase
  sin = liftRFromS1 sin
  cos = liftRFromS1 cos
  tan = liftRFromS1 tan
  asin = liftRFromS1 asin
  acos = liftRFromS1 acos
  atan = liftRFromS1 atan
  sinh = liftRFromS1 sinh
  cosh = liftRFromS1 cosh
  tanh = liftRFromS1 tanh
  asinh = liftRFromS1 asinh
  acosh = liftRFromS1 acosh
  atanh = liftRFromS1 atanh

instance (NumScalar r, Differentiable r, KnownSpan s)
         => RealFloatH (AstTensor AstMethodShare s (TKR n r)) where
  atan2H = liftRFromS2 atan2H

instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodShare s) (TKR n r) where
  v ==. u = case ftkAst v of
    FTKR shv' x -> case ftkAst u of
      FTKR shu' _ ->
        withShsFromShR shv' $ \shv ->
          withShsFromShR shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstConvDownSFromR shu x v ==. cAstConvDownSFromR shv x u
              _ -> error $ "(==.): shapes don't match: "
                           ++ show (shu, shv)

instance (KnownSpan s, NumScalar r)
         => OrdH (AstTensor AstMethodShare s) (TKR n r) where
  v <=. u = case ftkAst v of
    FTKR shv' x -> case ftkAst u of
      FTKR shu' _ ->
        withShsFromShR shv' $ \shv ->
          withShsFromShR shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstConvDownSFromR shu x v <=. cAstConvDownSFromR shv x u
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)


-- * Unlawful numeric instances for mixed AST; lawful modulo evaluation

instance (NumScalar r, KnownSpan s)
         => Num (AstTensor AstMethodShare s (TKX sh r)) where
  (+) = liftXFromS2 (+)
  (-) = liftXFromS2 (-)
  (*) = liftXFromS2 (*)
  negate = liftXFromS1 negate
  abs = liftXFromS1 abs
  signum = liftXFromS1 signum
  fromInteger i = error $ "fromInteger is not defined for mixed tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r, KnownSpan s)
         => IntegralH (AstTensor AstMethodShare s (TKX sh r)) where
  quotH = liftXFromS2 quotH
  remH = liftXFromS2 remH

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Fractional (AstTensor AstMethodShare s (TKX sh r)) where
  (/) = liftXFromS2 (/)
  recip = liftXFromS1 recip
  fromRational r = error $ "fromRational is not defined for mixed tensors: "
                           ++ show r

instance (NumScalar r, Differentiable r, KnownSpan s)
         => Floating (AstTensor AstMethodShare s (TKX sh r)) where
  pi = error "pi is not defined for tensors"
  exp = liftXFromS1 exp
  log = liftXFromS1 log
  sqrt = liftXFromS1 sqrt
  (**) = liftXFromS2 (**)
  logBase = liftXFromS2 logBase
  sin = liftXFromS1 sin
  cos = liftXFromS1 cos
  tan = liftXFromS1 tan
  asin = liftXFromS1 asin
  acos = liftXFromS1 acos
  atan = liftXFromS1 atan
  sinh = liftXFromS1 sinh
  cosh = liftXFromS1 cosh
  tanh = liftXFromS1 tanh
  asinh = liftXFromS1 asinh
  acosh = liftXFromS1 acosh
  atanh = liftXFromS1 atanh

instance (NumScalar r, Differentiable r, KnownSpan s)
         => RealFloatH (AstTensor AstMethodShare s (TKX sh r)) where
  atan2H = liftXFromS2 atan2H

instance (KnownSpan s, NumScalar r)
         => EqH (AstTensor AstMethodShare s) (TKX sh r) where
  v ==. u = case ftkAst v of
    FTKX shv' x -> case ftkAst u of
      FTKX shu' _ ->
        withShsFromShX shv' $ \shv ->
          withShsFromShX shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstConvDownSFromX shu x v ==. cAstConvDownSFromX shv x u
              _ -> error $ "(==.): shapes don't match: "
                           ++ show (shu, shv)

instance (KnownSpan s, NumScalar r)
         => OrdH (AstTensor AstMethodShare s) (TKX sh r) where
  v <=. u = case ftkAst v of
    FTKX shv' x -> case ftkAst u of
      FTKX shu' _ ->
        withShsFromShX shv' $ \shv ->
          withShsFromShX shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstConvDownSFromX shu x v <=. cAstConvDownSFromX shv x u
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)


-- * AstRaw instances

instance Boolean (AstRaw PlainSpan (TKScalar Bool)) where
  true = AstRaw true
  false = AstRaw false
  notB b = AstRaw (notB $ unAstRaw b)
  b &&* c = AstRaw (unAstRaw b &&* unAstRaw c)
  b ||* c = AstRaw (unAstRaw b ||* unAstRaw c)

instance (EqH (AstTensor AstMethodShare s) y)
         => EqH (AstRaw s) y where
  AstRaw v ==. AstRaw u = AstRaw $ v ==. u
instance (OrdH (AstTensor AstMethodShare s) y)
         => OrdH (AstRaw s) y where
  AstRaw v <=. AstRaw u = AstRaw $ v <=. u

deriving instance Eq (AstRaw s y)
deriving instance Ord (AstRaw s y)
deriving instance Num (AstTensor AstMethodShare s y) => Num (AstRaw s y)
deriving instance IntegralH (AstTensor AstMethodShare s y)
                  => IntegralH (AstRaw s y)
deriving instance Fractional (AstTensor AstMethodShare s y)
                  => Fractional (AstRaw s y)
deriving instance Floating (AstTensor AstMethodShare s y)
                  => Floating (AstRaw s y)
deriving instance RealFloatH (AstTensor AstMethodShare s y)
                  => RealFloatH (AstRaw s y)


-- * Misc

astShareNoSimplify :: KnownSpan s
                   => AstTensor AstMethodShare s y
                   -> AstTensor AstMethodShare s y
{-# NOINLINE astShareNoSimplify #-}
astShareNoSimplify a | astIsSmall True a = a
                         -- too important an optimization to skip
astShareNoSimplify a = case a of
  AstFromPrimal v -> fromPrimal $ astShareNoSimplify v
  AstFromDual v -> fromDual $ astShareNoSimplify v
  AstFromPlain v -> fromPlain $ astShareNoSimplify v
  _ -> unsafePerformIO $ case ftkAst a of
    ftk@FTKScalar -> do
        var <- funToAstAutoBoundsIO ftk a
        pure $! astShare var a
    FTKR sh' x ->
      withShsFromShR sh' $ \(sh :: ShS sh) -> do
        let v = cAstConvDownSFromR sh x a
        var <- funToAstNoBoundsIO (FTKS sh x)
        pure $! cAstConvUpRFromS sh x $ astShare var v
    FTKX sh' x ->
      withShsFromShX sh' $ \(sh :: ShS sh) -> do
        let v = cAstConvDownSFromX sh x a
        var <- funToAstNoBoundsIO (FTKS sh x)
        pure $! cAstConvUpXFromS sh' x $ astShare var v
    FTKS ZSS x@FTKScalar -> do
        let v = cAstConvDownKFromS a
        var <- funToAstAutoBoundsIO x v
        pure $! cAstConvUpSFromK $ astShare var v
    -- calling recursively for product may be not worth it
    ftk -> do
        var <- funToAstNoBoundsIO ftk
        pure $! astShare var a

cAstReplicateNS0 :: forall shn x s ms.
                    ShS shn -> AstTensor ms s (TKS2 '[] x)
                 -> AstTensor ms s (TKS2 shn x)
cAstReplicateNS0 shn v | STKS _ x <- ftkToSTK (ftkAst v) =
  let go :: ShS shn2 -> AstTensor ms s (TKS2 shn2 x)
      go ZSS = v
      go (snat :$$ shn3) = AstReplicate snat (STKS shn3 x) $ go shn3
  in go shn

sunReplicatePrim :: Nested.Elt a
                 => Nested.Shaped sh a -> Maybe a
{-# INLINE sunReplicatePrim #-}
sunReplicatePrim (Nested.Shaped arr)
  | all (all (== 0) . take (shxLength (Nested.mshape arr)))
        (Mixed.marrayStrides arr)
  , shxSize (Nested.mshape arr) /= 0 =
    Just $ Nested.mindex arr $ ixxZero' $ Nested.mshape arr
sunReplicatePrim arr | ZSS <- Nested.sshape arr = Just $ Nested.sunScalar arr
sunReplicatePrim _ = Nothing

sunReplicate1 :: Nested.Elt a
              => Nested.Shaped (n ': sh) a -> Maybe (Nested.Shaped sh a)
{-# INLINE sunReplicate1 #-}
sunReplicate1 a | (snat :$$ _) <- Nested.sshape a =
  sunReplicateN (snat :$$ ZSS) a

sunReplicateN :: Nested.Elt a
              => ShS shm -> Nested.Shaped (shm ++ shn) a
              -> Maybe (Nested.Shaped shn a)
{-# INLINE sunReplicateN #-}
sunReplicateN shm a@(Nested.Shaped arr)
  | all (all (== 0) . take (shsLength shm)) (Mixed.marrayStrides arr)
  , shsSize shm /= 0 =
    Just $ Nested.sindexPartial a $ ixsZero shm
sunReplicateN _ _ = Nothing

unReplC :: forall sh r s ms. KnownSpan s
        => AstTensor ms s (TKS sh r) -> Maybe r
unReplC (AstReplicate _ _ (AstConcreteK a)) = Just a
unReplC (AstReplicate _ STKS{} u) = unReplC u
unReplC (AstConcreteS a) = sunReplicatePrim a
unReplC (AstLet _ _ t) = unReplC t
unReplC (AstPrimalPart t) = unReplC t
unReplC (AstDualPart t) = unReplC t
unReplC (AstPlainPart t) = unReplC t
unReplC (AstFromPrimal t) = unReplC t
unReplC (AstFromDual t) = unReplC t
unReplC (AstFromPlain t) = unReplC t
unReplC (AstConvert (ConvCmp ConvXS (Conv0X STKScalar)) (AstConcreteK a)) =
  Just a
unReplC _ = Nothing

unRepl1 :: forall n sh x s ms. KnownSpan s
        => AstTensor ms s (TKS2 (n ': sh) x)
        -> Maybe (AstTensor ms s (TKS2 sh x))
unRepl1 (AstReplicate _ STKScalar u) = Just $ cAstConvUpSFromK u
unRepl1 (AstReplicate _ STKS{} u) = Just u
unRepl1 (AstConcreteS a) = AstConcreteS <$> sunReplicate1 a
unRepl1 (AstLet var u t) = AstLet var u <$> unRepl1 t
unRepl1 (AstPrimalPart t) = primalPart <$> unRepl1 t
unRepl1 (AstDualPart t) = dualPart <$> unRepl1 t
unRepl1 (AstPlainPart t) = plainPart <$> unRepl1 t
unRepl1 (AstFromPrimal t) = fromPrimal <$> unRepl1 t
unRepl1 (AstFromDual t) = fromDual <$> unRepl1 t
unRepl1 (AstFromPlain t) = fromPlain <$> unRepl1 t
unRepl1 _ = Nothing

-- The result must not be equal to the argument.
unRepl :: forall sh x s ms. KnownSpan s
       => AstTensor ms s (TKS2 sh x)
       -> Maybe (AstTensor ms s (TKS2 '[] x))
-- This is too costly and not needed in all the places where unRepl is used,
-- hence the restriction to different result and argument:
-- unRepl t | FTKS ZSS _ <- ftkAst t = Just t
unRepl (AstReplicate _ (STKS ZSS _) u) = Just u
unRepl (AstReplicate _ STKScalar u) = Just $ cAstConvUpSFromK u
unRepl (AstReplicate _ STKS{} u) = unRepl u
unRepl (AstConcreteS a) | _ :$$ _ <- Nested.sshape a =
  AstConcreteS . Nested.sscalar <$> sunReplicatePrim a
unRepl (AstLet var u t) = AstLet var u <$> unRepl t
unRepl (AstPrimalPart t) = primalPart <$> unRepl t
unRepl (AstDualPart t) = dualPart <$> unRepl t
unRepl (AstPlainPart t) = plainPart <$> unRepl t
unRepl (AstFromPrimal t) = fromPrimal <$> unRepl t
unRepl (AstFromDual t) = fromDual <$> unRepl t
unRepl (AstFromPlain t) = fromPlain <$> unRepl t
unRepl _ = Nothing
