{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Definitions, mostly class instances, needed to make AST a valid
-- carrier for a tensor class algebra (instance) defined
-- in "HordeAd.Core.OpsAst".
-- This algebra permits user programs to be instantiated as AST terms,
-- as well as to be interpreted into AST terms and it also permits derivatives
-- to be expressed as AST terms.
module HordeAd.Core.CarriersAst
  ( AstRaw(..), AstNoVectorize(..), AstNoSimplify(..)
  , astLetFunNoSimplify, sunReplicateScal, sunReplicate1, sunReplicateN
  ) where

import Prelude hiding (foldl')

import Data.Int (Int64)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Foreign.C (CInt)
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
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Type family instances for AstTensor

-- This can't be just HFun, because they need to be vectorized
-- and vectorization applies such functions to the variable from build1
-- and the variable has to be eliminated via vectorization to preserve
-- the closed form of the function. Just applying a Haskell closure
-- to the build1 variable and then duplicating the result of the function
-- would not eliminate the variable and also would likely results
-- in more costly computations. Also, that would prevent simplification
-- of the instances, especially after applied to arguments that are terms.
type instance HFunOf (AstTensor AstMethodLet s) x z = AstHFun s s x z

type instance BoolOf (AstTensor ms s) = AstBool ms

-- This can't be defined only for FullSpan, because the BaseTensor instance
-- for @AstTensor ms PrimalSpan@ needs it and we need the instance
-- to satisfy ADReady constraints for AST.
type instance PrimalOf (AstTensor ms s) = AstTensor ms (PrimalStepSpan s)
type instance DualOf (AstTensor ms s) = AstTensor ms DualSpan
type instance PlainOf (AstTensor ms s) = AstTensor ms PlainSpan
type instance ShareOf (AstTensor ms s) = AstRaw s


-- * Unlawful numeric instances for AST scalars; they are lawful modulo evaluation

-- These are, unfortunately, required by some numeric instances.
instance Eq (AstTensor ms s y) where
  (==) = error "Eq is not defined for AST; please use EqH instead"
  (/=) = error "Eq is not defined for AST; please use EqH instead"

instance Ord (AstTensor ms s y) where
  (<=) = error "Ord is not defined for AST; please use OrdH instead"

-- TODO: perhaps aim for a polynomial normal form? but that requires global
-- inspection of the whole expression
-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right
-- and let's push negation down.
--
-- Not considered are rules that would require comparing non-constant terms
-- or that would duplicate a non-constant term, as well as most rules
-- informed by inequalities, expressed via max or min, such as
-- max n (signum (abs x)) | n <= 0 --> signum (abs x).
-- We could use sharing via @tlet@ if terms are duplicated, but it's
-- unclear if the term bloat is worth it and also we'd need to restrict
-- this extended simplification to AstMethodLet.
--
-- | Integer terms need to be simplified, because large ones are sometimes
-- created due to vectorization, e.g., via astTransposeAsGather
-- or astReshapeAsGather and can be a deciding factor in whether
-- the other tensor terms can be simplified in turn.
--
-- The normal form has AstConcreteK or AstFromPlain (AstConcreteK),
-- if any, as the first argument of the constructor.
-- No flattening is performed beyond that.
instance (NumScalar r, AstSpan s)
         => Num (AstTensor ms s (TKScalar r)) where
  AstPrimalPart u + AstPrimalPart v = AstPrimalPart $ u + v
  AstDualPart u + AstDualPart v = AstDualPart $ u + v
  AstPlainPart @_ @s1 u + AstPlainPart @_ @s2 v
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ u + v
  AstFromPrimal u + AstFromPrimal v = fromPrimal $ u + v
  AstFromDual u + AstFromDual v = fromDual $ u + v
  AstFromPlain u + AstFromPlain v = fromPlain $ u + v
  -- TODO: define a pattern synonym that captures the below. Also elsewhere.
  AstConvert c u + AstConvert _ v
    | FTKS ZSS x <- ftkAst u
    , FTKS ZSS y <- ftkAst v
    , Just Refl <- matchingFTK x (convertFTK c (ftkAst u))
    , Just Refl <- matchingFTK x y =
      AstConvert c $ u + v
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

  AstPrimalPart u * AstPrimalPart v = AstPrimalPart $ u * v
  AstPlainPart @_ @s1 u * AstPlainPart @_ @s2 v
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ u * v
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
  AstConvert c u * AstConvert _ v
    | FTKS ZSS x <- ftkAst u
    , FTKS ZSS y <- ftkAst v
    , Just Refl <- matchingFTK x (convertFTK c (ftkAst u))
    , Just Refl <- matchingFTK x y =
      AstConvert c $ u * v
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
  negate (AstLet var n k) = AstLet var n (negate k)
  negate (AstPrimalPart n) = AstPrimalPart (negate n)
  negate (AstDualPart n) = AstDualPart (negate n)
  negate (AstPlainPart n) = AstPlainPart (negate n)
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
  negate (AstConvert c u)
    | FTKS ZSS x <- ftkAst u
    , Just Refl <- matchingFTK x (convertFTK c (ftkAst u)) =
      AstConvert c (negate u)
  negate u = AstN1K NegateOp u
  abs (AstPrimalPart n) = AstPrimalPart (abs n)
  abs (AstDualPart n) = AstDualPart (abs n)
  abs (AstPlainPart n) = AstPlainPart (abs n)
  abs (AstFromPrimal n) = fromPrimal (abs n)
  abs (AstFromDual n) = fromDual (abs n)
  abs (AstFromPlain n) = fromPlain (abs n)
  abs (AstConcreteK n) = AstConcreteK (abs n)
  abs (AstN1K AbsOp u) = AstN1K AbsOp u
  abs (AstN1K NegateOp u) = abs u
  abs (AstConvert c u)
    | FTKS ZSS x <- ftkAst u
    , Just Refl <- matchingFTK x (convertFTK c (ftkAst u)) =
      AstConvert c (abs u)
  abs u = AstN1K AbsOp u
  signum (AstPrimalPart n) = AstPrimalPart (signum n)
  signum (AstDualPart n) = AstDualPart (signum n)
  signum (AstPlainPart n) = AstPlainPart (signum n)
  signum (AstFromPrimal n) = fromPrimal (signum n)
  signum (AstFromDual n) = fromDual (signum n)
  signum (AstFromPlain n) = fromPlain (signum n)
  signum (AstConcreteK n) = AstConcreteK (signum n)
  signum (AstN1K SignumOp u) = AstN1K SignumOp u
  signum (AstConvert c u)
    | FTKS ZSS x <- ftkAst u
    , Just Refl <- matchingFTK x (convertFTK c (ftkAst u)) =
      AstConvert c (signum u)
  signum u = AstN1K SignumOp u
  fromInteger i = fromPlain $ AstConcreteK (fromInteger i)
{- TODO: RULE left-hand side too complicated to desugar
  {-# SPECIALIZE instance Num (AstTensor ms FullSpan (TKScalar Int64)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms PrimalSpan (TKScalar Int64)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms FullSpan (TKScalar CInt)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms PrimalSpan (TKScalar CInt)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms FullSpan (TKScalar Double)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms PrimalSpan (TKScalar Double)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms FullSpan (TKScalar Float)) #-}
  {-# SPECIALIZE instance Num (AstTensor ms PrimalSpan (TKScalar Float)) #-}
-}

-- An approximation. False doesn't imply terms have different semantics,
-- but True implies they have equal semantics.
eqK :: AstTensor ms s (TKScalar r) -> AstTensor ms s (TKScalar r) -> Bool
eqK (AstVar var1) (AstVar var2) = var1 == var2
eqK (AstLet @_ @_ @s1 var1 u1 v1) (AstLet @_ @_ @s2 var2 u2 v2)
  | FTKScalar @r1 <- ftkAst u1, FTKScalar @r2 <- ftkAst u2
  , Just Refl <- testEquality (typeRep @r1) (typeRep @r2)
  , Just Refl <- sameAstSpan @s1 @s2 =
    var1 == var2 && eqK u1 u2 && eqK v1 v2
eqK (AstPrimalPart u1) (AstPrimalPart u2) = eqK u1 u2
eqK (AstDualPart u1) (AstDualPart u2) = eqK u1 u2
eqK (AstPlainPart @_ @s1 u1) (AstPlainPart @_ @s2 u2)
  | Just Refl <- sameAstSpan @s1 @s2 =
    eqK u1 u2
eqK (AstFromPrimal u1) (AstFromPrimal u2) = eqK u1 u2
eqK (AstFromDual u1) (AstFromDual u2) = eqK u1 u2
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
eqK _ _ = False

-- Div and mod operations are very costly (simplifying them requires
-- constructing conditionals, etc), so they are not included in IntegralH.
instance (NumScalar r, IntegralH r, Nested.IntElt r, AstSpan s)
         => IntegralH (AstTensor ms s (TKScalar r)) where
  quotH (AstPrimalPart n) (AstPrimalPart k) = AstPrimalPart (quotH n k)
  quotH (AstPlainPart @_ @s1 n) (AstPlainPart @_ @s2 k)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart (quotH n k)
  quotH (AstFromPrimal n) (AstFromPrimal k) = fromPrimal (quotH n k)
  quotH (AstFromPlain n) (AstFromPlain k) = fromPlain (quotH n k)
  quotH (AstConvert c n) (AstConvert _ k)
    | FTKS ZSS x <- ftkAst n
    , FTKS ZSS y <- ftkAst k
    , Just Refl <- matchingFTK x (convertFTK c (ftkAst n))
    , Just Refl <- matchingFTK x y =
      AstConvert c (quotH n k)
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
        (u1, u2) = bounds t
    in if u1 == u2 then fromPlain $ AstConcreteK u1 else t

  remH (AstPrimalPart n) (AstPrimalPart k) = AstPrimalPart (remH n k)
  remH (AstPlainPart @_ @s1 n) (AstPlainPart @_ @s2 k)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart (remH n k)
  remH (AstFromPrimal n) (AstFromPrimal k) = fromPrimal (remH n k)
  remH (AstFromPlain n) (AstFromPlain k) = fromPlain (remH n k)
  remH (AstConvert c n) (AstConvert _ k)
    | FTKS ZSS x <- ftkAst n
    , FTKS ZSS y <- ftkAst k
    , Just Refl <- matchingFTK x (convertFTK c (ftkAst n))
    , Just Refl <- matchingFTK x y =
      AstConvert c (remH n k)
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
        (u1, u2) = bounds t
    in if u1 == u2 then fromPlain $ AstConcreteK u1 else t
  {-# SPECIALIZE instance IntegralH (AstTensor ms FullSpan (TKScalar Int64)) #-}
  {-# SPECIALIZE instance IntegralH (AstTensor ms PrimalSpan (TKScalar Int64)) #-}
  {-# SPECIALIZE instance IntegralH (AstTensor ms FullSpan (TKScalar CInt)) #-}
  {-# SPECIALIZE instance IntegralH (AstTensor ms PrimalSpan (TKScalar CInt)) #-}

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Fractional (AstTensor ms s (TKScalar r)) where
  AstPrimalPart u / AstPrimalPart v = AstPrimalPart $ u / v
  AstPlainPart @_ @s1 u / AstPlainPart @_ @s2 v
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ u / v
  AstFromPrimal u / AstFromPrimal v = fromPrimal $ u / v
  AstFromPlain u / AstFromPlain v = fromPlain $ u / v
  AstConcreteK u / AstConcreteK v = AstConcreteK $ u / v
  u / v = AstR2K DivideOp u v
  recip (AstPrimalPart u) = AstPrimalPart (recip u)
  recip (AstPlainPart u) = AstPlainPart (recip u)
  recip (AstFromPrimal u) = fromPrimal (recip u)
  recip (AstFromPlain u) = fromPlain (recip u)
  recip (AstConcreteK u) = AstConcreteK (recip u)
  recip u = AstR1K RecipOp u
  fromRational r = fromPlain $ AstConcreteK (fromRational r)

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKScalar r)) where
  pi = error "pi is not defined for tensors"
  exp (AstPrimalPart u) = AstPrimalPart $ exp u
  exp (AstPlainPart u) = AstPlainPart $ exp u
  exp (AstFromPrimal u) = fromPrimal $ exp u
  exp (AstFromPlain u) = fromPlain $ exp u
  exp (AstConcreteK u) = AstConcreteK $ exp u
  exp u = AstR1K ExpOp u
  log (AstPrimalPart u) = AstPrimalPart $ log u
  log (AstPlainPart u) = AstPlainPart $ log u
  log (AstFromPrimal u) = fromPrimal $ log u
  log (AstFromPlain u) = fromPlain $ log u
  log (AstConcreteK u) = AstConcreteK $ log u
  log u = AstR1K LogOp u
  sqrt (AstPrimalPart u) = AstPrimalPart $ sqrt u
  sqrt (AstPlainPart u) = AstPlainPart $ sqrt u
  sqrt (AstFromPrimal u) = fromPrimal $ sqrt u
  sqrt (AstFromPlain u) = fromPlain $ sqrt u
  sqrt (AstConcreteK u) = AstConcreteK $ sqrt u
  sqrt u = AstR1K SqrtOp u
  (AstPrimalPart u) ** (AstPrimalPart v) = AstPrimalPart $ u ** v
  (AstPlainPart @_ @s1 u) ** (AstPlainPart @_ @s2 v)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ u ** v
  (AstFromPrimal u) ** (AstFromPrimal v) = fromPrimal $ u ** v
  (AstFromPlain u) ** (AstFromPlain v) = fromPlain $ u ** v
  (AstConcreteK u) ** (AstConcreteK v) = AstConcreteK $ u ** v
  u ** v = AstR2K PowerOp u v
  logBase (AstPrimalPart u) (AstPrimalPart v) = AstPrimalPart $ logBase u v
  logBase (AstPlainPart @_ @s1 u) (AstPlainPart @_ @s2 v)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ logBase u v
  logBase (AstFromPrimal u) (AstFromPrimal v) = fromPrimal $ logBase u v
  logBase (AstFromPlain u) (AstFromPlain v) = fromPlain $ logBase u v
  logBase (AstConcreteK u) (AstConcreteK v) = AstConcreteK $ logBase u v
  logBase u v = AstR2K LogBaseOp u v
  sin (AstPrimalPart u) = AstPrimalPart $ sin u
  sin (AstPlainPart u) = AstPlainPart $ sin u
  sin (AstFromPrimal u) = fromPrimal $ sin u
  sin (AstFromPlain u) = fromPlain $ sin u
  sin (AstConcreteK u) = AstConcreteK $ sin u
  sin u = AstR1K SinOp u
  cos (AstPrimalPart u) = AstPrimalPart $ cos u
  cos (AstPlainPart u) = AstPlainPart $ cos u
  cos (AstFromPrimal u) = fromPrimal $ cos u
  cos (AstFromPlain u) = fromPlain $ cos u
  cos (AstConcreteK u) = AstConcreteK $ cos u
  cos u = AstR1K CosOp u
  tan (AstPrimalPart u) = AstPrimalPart $ tan u
  tan (AstPlainPart u) = AstPlainPart $ tan u
  tan (AstFromPrimal u) = fromPrimal $ tan u
  tan (AstFromPlain u) = fromPlain $ tan u
  tan (AstConcreteK u) = AstConcreteK $ tan u
  tan u = AstR1K TanOp u
  asin (AstPrimalPart u) = AstPrimalPart $ asin u
  asin (AstPlainPart u) = AstPlainPart $ asin u
  asin (AstFromPrimal u) = fromPrimal $ asin u
  asin (AstFromPlain u) = fromPlain $ asin u
  asin (AstConcreteK u) = AstConcreteK $ asin u
  asin u = AstR1K AsinOp u
  acos (AstPrimalPart u) = AstPrimalPart $ acos u
  acos (AstPlainPart u) = AstPlainPart $ acos u
  acos (AstFromPrimal u) = fromPrimal $ acos u
  acos (AstFromPlain u) = fromPlain $ acos u
  acos (AstConcreteK u) = AstConcreteK $ acos u
  acos u = AstR1K AcosOp u
  atan (AstPrimalPart u) = AstPrimalPart $ atan u
  atan (AstPlainPart u) = AstPlainPart $ atan u
  atan (AstFromPrimal u) = fromPrimal $ atan u
  atan (AstFromPlain u) = fromPlain $ atan u
  atan (AstConcreteK u) = AstConcreteK $ atan u
  atan u = AstR1K AtanOp u
  sinh (AstPrimalPart u) = AstPrimalPart $ sinh u
  sinh (AstPlainPart u) = AstPlainPart $ sinh u
  sinh (AstFromPrimal u) = fromPrimal $ sinh u
  sinh (AstFromPlain u) = fromPlain $ sinh u
  sinh (AstConcreteK u) = AstConcreteK $ sinh u
  sinh u = AstR1K SinhOp u
  cosh (AstPrimalPart u) = AstPrimalPart $ cosh u
  cosh (AstPlainPart u) = AstPlainPart $ cosh u
  cosh (AstFromPrimal u) = fromPrimal $ cosh u
  cosh (AstFromPlain u) = fromPlain $ cosh u
  cosh (AstConcreteK u) = AstConcreteK $ cosh u
  cosh u = AstR1K CoshOp u
  tanh (AstPrimalPart u) = AstPrimalPart $ tanh u
  tanh (AstPlainPart u) = AstPlainPart $ tanh u
  tanh (AstFromPrimal u) = fromPrimal $ tanh u
  tanh (AstFromPlain u) = fromPlain $ tanh u
  tanh (AstConcreteK u) = AstConcreteK $ tanh u
  tanh u = AstR1K TanhOp u
  asinh (AstPrimalPart u) = AstPrimalPart $ asinh u
  asinh (AstPlainPart u) = AstPlainPart $ asinh u
  asinh (AstFromPrimal u) = fromPrimal $ asinh u
  asinh (AstFromPlain u) = fromPlain $ asinh u
  asinh (AstConcreteK u) = AstConcreteK $ asinh u
  asinh u = AstR1K AsinhOp u
  acosh (AstPrimalPart u) = AstPrimalPart $ acosh u
  acosh (AstPlainPart u) = AstPlainPart $ acosh u
  acosh (AstFromPrimal u) = fromPrimal $ acosh u
  acosh (AstFromPlain u) = fromPlain $ acosh u
  acosh (AstConcreteK u) = AstConcreteK $ acosh u
  acosh u = AstR1K AcoshOp u
  atanh (AstPrimalPart u) = AstPrimalPart $ atanh u
  atanh (AstPlainPart u) = AstPlainPart $ atanh u
  atanh (AstFromPrimal u) = fromPrimal $ atanh u
  atanh (AstFromPlain u) = fromPlain $ atanh u
  atanh (AstConcreteK u) = AstConcreteK $ atanh u
  atanh u = AstR1K AtanhOp u

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => RealFloatH (AstTensor ms s (TKScalar r)) where
  atan2H (AstPrimalPart u) (AstPrimalPart v) = AstPrimalPart $ atan2H u v
  atan2H (AstPlainPart @_ @s1 u) (AstPlainPart @_ @s2 v)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ atan2H u v
  atan2H (AstFromPrimal u) (AstFromPrimal v) = fromPrimal $ atan2H u v
  atan2H (AstFromPlain u) (AstFromPlain v) = fromPlain $ atan2H u v
  atan2H (AstConcreteK u) (AstConcreteK v) = AstConcreteK $ atan2H u v
  atan2H u v = AstR2K Atan2Op u v


-- * Unlawful numeric instances for ranked AST; lawful modulo evaluation

instance (NumScalar r, AstSpan s)
         => Num (AstTensor ms s (TKR n r)) where
  (+) = liftRFromS2 (+)
  (-) = liftRFromS2 (-)
  (*) = liftRFromS2 (*)
  negate = liftRFromS1 negate
  abs = liftRFromS1 abs
  signum = liftRFromS1 signum
  fromInteger i = error $ "fromInteger is not defined for ranked tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r, AstSpan s)
         => IntegralH (AstTensor ms s (TKR n r)) where
  quotH = liftRFromS2 quotH
  remH = liftRFromS2 remH

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Fractional (AstTensor ms s (TKR n r)) where
  (/) = liftRFromS2 (/)
  recip = liftRFromS1 recip
  fromRational r = error $ "fromRational is not defined for ranked tensors: "
                           ++ show r

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKR n r)) where
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

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => RealFloatH (AstTensor ms s (TKR n r)) where
  atan2H = liftRFromS2 atan2H


-- * Unlawful numeric instances for shaped AST; lawful modulo evaluation

instance (NumScalar r, AstSpan s)
         => Num (AstTensor ms s (TKS sh r)) where
  AstReplicate snat stk@STKS{} u + AstReplicate _ STKS{} v =
    AstReplicate snat stk $ u + v
  AstPrimalPart u + AstPrimalPart v = AstPrimalPart $ u + v
  AstDualPart u + AstDualPart v = AstDualPart $ u + v
  AstPlainPart @_ @s1 u + AstPlainPart @_ @s2 v
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ u + v
  AstFromPrimal u + AstFromPrimal v = fromPrimal $ u + v
  AstFromDual u + AstFromDual v = fromDual $ u + v
  AstFromPlain u + AstFromPlain v = fromPlain $ u + v
  AstConvert c u + AstConvert _ v
    | FTKS ZSS x <- convertFTK c (ftkAst u)
    , Just Refl <- matchingFTK x (ftkAst u)
    , Just Refl <- matchingFTK x (ftkAst v) =
      AstConvert c $ u + v
  AstConcreteS z + u | Just 0 <- sunReplicateScal z = u
  u + AstConcreteS z | Just 0 <- sunReplicateScal z = u
  AstFromPlain (AstConcreteS z) + u | Just 0 <- sunReplicateScal z = u
  u + AstFromPlain (AstConcreteS z) | Just 0 <- sunReplicateScal z = u
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

  AstReplicate snat stk@STKS{} u * AstReplicate _ STKS{} v =
    AstReplicate snat stk $ u * v
  AstPrimalPart u * AstPrimalPart v = AstPrimalPart $ u * v
  AstPlainPart @_ @s1 u * AstPlainPart @_ @s2 v
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ u * v
  AstFromPrimal u * AstFromPrimal v = fromPrimal $ u * v
--  AstFromDual{} * AstFromDual{} = 0
  AstFromPlain u * AstFromPlain v = fromPlain $ u * v
  AstConcreteS z * _ | Just 0 <- sunReplicateScal z = AstConcreteS z
  _ * AstConcreteS z | Just 0 <- sunReplicateScal z = AstConcreteS z
  AstConcreteS s * u | Just 1 <- sunReplicateScal s = u
  u * AstConcreteS s | Just 1 <- sunReplicateScal s = u
  AstFromPlain (AstConcreteS z) * _ | Just 0 <- sunReplicateScal z =
    AstFromPlain $ AstConcreteS z
  _ * AstFromPlain (AstConcreteS z) | Just 0 <- sunReplicateScal z =
    AstFromPlain $ AstConcreteS z
  AstFromPlain (AstConcreteS s) * u | Just 1 <- sunReplicateScal s = u
  u * AstFromPlain (AstConcreteS s) | Just 1 <- sunReplicateScal s = u
  AstConvert c u * AstConvert _ v
    | FTKS ZSS x <- convertFTK c (ftkAst u)
    , Just Refl <- matchingFTK x (ftkAst u)
    , Just Refl <- matchingFTK x (ftkAst v) =
      AstConvert c $ u * v
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

  u@AstConcreteS{} * AstPlusS v w = AstPlusS (u * v) (u * w)
  AstTimesS u@AstConcreteS{} x * AstPlusS v w =
    AstTimesS x (AstPlusS (u * v) (u * w))
  AstPlusS v w * u@AstConcreteS{} = AstPlusS (v * u) (w * u)
  AstPlusS v w * AstTimesS u@AstConcreteS{} x =
    AstTimesS (AstPlusS (v * u) (w * u)) x
  u@(AstFromPlain (AstConcreteS{})) * AstPlusS v w = AstPlusS (u * v) (u * w)
  AstTimesS u@(AstFromPlain (AstConcreteS{})) x * AstPlusS v w =
    AstTimesS x (AstPlusS (u * v) (u * w))
  AstPlusS v w * u@(AstFromPlain (AstConcreteS{})) = AstPlusS (v * u) (w * u)
  AstPlusS v w * AstTimesS u@(AstFromPlain (AstConcreteS{})) x =
    AstTimesS (AstPlusS (v * u) (w * u)) x

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

  negate (AstReplicate snat stk@STKS{} u) = AstReplicate snat stk (negate u)
  negate (AstCond b n k) = AstCond b (negate n) (negate k)
-- TODO: negate (AstBuild1 k stk (var, v)) = AstBuild1 k stk (var, negate v)
  negate (AstLet var n k) = AstLet var n (negate k)
  negate (AstPrimalPart n) = AstPrimalPart (negate n)
  negate (AstDualPart n) = AstDualPart (negate n)
  negate (AstPlainPart n) = AstPlainPart (negate n)
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
  negate (AstGatherS @shm @shn @shp shn v (vars, ix)) =
    AstGatherS @shm @shn @shp shn (negate v) (vars, ix)
  negate (AstConvert c n)
    | FTKS ZSS x <- convertFTK c (ftkAst n)
    , Just Refl <- matchingFTK x (ftkAst n) =
      AstConvert c (negate n)
  negate u = AstN1S NegateOp u
  abs (AstReplicate snat stk@STKS{} u) = AstReplicate snat stk (abs u)
  abs (AstPrimalPart n) = AstPrimalPart (abs n)
  abs (AstDualPart n) = AstDualPart (abs n)
  abs (AstPlainPart n) = AstPlainPart (abs n)
  abs (AstFromPrimal n) = fromPrimal (abs n)
  abs (AstFromDual n) = fromDual (abs n)
  abs (AstFromPlain n) = fromPlain (abs n)
  abs (AstN1S AbsOp u) = AstN1S AbsOp u
  abs (AstConcreteS u) = AstConcreteS (abs u)
  abs (AstConvert c n)
    | FTKS ZSS x <- convertFTK c (ftkAst n)
    , Just Refl <- matchingFTK x (ftkAst n) =
      AstConvert c (abs n)
  abs (AstN1S NegateOp u) = abs u
  abs u = AstN1S AbsOp u
  signum (AstReplicate snat stk@STKS{} u) = AstReplicate snat stk (signum u)
  signum (AstPrimalPart n) = AstPrimalPart (signum n)
  signum (AstDualPart n) = AstDualPart (signum n)
  signum (AstPlainPart n) = AstPlainPart (signum n)
  signum (AstFromPrimal n) = fromPrimal (signum n)
  signum (AstFromDual n) = fromDual (signum n)
  signum (AstFromPlain n) = fromPlain (signum n)
  signum (AstN1S SignumOp u) = AstN1S SignumOp u
  signum (AstConcreteS u) = AstConcreteS (signum u)
  signum (AstConvert c n)
    | FTKS ZSS x <- convertFTK c (ftkAst n)
    , Just Refl <- matchingFTK x (ftkAst n) =
      AstConvert c (signum n)
  signum u = AstN1S SignumOp u
  fromInteger i = error $ "fromInteger is not defined for shaped tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r, AstSpan s)
         => IntegralH (AstTensor ms s (TKS sh r)) where
  quotH (AstReplicate snat stk@STKS{} u) (AstReplicate _ STKS{} v) =
    AstReplicate snat stk $ quotH u v
  quotH (AstPrimalPart n) (AstPrimalPart k) = AstPrimalPart (quotH n k)
  quotH (AstPlainPart @_ @s1 n) (AstPlainPart @_ @s2 k)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart (quotH n k)
  quotH (AstFromPrimal n) (AstFromPrimal k) = fromPrimal (quotH n k)
  quotH (AstFromPlain n) (AstFromPlain k) = fromPlain (quotH n k)
  quotH (AstConvert c n) (AstConvert _ k)
    | FTKS ZSS x <- convertFTK c (ftkAst n)
    , Just Refl <- matchingFTK x (ftkAst n)
    , Just Refl <- matchingFTK x (ftkAst k) =
      AstConvert c (quotH n k)
  quotH (AstConcreteS n) (AstConcreteS k) = AstConcreteS (quotH n k)
  quotH (AstConcreteS z) _ | Just 0 <- sunReplicateScal z = AstConcreteS z
  quotH u (AstConcreteS s) | Just 1 <- sunReplicateScal s = u
  quotH (AstFromPlain (AstConcreteS z)) _ | Just 0 <- sunReplicateScal z =
    AstFromPlain $ AstConcreteS z
  quotH u (AstFromPlain (AstConcreteS s)) | Just 1 <- sunReplicateScal s = u
  quotH (AstI2S QuotOp u v) w = quotH u (v * w)
  quotH u v = AstI2S QuotOp u v

  remH (AstReplicate snat stk@STKS{} u) (AstReplicate _ STKS{} v) =
    AstReplicate snat stk $ remH u v
  remH (AstPrimalPart n) (AstPrimalPart k) = AstPrimalPart (remH n k)
  remH (AstPlainPart @_ @s1 n) (AstPlainPart @_ @s2 k)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart (remH n k)
  remH (AstFromPrimal n) (AstFromPrimal k) = fromPrimal (remH n k)
  remH (AstFromPlain n) (AstFromPlain k) = fromPlain (remH n k)
  remH (AstConvert c n) (AstConvert _ k)
    | FTKS ZSS x <- convertFTK c (ftkAst n)
    , Just Refl <- matchingFTK x (ftkAst n)
    , Just Refl <- matchingFTK x (ftkAst k) =
      AstConvert c (remH n k)
  remH (AstConcreteS n) (AstConcreteS k) = AstConcreteS (remH n k)
  remH (AstConcreteS z) _ | Just 0 <- sunReplicateScal z = AstConcreteS z
  remH (AstFromPlain (AstConcreteS z)) _ | Just 0 <- sunReplicateScal z =
    AstFromPlain $ AstConcreteS z
--  remH _ (AstConcreteS s) | Just 1 <- sunReplicateScal s = AstConcreteS 0
  remH u v = AstI2S RemOp u v

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Fractional (AstTensor ms s (TKS sh r)) where
  AstPrimalPart u / AstPrimalPart v = AstPrimalPart $ u / v
  AstPlainPart @_ @s1 u / AstPlainPart @_ @s2 v
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ u / v
  AstFromPrimal u / AstFromPrimal v = fromPrimal $ u / v
  AstFromPlain u / AstFromPlain v = fromPlain $ u / v
  AstConcreteS u / AstConcreteS v = AstConcreteS $ u / v
  u / v = AstR2S DivideOp u v
  recip (AstPrimalPart u) = AstPrimalPart (recip u)
  recip (AstPlainPart u) = AstPlainPart (recip u)
  recip (AstFromPrimal u) = fromPrimal (recip u)
  recip (AstFromPlain u) = fromPlain (recip u)
  recip (AstConcreteS u) = AstConcreteS (recip u)
  recip u = AstR1S RecipOp u
  fromRational r = error $ "fromRational is not defined for shaped tensors: "
                           ++ show r

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKS sh r)) where
  pi = error "pi is not defined for tensors"
  exp (AstPrimalPart u) = AstPrimalPart $ exp u
  exp (AstPlainPart u) = AstPlainPart $ exp u
  exp (AstFromPrimal u) = fromPrimal $ exp u
  exp (AstFromPlain u) = fromPlain $ exp u
  exp (AstConcreteS u) = AstConcreteS $ exp u
  exp u = AstR1S ExpOp u
  log (AstPrimalPart u) = AstPrimalPart $ log u
  log (AstPlainPart u) = AstPlainPart $ log u
  log (AstFromPrimal u) = fromPrimal $ log u
  log (AstFromPlain u) = fromPlain $ log u
  log (AstConcreteS u) = AstConcreteS $ log u
  log u = AstR1S LogOp u
  sqrt (AstPrimalPart u) = AstPrimalPart $ sqrt u
  sqrt (AstPlainPart u) = AstPlainPart $ sqrt u
  sqrt (AstFromPrimal u) = fromPrimal $ sqrt u
  sqrt (AstFromPlain u) = fromPlain $ sqrt u
  sqrt (AstConcreteS u) = AstConcreteS $ sqrt u
  sqrt u = AstR1S SqrtOp u
  (AstPrimalPart u) ** (AstPrimalPart v) = AstPrimalPart $ u ** v
  (AstPlainPart @_ @s1 u) ** (AstPlainPart @_ @s2 v)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ u ** v
  (AstFromPrimal u) ** (AstFromPrimal v) = fromPrimal $ u ** v
  (AstFromPlain u) ** (AstFromPlain v) = fromPlain $ u ** v
  (AstConcreteS u) ** (AstConcreteS v) = AstConcreteS $ u ** v
  u ** v = AstR2S PowerOp u v
  logBase (AstPrimalPart u) (AstPrimalPart v) = AstPrimalPart $ logBase u v
  logBase (AstPlainPart @_ @s1 u) (AstPlainPart @_ @s2 v)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ logBase u v
  logBase (AstFromPrimal u) (AstFromPrimal v) = fromPrimal $ logBase u v
  logBase (AstFromPlain u) (AstFromPlain v) = fromPlain $ logBase u v
  logBase (AstConcreteS u) (AstConcreteS v) = AstConcreteS $ logBase u v
  logBase u v = AstR2S LogBaseOp u v
  sin (AstPrimalPart u) = AstPrimalPart $ sin u
  sin (AstPlainPart u) = AstPlainPart $ sin u
  sin (AstFromPrimal u) = fromPrimal $ sin u
  sin (AstFromPlain u) = fromPlain $ sin u
  sin (AstConcreteS u) = AstConcreteS $ sin u
  sin u = AstR1S SinOp u
  cos (AstPrimalPart u) = AstPrimalPart $ cos u
  cos (AstPlainPart u) = AstPlainPart $ cos u
  cos (AstFromPrimal u) = fromPrimal $ cos u
  cos (AstFromPlain u) = fromPlain $ cos u
  cos (AstConcreteS u) = AstConcreteS $ cos u
  cos u = AstR1S CosOp u
  tan (AstPrimalPart u) = AstPrimalPart $ tan u
  tan (AstPlainPart u) = AstPlainPart $ tan u
  tan (AstFromPrimal u) = fromPrimal $ tan u
  tan (AstFromPlain u) = fromPlain $ tan u
  tan (AstConcreteS u) = AstConcreteS $ tan u
  tan u = AstR1S TanOp u
  asin (AstPrimalPart u) = AstPrimalPart $ asin u
  asin (AstPlainPart u) = AstPlainPart $ asin u
  asin (AstFromPrimal u) = fromPrimal $ asin u
  asin (AstFromPlain u) = fromPlain $ asin u
  asin (AstConcreteS u) = AstConcreteS $ asin u
  asin u = AstR1S AsinOp u
  acos (AstPrimalPart u) = AstPrimalPart $ acos u
  acos (AstPlainPart u) = AstPlainPart $ acos u
  acos (AstFromPrimal u) = fromPrimal $ acos u
  acos (AstFromPlain u) = fromPlain $ acos u
  acos (AstConcreteS u) = AstConcreteS $ acos u
  acos u = AstR1S AcosOp u
  atan (AstPrimalPart u) = AstPrimalPart $ atan u
  atan (AstPlainPart u) = AstPlainPart $ atan u
  atan (AstFromPrimal u) = fromPrimal $ atan u
  atan (AstFromPlain u) = fromPlain $ atan u
  atan (AstConcreteS u) = AstConcreteS $ atan u
  atan u = AstR1S AtanOp u
  sinh (AstPrimalPart u) = AstPrimalPart $ sinh u
  sinh (AstPlainPart u) = AstPlainPart $ sinh u
  sinh (AstFromPrimal u) = fromPrimal $ sinh u
  sinh (AstFromPlain u) = fromPlain $ sinh u
  sinh (AstConcreteS u) = AstConcreteS $ sinh u
  sinh u = AstR1S SinhOp u
  cosh (AstPrimalPart u) = AstPrimalPart $ cosh u
  cosh (AstPlainPart u) = AstPlainPart $ cosh u
  cosh (AstFromPrimal u) = fromPrimal $ cosh u
  cosh (AstFromPlain u) = fromPlain $ cosh u
  cosh (AstConcreteS u) = AstConcreteS $ cosh u
  cosh u = AstR1S CoshOp u
  tanh (AstPrimalPart u) = AstPrimalPart $ tanh u
  tanh (AstPlainPart u) = AstPlainPart $ tanh u
  tanh (AstFromPrimal u) = fromPrimal $ tanh u
  tanh (AstFromPlain u) = fromPlain $ tanh u
  tanh (AstConcreteS u) = AstConcreteS $ tanh u
  tanh u = AstR1S TanhOp u
  asinh (AstPrimalPart u) = AstPrimalPart $ asinh u
  asinh (AstPlainPart u) = AstPlainPart $ asinh u
  asinh (AstFromPrimal u) = fromPrimal $ asinh u
  asinh (AstFromPlain u) = fromPlain $ asinh u
  asinh (AstConcreteS u) = AstConcreteS $ asinh u
  asinh u = AstR1S AsinhOp u
  acosh (AstPrimalPart u) = AstPrimalPart $ acosh u
  acosh (AstPlainPart u) = AstPlainPart $ acosh u
  acosh (AstFromPrimal u) = fromPrimal $ acosh u
  acosh (AstFromPlain u) = fromPlain $ acosh u
  acosh (AstConcreteS u) = AstConcreteS $ acosh u
  acosh u = AstR1S AcoshOp u
  atanh (AstPrimalPart u) = AstPrimalPart $ atanh u
  atanh (AstPlainPart u) = AstPlainPart $ atanh u
  atanh (AstFromPrimal u) = fromPrimal $ atanh u
  atanh (AstFromPlain u) = fromPlain $ atanh u
  atanh (AstConcreteS u) = AstConcreteS $ atanh u
  atanh u = AstR1S AtanhOp u

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => RealFloatH (AstTensor ms s (TKS sh r)) where
  atan2H (AstPrimalPart u) (AstPrimalPart v) = AstPrimalPart $ atan2H u v
  atan2H (AstPlainPart @_ @s1 u) (AstPlainPart @_ @s2 v)
    | Just Refl <- sameAstSpan @s1 @s2 = AstPlainPart $ atan2H u v
  atan2H (AstFromPrimal u) (AstFromPrimal v) = fromPrimal $ atan2H u v
  atan2H (AstFromPlain u) (AstFromPlain v) = fromPlain $ atan2H u v
  atan2H (AstConcreteS u) (AstConcreteS v) = AstConcreteS $ atan2H u v
  atan2H u v = AstR2S Atan2Op u v


-- * Unlawful numeric instances for mixed AST; lawful modulo evaluation

instance (NumScalar r, AstSpan s)
         => Num (AstTensor ms s (TKX sh r)) where
  (+) = liftXFromS2 (+)
  (-) = liftXFromS2 (-)
  (*) = liftXFromS2 (*)
  negate = liftXFromS1 negate
  abs = liftXFromS1 abs
  signum = liftXFromS1 signum
  fromInteger i = error $ "fromInteger is not defined for mixed tensors: "
                          ++ show i

instance (NumScalar r, IntegralH r, Nested.IntElt r, AstSpan s)
         => IntegralH (AstTensor ms s (TKX sh r)) where
  quotH = liftXFromS2 quotH
  remH = liftXFromS2 remH

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Fractional (AstTensor ms s (TKX sh r)) where
  (/) = liftXFromS2 (/)
  recip = liftXFromS1 recip
  fromRational r = error $ "fromRational is not defined for mixed tensors: "
                           ++ show r

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => Floating (AstTensor ms s (TKX sh r)) where
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

instance (NumScalar r, RealFloatH r, Nested.FloatElt r, AstSpan s)
         => RealFloatH (AstTensor ms s (TKX sh r)) where
  atan2H = liftXFromS2 atan2H


-- * Unlawful instances of AST for bool; they are lawful modulo evaluation

-- Simple variable comparisons, if any, come first.
instance Boolean (AstBool ms) where
  true = AstBoolConst True
  false = AstBoolConst False
  notB (AstBoolConst b) = AstBoolConst $ not b
  notB (AstBoolNot b) = b
  notB b = AstBoolNot b
  AstBoolConst True &&* b = b
  AstBoolConst False &&* _b = AstBoolConst False
  b &&* AstBoolConst True = b
  _b &&* AstBoolConst False = AstBoolConst False
  AstBoolAnd b c &&* d = b &&* (c &&* d)
  b@(AstLeqK AstConcreteK{} AstVar{}) &&* c = AstBoolAnd b c
  b@(AstLeqK AstConcreteK{} (AstN1K NegateOp
                                    AstVar{})) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstLeqK AstConcreteK{} AstVar{})) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstLeqK AstConcreteK{} (AstN1K NegateOp
                                       AstVar{}))) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstBoolAnd (AstLeqK AstConcreteK{} AstVar{}) _)) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstBoolAnd
          (AstLeqK AstConcreteK{}
                   (AstN1K NegateOp AstVar{})) _)) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstBoolAnd (AstBoolNot (AstLeqK AstConcreteK{}
                                        AstVar{})) _)) &&* c = AstBoolAnd b c
  b@(AstBoolNot
       (AstBoolAnd
          (AstBoolNot
             (AstLeqK AstConcreteK{}
                      (AstN1K NegateOp AstVar{}))) _)) &&* c = AstBoolAnd b c
  b &&* c@(AstLeqK AstConcreteK{} AstVar{}) = AstBoolAnd c b
  b &&* c@(AstLeqK AstConcreteK{} (AstN1K NegateOp
                                          AstVar{})) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstLeqK AstConcreteK{} AstVar{})) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstLeqK AstConcreteK{} (AstN1K NegateOp
                                             AstVar{}))) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstBoolAnd (AstLeqK AstConcreteK{} AstVar{}) _)) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstBoolAnd
                (AstLeqK AstConcreteK{}
                         (AstN1K NegateOp AstVar{})) _)) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstBoolAnd (AstBoolNot (AstLeqK AstConcreteK{}
                                              AstVar{})) _)) = AstBoolAnd c b
  b &&* c@(AstBoolNot
             (AstBoolAnd
                (AstBoolNot
                   (AstLeqK AstConcreteK{}
                            (AstN1K NegateOp AstVar{}))) _)) = AstBoolAnd c b
  b &&* AstBoolAnd
          c@(AstLeqK AstConcreteK{} AstVar{}) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstLeqK AstConcreteK{}
                     (AstN1K NegateOp AstVar{})) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot (AstLeqK AstConcreteK{}
                                 AstVar{})) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstLeqK AstConcreteK{}
                        (AstN1K NegateOp AstVar{}))) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstBoolAnd (AstLeqK AstConcreteK{}
                                    AstVar{}) _)) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstBoolAnd
                  (AstLeqK AstConcreteK{}
                           (AstN1K NegateOp
                                   AstVar{})) _)) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstBoolAnd
                  (AstBoolNot
                     (AstLeqK AstConcreteK{}
                              AstVar{})) _)) d = AstBoolAnd c (b &&* d)
  b &&* AstBoolAnd
          c@(AstBoolNot
               (AstBoolAnd
                  (AstBoolNot
                     (AstLeqK AstConcreteK{}
                              (AstN1K
                                 NegateOp
                                 AstVar{}))) _)) d = AstBoolAnd c (b &&* d)
  b &&* c = AstBoolAnd b c
  b ||* c = notB (notB b &&* notB c)

-- TODO: refactor with something like liftRFromS2
instance (AstSpan s, NumScalar r) => EqH (AstTensor ms s) (TKR n r) where
  v ==. u = case ftkAst v of
    FTKR shv' _ -> case ftkAst u of
      FTKR shu' _ ->
        withShsFromShR shv' $ \shv ->
          withShsFromShR shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstSFromR shu (plainPart v)
                ==. cAstSFromR shv (plainPart u)
              _ -> error $ "(==.): shapes don't match: "
                           ++ show (shu, shv)

instance (AstSpan s, NumScalar r) => EqH (AstTensor ms s) (TKX sh r) where
  v ==. u = case ftkAst v of
    FTKX shv' _ -> case ftkAst u of
      FTKX shu' _ ->
        withShsFromShX shv' $ \shv ->
          withShsFromShX shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstSFromX shu (plainPart v)
                ==. cAstSFromX shv (plainPart u)
              _ -> error $ "(==.): shapes don't match: "
                           ++ show (shu, shv)

instance (AstSpan s, NumScalar r) => OrdH (AstTensor ms s) (TKR n r) where
  v <=. u = case ftkAst v of
    FTKR shv' _ -> case ftkAst u of
      FTKR shu' _ ->
        withShsFromShR shv' $ \shv ->
          withShsFromShR shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstSFromR shu (plainPart v)
                <=. cAstSFromR shv (plainPart u)
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)

instance (AstSpan s, NumScalar r) => OrdH (AstTensor ms s) (TKX sh r) where
  v <=. u = case ftkAst v of
    FTKX shv' _ -> case ftkAst u of
      FTKX shu' _ ->
        withShsFromShX shv' $ \shv ->
          withShsFromShX shu' $ \shu ->
            case testEquality shv shu of
              Just Refl ->
                cAstSFromX shu (plainPart v)
                <=. cAstSFromX shv (plainPart u)
              _ -> error $ "(<=.): shapes don't match: "
                           ++ show (shu, shv)

-- TODO: share u and v, since they are duplicated here
instance (AstSpan s, NumScalar r)
         => EqH (AstTensor ms s) (TKScalar r) where
  v ==. u = v <=. u &&* u <=. v
  {- TODO: for this to work, booleans have to be first-class:
  vUnshared ==. uUnshared = astLetFunNoSimplify vUnshared $ \v ->
                            astLetFunNoSimplify uUnshared $ \u ->
    v <=. u &&* u <=. v -}

instance (AstSpan s, NumScalar r)
         => EqH (AstTensor ms s) (TKS sh r) where
  v ==. u = v <=. u &&* u <=. v

-- These are common in indexing, so worth optimizing early via AstConcrete.
-- We keep AstConcrete on the left, as with AstPlusK and others.
instance (AstSpan s, NumScalar r)
         => OrdH (AstTensor ms s) (TKScalar r) where
  u <=. v | let (u1, u2) = bounds u
                (v1, v2) = bounds v
          , u2 <= v1 || u1 > v2 = AstBoolConst (u2 <= v1)
  AstPrimalPart u <=. AstPrimalPart v = u <=. v
  AstPlainPart @_ @s1 u <=. AstPlainPart @_ @s2 v
    | Just Refl <- sameAstSpan @s1 @s2 =
      u <=. v
  AstFromPrimal u <=. AstFromPrimal v = u <=. v
  AstFromDual{} <=. AstFromDual{} = AstBoolConst True
  AstFromPlain u <=. AstFromPlain v = u <=. v
  AstConvert c u <=. AstConvert _ v
    | FTKS ZSS (FTKScalar @ru) <- ftkAst u
    , FTKS ZSS (FTKScalar @rv) <- ftkAst v
    , Just Refl <- testEquality (typeRep @ru) (typeRep @rv)
    , Dict0 <- lemTKAllNumConvert c
    , Dict0 <- numFromTKAllNum (Proxy @ru)
    = u <=. v
  AstConcreteK u <=. AstConvert _ v
    | FTKS ZSS (FTKScalar @rv) <- ftkAst v
    , Just Refl <- testEquality (typeRep @rv) (typeRep @r)
    = AstConcreteS (unConcrete $ sfromK $ Concrete u) <=. v
  u <=. AstPlusK (AstConcreteK v) w =
    u - AstConcreteK v <=. w
  AstPlusK (AstConcreteK u) w <=. v =
    AstConcreteK u <=. v - w
  u <=. AstConcreteK v =
    AstConcreteK (negate v) <=. negate u
  AstConcreteK u <=. AstTimesK (AstConcreteK v) w
    | v > 0 && u >= 0
    , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      AstConcreteK ((u + v - 1) `quotH` v) <=. w -- 10 == 5 * 2, 11 > 5 * 2
  AstConcreteK u <=. AstTimesK (AstConcreteK v) w
    | v > 0 && u < 0
    , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      AstConcreteK (u `quotH` v) <=. w  -- -10 == 5 * -2, -9 > 5 * -2
  AstConcreteK u <=. AstTimesK (AstConcreteK v) w
    | v < 0
    , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      AstConcreteK u <=. AstTimesK (AstConcreteK $ negate v) (AstN1K NegateOp w)
  v@AstConcreteK{} <=. u = AstLeqK v u
  u <=. AstPlusK (AstFromPlain (AstConcreteK v)) w =
    u - AstFromPlain (AstConcreteK v) <=. w
  AstPlusK (AstFromPlain (AstConcreteK u)) w <=. v =
    AstFromPlain (AstConcreteK u) <=. v - w
  u <=. AstFromPlain (AstConcreteK v) =
    AstFromPlain (AstConcreteK (negate v)) <=. negate u
  AstFromPlain (AstConcreteK u) <=. AstTimesK (AstFromPlain (AstConcreteK v)) w
    | v > 0 && u >= 0
    , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      AstFromPlain (AstConcreteK ((u + v - 1) `quotH` v)) <=. w
        -- 10 == 5 * 2, 11 > 5 * 2
  AstFromPlain (AstConcreteK u) <=. AstTimesK (AstFromPlain (AstConcreteK v)) w
    | v > 0 && u < 0
    , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      AstFromPlain (AstConcreteK (u `quotH` v)) <=. w
        -- -10 == 5 * -2, -9 > 5 * -2
  AstFromPlain (AstConcreteK u) <=. AstTimesK (AstFromPlain (AstConcreteK v)) w
    | v < 0
    , Just Refl <- testEquality (typeRep @r) (typeRep @Int64) =
      AstFromPlain (AstConcreteK u)
      <=. AstTimesK (AstFromPlain (AstConcreteK $ negate v)) (AstN1K NegateOp w)
  v <=. u = AstConcreteK 0 <=. plainPart u - plainPart v

instance (AstSpan s, NumScalar r)
         => OrdH (AstTensor ms s) (TKS sh r) where
  AstPrimalPart u <=. AstPrimalPart v = u <=. v
  AstPlainPart @_ @s1 u <=. AstPlainPart @_ @s2 v
    | Just Refl <- sameAstSpan @s1 @s2 =
      u <=. v
  AstFromPrimal u <=. AstFromPrimal v = u <=. v
  AstFromDual{} <=. AstFromDual{} = AstBoolConst True
  AstFromPlain u <=. AstFromPlain v = u <=. v
  AstConvert c u <=. AstConvert _ v
    | FTKS ZSS x <- convertFTK c (ftkAst u)
    , Just Refl <- matchingFTK x (ftkAst u)
    , Just Refl <- matchingFTK x (ftkAst v) = u <=. v
  AstConcreteS u <=. AstConvert c v
    | FTKS ZSS (FTKScalar @rz) <- convertFTK c (ftkAst v)
    , FTKScalar @ry <- ftkAst v
    , Just Refl <- testEquality (typeRep @ry) (typeRep @rz) =
      AstConcreteK (unConcrete $ kfromS $ Concrete u) <=. v
  AstConcreteS u <=. AstConcreteS v =
    AstBoolConst $ Concrete @(TKS sh r) u <=. Concrete v
  u <=. AstPlusS (AstConcreteS v) w =
    u - AstConcreteS v <=. w
  AstPlusS (AstConcreteS u) w <=. v =
    AstConcreteS u <=. v - w
  u <=. AstConcreteS v =
    AstConcreteS (negate v) <=. negate u
  u <=. AstPlusS (AstFromPlain (AstConcreteS v)) w =
    u - AstFromPlain (AstConcreteS v) <=. w
  AstPlusS (AstFromPlain (AstConcreteS u)) w <=. v =
    AstFromPlain (AstConcreteS u) <=. v - w
  u <=. AstFromPlain (AstConcreteS v) =
    AstFromPlain (AstConcreteS (negate v)) <=. negate u
  AstVar u <=. AstVar v | u == v =
    AstBoolConst True
  AstConvert _ (AstVar u) <=. AstConvert _ (AstVar v)
    | varNameToAstVarId u == varNameToAstVarId v =
      AstBoolConst True
  v <=. u = AstLeqS (plainPart v) (plainPart u)


-- * AstRaw, AstNoVectorize and AstNoSimplify definitions

-- | An AST variant that doesn't vectorize terms and also builds them
-- with ordinary, non-simplifying constructors. It's based on sharing
-- rather than lets and commonly used as the instance for primals
-- inside ADVal and, consequently, used for evaluating delta expressions.
type role AstRaw nominal nominal
newtype AstRaw s y =
  AstRaw {unAstRaw :: AstTensor AstMethodShare s y}
 deriving Show

-- | An AST variant for testing that doesn't vectorize terms, but still
-- builds them using simplifying smart constructors.
type role AstNoVectorize nominal nominal
newtype AstNoVectorize s y =
  AstNoVectorize {unAstNoVectorize :: AstTensor AstMethodLet s y}
 deriving Show

-- | An AST variant for testing that vectorizes terms, but builds them
-- with ordinary, non-simplifying constructors.
type role AstNoSimplify nominal nominal
newtype AstNoSimplify s y =
  AstNoSimplify {unAstNoSimplify :: AstTensor AstMethodLet s y}
 deriving Show


-- * AstRaw, AstNoVectorize and AstNoSimplify type family instances

type instance PrimalOf (AstRaw s) = AstRaw (PrimalStepSpan s)
type instance DualOf (AstRaw s) = AstTensor AstMethodShare DualSpan
type instance PlainOf (AstRaw s) = AstRaw PlainSpan
type instance ShareOf (AstRaw s) = AstRaw s
type instance HFunOf (AstRaw s) x y = AstHFun s s x y
type instance BoolOf (AstRaw s) = AstBool AstMethodShare

type instance PrimalOf (AstNoVectorize s) = AstNoVectorize (PrimalStepSpan s)
type instance DualOf (AstNoVectorize s) = AstTensor AstMethodLet DualSpan
type instance PlainOf (AstNoVectorize s) = AstNoVectorize PlainSpan
type instance ShareOf (AstNoVectorize s) = AstRaw s
type instance HFunOf (AstNoVectorize s) x z = AstHFun s s x z
type instance BoolOf (AstNoVectorize s) = AstBool AstMethodLet

type instance PrimalOf (AstNoSimplify s) = AstNoSimplify (PrimalStepSpan s)
type instance DualOf (AstNoSimplify s) = AstTensor AstMethodLet DualSpan
type instance PlainOf (AstNoSimplify s) = AstNoSimplify PlainSpan
type instance ShareOf (AstNoSimplify s) = AstRaw s
type instance HFunOf (AstNoSimplify s) x z = AstHFun s s x z
type instance BoolOf (AstNoSimplify s) = AstBool AstMethodLet


-- * AstRaw, AstNoVectorize and AstNoSimplify other instances

instance EqH (AstTensor AstMethodShare s) y => EqH (AstRaw s) y where
  AstRaw v ==. AstRaw u = v ==. u
instance OrdH (AstTensor AstMethodShare s) y => OrdH (AstRaw s) y where
  AstRaw v <=. AstRaw u = v <=. u

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

instance EqH (AstTensor AstMethodLet s) y => EqH (AstNoVectorize s) y where
  AstNoVectorize v ==. AstNoVectorize u = v ==. u
instance OrdH (AstTensor AstMethodLet s) y => OrdH (AstNoVectorize s) y where
  AstNoVectorize v <=. AstNoVectorize u = v <=. u
deriving instance Eq (AstNoVectorize s y)
deriving instance Ord (AstNoVectorize s y)
deriving instance Num (AstTensor AstMethodLet s y) => Num (AstNoVectorize s y)
deriving instance (IntegralH (AstTensor AstMethodLet s y))
                  => IntegralH (AstNoVectorize s y)
deriving instance Fractional (AstTensor AstMethodLet s y)
                  => Fractional (AstNoVectorize s y)
deriving instance Floating (AstTensor AstMethodLet s y)
                  => Floating (AstNoVectorize s y)
deriving instance (RealFloatH (AstTensor AstMethodLet s y))
                  => RealFloatH (AstNoVectorize s y)

instance EqH (AstTensor AstMethodLet s) y => EqH (AstNoSimplify s) y where
  AstNoSimplify v ==. AstNoSimplify u = v ==. u
instance OrdH (AstTensor AstMethodLet s) y => OrdH (AstNoSimplify s) y where
  AstNoSimplify v <=. AstNoSimplify u = v <=. u
deriving instance Eq (AstNoSimplify s y)
deriving instance Ord (AstNoSimplify s y)
deriving instance Num (AstTensor AstMethodLet s y) => Num (AstNoSimplify s y)
deriving instance (IntegralH (AstTensor AstMethodLet s y))
                  => IntegralH (AstNoSimplify s y)
deriving instance Fractional (AstTensor AstMethodLet s y)
                  => Fractional (AstNoSimplify s y)
deriving instance Floating (AstTensor AstMethodLet s y)
                  => Floating (AstNoSimplify s y)
deriving instance (RealFloatH (AstTensor AstMethodLet s y))
                  => RealFloatH (AstNoSimplify s y)


-- * Misc

astLetFunNoSimplify
  :: forall y z s s2. AstSpan s
  => AstTensor AstMethodLet s y
  -> (AstTensor AstMethodLet s y -> AstTensor AstMethodLet s2 z)
  -> AstTensor AstMethodLet s2 z
astLetFunNoSimplify a f | astIsSmall True a = f a
                            -- too important an optimization to skip
astLetFunNoSimplify a f = case a of
  AstFromS' FTKScalar _ ->
    let (var, ast) = funToAst2 (ftkAst a) Nothing f
    in AstLet var a ast
  AstFromS' @y2 ftkz v ->
    let (var, ast) = funToAst2 (ftkAst v) Nothing (f . cAstFromS @y2 ftkz)
    in AstLet var v ast
  AstFromPrimal (AstFromS' FTKScalar _) ->
    let (var, ast) = funToAst2 (ftkAst a) Nothing f
    in AstLet var a ast
  AstFromPrimal (AstFromS' @y2 ftkz vRaw) ->
    let v = fromPrimal vRaw
        (var, ast) = funToAst2 (ftkAst v) Nothing (f . cAstFromS @y2 ftkz)
    in AstLet var v ast
  AstFromPlain (AstFromS' FTKScalar _) ->
    let (var, ast) = funToAst2 (ftkAst a) Nothing f
    in AstLet var a ast
  AstFromPlain (AstFromS' @y2 ftkz vRaw) ->
    let v = fromPlain vRaw
        (var, ast) = funToAst2 (ftkAst v) Nothing (f . cAstFromS @y2 ftkz)
    in AstLet var v ast
  _ -> case ftkAst a of
    ftk@(FTKR @_ @x2 sh' x) ->
      withShsFromShR sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst2 (FTKS sh x) Nothing
                        (f . cAstFromS @(TKS2 sh x2) ftk)
        in AstLet var (cAstSFromR @sh sh a) ast
             -- safe, because subsitution ruled out above
    ftk@(FTKX @_ @x sh' x) ->
      withShsFromShX sh' $ \(sh :: ShS sh) ->
        let (var, ast) =
              funToAst2 (FTKS sh x) Nothing
                        (f . cAstFromS @(TKS2 sh x) ftk)
        in AstLet var (cAstSFromX @sh sh a) ast
    -- processing product recursively may be not worth it
    ftk -> let (var, ast) = funToAst2 ftk Nothing f
           in AstLet var a ast

sunReplicateScal :: Nested.Elt a
                 => Nested.Shaped sh a -> Maybe a
sunReplicateScal (Nested.Shaped arr)
  | all (all (== 0) . take (shxLength (Nested.mshape arr)))
        (Mixed.marrayStrides arr)
  , shxSize (Nested.mshape arr) /= 0 =
    Just $ Nested.mindex arr $ ixxZero' $ Nested.mshape arr
sunReplicateScal _ = Nothing

sunReplicate1 :: Nested.Elt a
              => Nested.Shaped (n ': sh) a -> Maybe (Nested.Shaped sh a)
sunReplicate1 a | (snat :$$ _) <- Nested.sshape a =
  sunReplicateN (snat :$$ ZSS) a

sunReplicateN :: Nested.Elt a
              => ShS shm -> Nested.Shaped (shm ++ shn) a
              -> Maybe (Nested.Shaped shn a)
sunReplicateN shm a@(Nested.Shaped arr)
  | all (all (== 0) . take (shsLength shm)) (Mixed.marrayStrides arr)
  , shsSize shm /= 0 =
    Just $ Nested.sindexPartial a $ ixsZero shm
sunReplicateN _ _ = Nothing
