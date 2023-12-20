{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The environment and some helper operations for AST interpretation.
module HordeAd.Core.AstEnv
  ( -- * The environment and operations for extending it
    AstEnv, AstEnvElem(..)
  , extendEnvS, extendEnvR, extendEnvDR, extendEnvDS
  , extendEnvPars, extendEnvParsS
    -- * The operations for interpreting binding (visible lambdas)
  , interpretLambdaI, interpretLambdaIS
  , interpretLambdaIndex, interpretLambdaIndexS
  , interpretLambdaIndexToIndex, interpretLambdaIndexToIndexS
  , interpretLambdaDomains, interpretLambdaDomainsS
  , interpretLambda2, interpretLambda3, interpretLambda4
    -- * Interpretation of arithmetic, boolean and relation operations
  , interpretAstN1, interpretAstN2, interpretAstR1, interpretAstR2
  , interpretAstI2, interpretAstB2, interpretAstRelOp
  ) where

import Prelude

import qualified Data.Array.Shape as Sh
import qualified Data.EnumMap.Strict as EM
import           Data.Kind (Type)
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex
import           HordeAd.Util.SizedList

-- * The environment and operations for extending it

-- | The environment that keeps variables values during interpretation
type AstEnv ranked shaped = EM.EnumMap AstVarId (AstEnvElem ranked shaped)

type role AstEnvElem representational representational
data AstEnvElem :: RankedTensorKind -> ShapedTensorKind -> Type where
  AstEnvElemR :: (KnownNat n, GoodScalar r)
              => ranked r n -> AstEnvElem ranked shaped
  AstEnvElemS :: (Sh.Shape sh, GoodScalar r)
              => shaped r sh -> AstEnvElem ranked shaped
deriving instance (CRanked ranked Show, CShaped shaped Show)
                  => Show (AstEnvElem ranked shaped)

-- An informal invariant: if s is FullSpan, ranked is dual numbers,
-- and if s is PrimalSpan, ranked is their primal part.
-- The same for all the function below.
extendEnvR :: forall ranked shaped r n s.
              (KnownNat n, GoodScalar r)
           => AstVarName (AstRanked s) r n -> ranked r n
           -> AstEnv ranked shaped -> AstEnv ranked shaped
extendEnvR (AstVarName var) !t !env =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvR: duplicate " ++ show var)
                   var (AstEnvElemR t) env

extendEnvS :: forall ranked shaped r sh s.
              (Sh.Shape sh, GoodScalar r)
           => AstVarName (AstShaped s) r sh -> shaped r sh
           -> AstEnv ranked shaped -> AstEnv ranked shaped
extendEnvS (AstVarName var) !t !env =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvS: duplicate " ++ show var)
                   var (AstEnvElemS t) env

extendEnvDR :: forall ranked shaped s. ConvertTensor ranked shaped
            => ( AstDynamicVarName (AstRanked s)
               , DynamicExists (DynamicOf ranked) )
            -> AstEnv ranked shaped
            -> AstEnv ranked shaped
extendEnvDR (AstDynamicVarName @_ @sh @r @y var, DynamicExists @r2 d) !env =
  -- We don't need to manually pick a specialization for the existential
  -- variable r2, because rfromD does not depend on r2.
  case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl ->
      withListShape (Sh.shapeT @sh) $ \ (_ :: Shape n Int) ->
        gcastWith (unsafeCoerce Refl :: n :~: y) $
        extendEnvR var (rfromD d) env
    _ -> error "extendEnvDR: type mismatch"

extendEnvDS :: ConvertTensor ranked shaped
            => ( AstDynamicVarName (AstShaped s)
               , DynamicExists (DynamicOf ranked) )
            -> AstEnv ranked shaped
            -> AstEnv ranked shaped
extendEnvDS (AstDynamicVarName @_ @sh @r @y var, DynamicExists @r2 d) !env =
  -- We don't need to manually pick a specialization for the existential
  -- variable r2, because sfromD does not depend on r2.
  case testEquality (typeRep @r) (typeRep @r2) of
    Just Refl -> gcastWith (unsafeCoerce Refl :: sh :~: y) $
                 extendEnvS var (sfromD d) env
    _ -> error "extendEnvDS: type mismatch"

extendEnvI :: ( RankedTensor ranked
              , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
           => IntVarName -> IntOf ranked -> AstEnv ranked shaped
           -> AstEnv ranked shaped
extendEnvI var !i !env = extendEnvR var (rconstant i) env

extendEnvVars :: forall ranked shaped m.
                 ( RankedTensor ranked
                 , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
              => AstVarList m -> IndexOf ranked m
              -> AstEnv ranked shaped
              -> AstEnv ranked shaped
extendEnvVars vars !ix !env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

extendEnvVarsS :: forall ranked shaped sh.
                  ( RankedTensor ranked
                  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
               => AstVarListS sh -> IndexSh ranked sh
               -> AstEnv ranked shaped
               -> AstEnv ranked shaped
extendEnvVarsS vars !ix !env =
  let assocs = zip (ShapedList.sizedListToList vars)
                   (ShapedList.sizedListToList ix)
  in foldr (uncurry extendEnvI) env assocs

extendEnvPars :: forall ranked shaped s. ConvertTensor ranked shaped
              => [AstDynamicVarName (AstRanked s)] -> Domains (DynamicOf ranked)
              -> AstEnv ranked shaped
              -> AstEnv ranked shaped
extendEnvPars vars !pars !env =
  let assocs = zip vars (V.toList pars)
  in foldr extendEnvDR env assocs

extendEnvParsS :: forall ranked shaped s. ConvertTensor ranked shaped
               => [AstDynamicVarName (AstShaped s)]
               -> Domains (DynamicOf ranked)
               -> AstEnv ranked shaped
               -> AstEnv ranked shaped
extendEnvParsS vars !pars !env =
  let assocs = zip vars (V.toList pars)
  in foldr extendEnvDS env assocs


-- * The operations for interpreting binding (visible lambdas)

interpretLambdaI
  :: forall ranked shaped n s r.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked shaped -> (IntVarName, AstRanked s r n)
  -> IntOf ranked
  -> ranked r n
{-# INLINE interpretLambdaI #-}
interpretLambdaI f !env (!var, !ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIS
  :: forall ranked shaped sh n s r.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstShaped s r sh -> shaped r sh)
  -> AstEnv ranked shaped -> (IntVarName, AstShaped s r sh)
  -> IntSh ranked n
  -> shaped r sh
{-# INLINE interpretLambdaIS #-}
interpretLambdaIS f !env (!var, ast) =
  \i -> f (extendEnvI var (ShapedList.unShapedNat i) env) ast

interpretLambdaIndex
  :: forall ranked shaped s r m n.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked shaped -> (AstVarList m, AstRanked s r n)
  -> IndexOf ranked m
  -> ranked r n
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f !env (!vars, !ast) =
  \ix -> f (extendEnvVars vars ix env) ast

interpretLambdaIndexS
  :: forall sh sh2 ranked shaped s r.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstShaped s r sh -> shaped r sh)
  -> AstEnv ranked shaped -> (AstVarListS sh2, AstShaped s r sh)
  -> IndexSh ranked sh2
  -> shaped r sh
{-# INLINE interpretLambdaIndexS #-}
interpretLambdaIndexS f !env (!vars, !ast) =
  \ix -> f (extendEnvVarsS vars ix env) ast

interpretLambdaIndexToIndex
  :: forall ranked shaped m n.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstInt -> IntOf ranked)
  -> AstEnv ranked shaped -> (AstVarList m, AstIndex n)
  -> IndexOf ranked m
  -> IndexOf ranked n
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f !env (!vars, !asts) =
  \ix -> f (extendEnvVars vars ix env) <$> asts

interpretLambdaIndexToIndexS
  :: forall ranked shaped sh sh2.
     ( RankedTensor ranked
     , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
  => (AstEnv ranked shaped -> AstInt -> IntOf ranked)
  -> AstEnv ranked shaped -> (AstVarListS sh, AstIndexS sh2)
  -> IndexSh ranked sh
  -> IndexSh ranked sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f !env (!vars, !asts) =
  \ix -> f (extendEnvVarsS vars ix env) <$> asts

interpretLambdaDomains
  :: forall s ranked shaped r n. ConvertTensor ranked shaped
  => (AstEnv ranked shaped -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked shaped
  -> ([AstDynamicVarName (AstRanked s)], AstRanked s r n)
  -> Domains (DynamicOf ranked)
  -> ranked r n
{-# INLINE interpretLambdaDomains #-}
interpretLambdaDomains f !env (!vars, !ast) =
  \pars -> f (extendEnvPars vars pars env) ast

interpretLambdaDomainsS
  :: forall s ranked shaped r sh. ConvertTensor ranked shaped
  => (AstEnv ranked shaped -> AstShaped s r sh -> shaped r sh)
  -> AstEnv ranked shaped
  -> ([AstDynamicVarName (AstShaped s)], AstShaped s r sh)
  -> Domains (DynamicOf ranked)
  -> shaped r sh
{-# INLINE interpretLambdaDomainsS #-}
interpretLambdaDomainsS f !env (!vars, !ast) =
  \pars -> f (extendEnvParsS vars pars env) ast

interpretLambda2
  :: forall s ranked shaped rn rm n m.
     (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
  => (AstEnv ranked shaped -> AstRanked s rn n -> ranked rn n)
  -> AstEnv ranked shaped
  -> ( AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rm m
     , AstRanked s rn n )
  -> ranked rn n -> ranked rm m
  -> ranked rn n
{-# INLINE interpretLambda2 #-}
interpretLambda2 f !env (!varn, !varm, !ast) =
  \x0 as -> let envE = extendEnvR varn x0
                       $ extendEnvR varm as env
            in f envE ast

interpretLambda3
  :: forall s ranked shaped rn rm n m.
     (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
  => (AstEnv ranked shaped -> AstDomains s -> DomainsOf ranked)
  -> AstEnv ranked shaped
  -> ( AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rm m
     , AstDomains s )
  -> ranked rn n -> ranked rn n -> ranked rm m
  -> DomainsOf ranked
{-# INLINE interpretLambda3 #-}
interpretLambda3 f !env (!varDt, !varn, !varm, !ast) =
  \cx x0 as -> let envE = extendEnvR varDt cx
                          $ extendEnvR varn x0
                          $ extendEnvR varm as env
               in f envE ast

interpretLambda4
  :: forall s ranked shaped rn rm n m.
     (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
  => (AstEnv ranked shaped -> AstRanked s rn n -> ranked rn n)
  -> AstEnv ranked shaped
  -> ( AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rm m
     , AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rm m
     , AstRanked s rn n )
  -> ranked rn n -> ranked rm m -> ranked rn n -> ranked rm m
  -> ranked rn n
{-# INLINE interpretLambda4 #-}
interpretLambda4 f !env (!varDx, !varDa, !varn, !varm, !ast) =
  \cx ca x0 as -> let envE = extendEnvR varDx cx
                             $ extendEnvR varDa ca
                             $ extendEnvR varn x0
                             $ extendEnvR varm as env
                  in f envE ast


-- * Interpretation of arithmetic, boolean and relation operations

-- TODO: when the code again tests with GHC >= 9.6, check whether
-- these INLINEs are still needed (removal causes 10% slowdown ATM).
interpretAstN1 :: Num a
               => OpCodeNum1 -> a -> a
{-# INLINE interpretAstN1 #-}
interpretAstN1 NegateOp u = negate u
interpretAstN1 AbsOp u = abs u
interpretAstN1 SignumOp u = signum u

interpretAstN2 :: Num a
               => OpCodeNum2 -> a -> a -> a
{-# INLINE interpretAstN2 #-}
interpretAstN2 MinusOp u v = u - v
interpretAstN2 TimesOp u v = u * v

interpretAstR1 :: RealFloat a
               => OpCode1 -> a -> a
{-# INLINE interpretAstR1 #-}
interpretAstR1 RecipOp u = recip u
interpretAstR1 ExpOp u = exp u
interpretAstR1 LogOp u = log u
interpretAstR1 SqrtOp u = sqrt u
interpretAstR1 SinOp u = sin u
interpretAstR1 CosOp u = cos u
interpretAstR1 TanOp u = tan u
interpretAstR1 AsinOp u = asin u
interpretAstR1 AcosOp u = acos u
interpretAstR1 AtanOp u = atan u
interpretAstR1 SinhOp u = sinh u
interpretAstR1 CoshOp u = cosh u
interpretAstR1 TanhOp u = tanh u
interpretAstR1 AsinhOp u = asinh u
interpretAstR1 AcoshOp u = acosh u
interpretAstR1 AtanhOp u = atanh u

interpretAstR2 :: RealFloat a
               => OpCode2 -> a -> a -> a
{-# INLINE interpretAstR2 #-}
interpretAstR2 DivideOp u v = u / v
interpretAstR2 PowerOp u v = u ** v
interpretAstR2 LogBaseOp u v = logBase u v
interpretAstR2 Atan2Op u v = atan2 u v

interpretAstI2 :: Integral a
               => OpCodeIntegral2 -> a -> a -> a
{-# INLINE interpretAstI2 #-}
interpretAstI2 QuotOp u v = quot u v
interpretAstI2 RemOp u v = rem u v

interpretAstB2 :: Boolean b
               => OpCodeBool -> b -> b -> b
{-# INLINE interpretAstB2 #-}
interpretAstB2 AndOp u v = u &&* v
interpretAstB2 OrOp u v = u ||* v

interpretAstRelOp :: (EqF f, OrdF f, GoodScalar r, HasSingletonDict y)
                  => OpCodeRel -> f r y -> f r y -> BoolOf f
{-# INLINE interpretAstRelOp #-}
interpretAstRelOp EqOp u v = u ==. v
interpretAstRelOp NeqOp u v = u /=. v
interpretAstRelOp LeqOp u v = u <=. v
interpretAstRelOp GeqOp u v = u >=. v
interpretAstRelOp LsOp u v = u <. v
interpretAstRelOp GtOp u v = u >. v
