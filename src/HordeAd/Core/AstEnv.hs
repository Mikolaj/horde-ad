{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The environment and some helper operations for AST interpretation.
module HordeAd.Core.AstEnv
  ( -- * The environment and operations for extending it
    AstEnv, AstEnvElem(..)
  , extendEnvR, extendEnvS, extendEnvHVector, extendEnvHFun, extendEnvD
    -- * The operations for interpreting binding (visible lambdas)
  , interpretLambdaI, interpretLambdaIS, interpretLambdaIHVector
  , interpretLambdaIndex, interpretLambdaIndexS
  , interpretLambdaIndexToIndex, interpretLambdaIndexToIndexS
  , interpretLambdaHVector, interpretLambdaHVectorS
  , interpretLambda2, interpretLambda2S
  , interpretLambdaRHR, interpretLambdaSHS
  , interpretLambdaRHH, interpretLambdaSHH
  , interpretLambdaHHH, interpretLambdaHHHHH
  , interpretLambda3, interpretLambda3S
  , interpretLambdaRRRH, interpretLambdaSSSH
  , interpretLambda4, interpretLambda4S
  , interpretLambdaRHRHR, interpretLambdaSHSHS
  , interpretLambdaRHRHH, interpretLambdaSHSHH
    -- * Interpretation of arithmetic, boolean and relation operations
  , interpretAstN1, interpretAstN2, interpretAstR1, interpretAstR2
  , interpretAstI2, interpretAstB2, interpretAstRelOp
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.Shape as Sh
import qualified Data.EnumMap.Strict as EM
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat)
import           Type.Reflection (typeRep)

import           HordeAd.Core.Ast
import           HordeAd.Core.HVector
import           HordeAd.Core.HVectorOps
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex
import           HordeAd.Util.SizedList

-- * The environment and operations for extending it

-- | The environment that keeps variables values during interpretation
type AstEnv ranked = EM.EnumMap AstVarId (AstEnvElem ranked)

type role AstEnvElem nominal
data AstEnvElem (ranked :: RankedTensorType) where
  AstEnvElemRanked :: (GoodScalar r, KnownNat n)
                   => ranked r n -> AstEnvElem ranked
  AstEnvElemShaped :: (GoodScalar r, Sh.Shape sh)
                   => ShapedOf ranked r sh -> AstEnvElem ranked
  AstEnvElemHFun :: HFunOf ranked -> AstEnvElem ranked

deriving instance ( CRanked ranked Show, CShaped (ShapedOf ranked) Show
                  , Show (HFunOf ranked) )
                  => Show (AstEnvElem ranked)

-- An informal invariant: if s is FullSpan, ranked is dual numbers,
-- and if s is PrimalSpan, ranked is their primal part.
-- The same for all the function below.
extendEnvR :: forall ranked r n s.
              (KnownNat n, GoodScalar r)
           => AstVarName (AstRanked s) r n -> ranked r n
           -> AstEnv ranked -> AstEnv ranked
extendEnvR !(AstVarName varId) !t !env =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvR: duplicate " ++ show varId)
                   varId (AstEnvElemRanked t) env

extendEnvS :: forall ranked r sh s.
              (Sh.Shape sh, GoodScalar r)
           => AstVarName (AstShaped s) r sh -> ShapedOf ranked r sh
           -> AstEnv ranked -> AstEnv ranked
extendEnvS !(AstVarName varId) !t !env =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvS: duplicate " ++ show varId)
                   varId (AstEnvElemShaped t) env

extendEnvHVector :: forall ranked. ADReady ranked
                 => [AstDynamicVarName] -> HVector ranked
                 -> AstEnv ranked -> AstEnv ranked
extendEnvHVector vars !pars !env = assert (length vars == V.length pars) $
  foldr extendEnvD env $ zip vars (V.toList pars)

extendEnvHFun :: AstVarId -> HFunOf ranked
              -> AstEnv ranked -> AstEnv ranked
extendEnvHFun !varId !t !env =
  EM.insertWithKey (\_ _ _ -> error $ "extendEnvHFun: duplicate " ++ show varId)
                   varId (AstEnvElemHFun t) env

-- We don't need to manually pick a specialization for the existential
-- variable r2, because the operations do not depend on r2.
extendEnvD :: forall ranked. ADReady ranked
           => (AstDynamicVarName, DynamicTensor ranked)
           -> AstEnv ranked
           -> AstEnv ranked
extendEnvD vd@(AstDynamicVarName @ty @r @sh varId, d) !env = case d of
  DynamicRanked @r3 @n3 u
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- matchingRank @sh @n3
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      extendEnvR (AstVarName varId) u env
  DynamicShaped @r3 @sh3 u
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      extendEnvS (AstVarName varId) u env
  DynamicRankedDummy @r3 @sh3 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @Nat)
    , Just Refl <- sameShape @sh3 @sh
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      withListShape (Sh.shapeT @sh) $ \sh4 ->
        extendEnvR @ranked @r (AstVarName varId) (rzero sh4) env
  DynamicShapedDummy @r3 @sh3 _ _
    | Just Refl <- testEquality (typeRep @ty) (typeRep @[Nat])
    , Just Refl <- sameShape @sh3 @sh
    , Just Refl <- testEquality (typeRep @r) (typeRep @r3) ->
      extendEnvS @ranked @r @sh (AstVarName varId) 0 env
  _ -> error $ "extendEnvD: impossible type"
               `showFailure`
               ( vd, typeRep @ty, typeRep @r, Sh.shapeT @sh
               , scalarDynamic d, shapeDynamic d )

extendEnvI :: ( RankedTensor ranked
              , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
           => IntVarName -> IntOf ranked -> AstEnv ranked
           -> AstEnv ranked
extendEnvI var !i !env = extendEnvR var (rconstant i) env

extendEnvVars :: forall ranked m.
                 ( RankedTensor ranked
                 , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
              => AstVarList m -> IndexOf ranked m
              -> AstEnv ranked
              -> AstEnv ranked
extendEnvVars vars !ix !env =
  let assocs = zip (sizedListToList vars) (indexToList ix)
  in foldr (uncurry extendEnvI) env assocs

extendEnvVarsS :: forall ranked sh.
                  ( RankedTensor ranked
                  , RankedOf (PrimalOf ranked) ~ PrimalOf ranked )
               => AstVarListS sh -> IndexSh ranked sh
               -> AstEnv ranked
               -> AstEnv ranked
extendEnvVarsS vars !ix !env =
  let assocs = zip (ShapedList.sizedListToList vars)
                   (ShapedList.sizedListToList ix)
  in foldr (uncurry extendEnvI) env assocs


-- * The operations for interpreting binding (visible lambdas)

interpretLambdaI
  :: forall ranked n s r.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked -> (IntVarName, AstRanked s r n)
  -> IntOf ranked
  -> ranked r n
{-# INLINE interpretLambdaI #-}
interpretLambdaI f !env (!var, !ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIS
  :: forall ranked sh n s r.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstShaped s r sh -> ShapedOf ranked r sh)
  -> AstEnv ranked -> (IntVarName, AstShaped s r sh)
  -> IntSh ranked n
  -> ShapedOf ranked r sh
{-# INLINE interpretLambdaIS #-}
interpretLambdaIS f !env (!var, ast) =
  \i -> f (extendEnvI var (ShapedList.unShapedNat i) env) ast

interpretLambdaIHVector
  :: forall ranked s.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked -> (IntVarName, AstHVector s)
  -> IntOf ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaIHVector #-}
interpretLambdaIHVector f !env (!var, !ast) =
  \i -> f (extendEnvI var i env) ast

interpretLambdaIndex
  :: forall ranked s r m n.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked -> (AstVarList m, AstRanked s r n)
  -> IndexOf ranked m
  -> ranked r n
{-# INLINE interpretLambdaIndex #-}
interpretLambdaIndex f !env (!vars, !ast) =
  \ix -> f (extendEnvVars vars ix env) ast

interpretLambdaIndexS
  :: forall sh sh2 ranked s r.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstShaped s r sh -> ShapedOf ranked r sh)
  -> AstEnv ranked -> (AstVarListS sh2, AstShaped s r sh)
  -> IndexSh ranked sh2
  -> ShapedOf ranked r sh
{-# INLINE interpretLambdaIndexS #-}
interpretLambdaIndexS f !env (!vars, !ast) =
  \ix -> f (extendEnvVarsS vars ix env) ast

interpretLambdaIndexToIndex
  :: forall ranked m n.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstInt -> IntOf ranked)
  -> AstEnv ranked -> (AstVarList m, AstIndex n)
  -> IndexOf ranked m
  -> IndexOf ranked n
{-# INLINE interpretLambdaIndexToIndex #-}
interpretLambdaIndexToIndex f !env (!vars, !asts) =
  \ix -> f (extendEnvVars vars ix env) <$> asts

interpretLambdaIndexToIndexS
  :: forall ranked sh sh2.
     (RankedTensor ranked, RankedOf (PrimalOf ranked) ~ PrimalOf ranked)
  => (AstEnv ranked -> AstInt -> IntOf ranked)
  -> AstEnv ranked -> (AstVarListS sh, AstIndexS sh2)
  -> IndexSh ranked sh
  -> IndexSh ranked sh2
{-# INLINE interpretLambdaIndexToIndexS #-}
interpretLambdaIndexToIndexS f !env (!vars, !asts) =
  \ix -> f (extendEnvVarsS vars ix env) <$> asts

interpretLambdaHVector
  :: forall s ranked r n. ADReady ranked
  => (AstEnv ranked -> AstRanked s r n -> ranked r n)
  -> AstEnv ranked
  -> ([AstDynamicVarName], AstRanked s r n)
  -> HVector ranked
  -> ranked r n
{-# INLINE interpretLambdaHVector #-}
interpretLambdaHVector f !env (!vars, !ast) =
  \pars -> f (extendEnvHVector vars pars env) ast

interpretLambdaHVectorS
  :: forall s ranked r sh. ADReady ranked
  => (AstEnv ranked -> AstShaped s r sh -> ShapedOf ranked r sh)
  -> AstEnv ranked
  -> ([AstDynamicVarName], AstShaped s r sh)
  -> HVector ranked
  -> ShapedOf ranked r sh
{-# INLINE interpretLambdaHVectorS #-}
interpretLambdaHVectorS f !env (!vars, !ast) =
  \pars -> f (extendEnvHVector vars pars env) ast

interpretLambda2
  :: forall s ranked rn rm n m.
     (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
  => (AstEnv ranked -> AstRanked s rn n -> ranked rn n)
  -> AstEnv ranked
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

interpretLambda2S
  :: forall s ranked rn rm sh shm.
     (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm)
  => (AstEnv ranked -> AstShaped s rn sh -> ShapedOf ranked rn sh)
  -> AstEnv ranked
  -> ( AstVarName (AstShaped s) rn sh
     , AstVarName (AstShaped s) rm shm
     , AstShaped s rn sh )
  -> ShapedOf ranked rn sh -> ShapedOf ranked rm shm
  -> ShapedOf ranked rn sh
{-# INLINE interpretLambda2S #-}
interpretLambda2S f !env (!varn, !varm, !ast) =
  \x0 as -> let envE = extendEnvS varn x0
                       $ extendEnvS varm as env
            in f envE ast

interpretLambdaRHR
  :: forall s ranked rn n.
     (GoodScalar rn, KnownNat n, ADReady ranked)
  => (AstEnv ranked -> AstRanked s rn n -> ranked rn n)
  -> AstEnv ranked
  -> ( AstVarName (AstRanked s) rn n
     , [AstDynamicVarName]
     , AstRanked s rn n )
  -> ranked rn n -> HVector ranked
  -> ranked rn n
{-# INLINE interpretLambdaRHR #-}
interpretLambdaRHR f !env (!varn, !varm, !ast) =
  \x0 as -> let envE = extendEnvR varn x0 env
            in f (extendEnvHVector varm as envE) ast

interpretLambdaSHS
  :: forall s ranked rn sh.
     (GoodScalar rn, Sh.Shape sh, ADReady ranked)
  => (AstEnv ranked -> AstShaped s rn sh -> ShapedOf ranked rn sh)
  -> AstEnv ranked
  -> ( AstVarName (AstShaped s) rn sh
     , [AstDynamicVarName]
     , AstShaped s rn sh )
  -> ShapedOf ranked rn sh -> HVector ranked
  -> ShapedOf ranked rn sh
{-# INLINE interpretLambdaSHS #-}
interpretLambdaSHS f !env (!varn, !varm, !ast) =
  \x0 as -> let envE = extendEnvS varn x0 env
            in f (extendEnvHVector varm as envE) ast

interpretLambdaRHH
  :: forall s ranked rn n.
     (GoodScalar rn, KnownNat n, ADReady ranked)
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( AstVarName (AstRanked s) rn n
     , [AstDynamicVarName]
     , AstHVector s )
  -> ranked rn n -> HVector ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaRHH #-}
interpretLambdaRHH f !env (!varn, !varm, !ast) =
  \x0 as -> let envE = extendEnvR varn x0 env
            in f (extendEnvHVector varm as envE) ast

interpretLambdaSHH
  :: forall s ranked rn sh.
     (GoodScalar rn, Sh.Shape sh, ADReady ranked)
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( AstVarName (AstShaped s) rn sh
     , [AstDynamicVarName]
     , AstHVector s )
  -> ShapedOf ranked rn sh -> HVector ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaSHH #-}
interpretLambdaSHH f !env (!varn, !varm, !ast) =
  \x0 as -> let envE = extendEnvS varn x0 env
            in f (extendEnvHVector varm as envE) ast

interpretLambdaHHH
  :: forall s ranked. ADReady ranked
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( [AstDynamicVarName]
     , [AstDynamicVarName]
     , AstHVector s )
  -> HVector ranked -> HVector ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaHHH #-}
interpretLambdaHHH f !env (!vs1, !vs2, !ast) =
  \w1 w2 -> let env1 = extendEnvHVector vs1 w1 env
            in f (extendEnvHVector vs2 w2 env1) ast

interpretLambdaHHHHH
  :: forall s ranked. ADReady ranked
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( [AstDynamicVarName]
     , [AstDynamicVarName]
     , [AstDynamicVarName]
     , [AstDynamicVarName]
     , AstHVector s )
  -> HVector ranked -> HVector ranked -> HVector ranked -> HVector ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaHHHHH #-}
interpretLambdaHHHHH f !env (!vs1, !vs2, !vs3, !vs4, !ast) =
  \w1 w2 w3 w4 -> let env1 = extendEnvHVector vs1 w1 env
                      env2 = extendEnvHVector vs2 w2 env1
                      env3 = extendEnvHVector vs3 w3 env2
                  in f (extendEnvHVector vs4 w4 env3) ast

interpretLambda3
  :: forall s ranked rn rm n m.
     (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rm m
     , AstHVector s )
  -> ranked rn n -> ranked rn n -> ranked rm m
  -> HVectorOf ranked
{-# INLINE interpretLambda3 #-}
interpretLambda3 f !env (!varDt, !varn, !varm, !ast) =
  \cx x0 as -> let envE = extendEnvR varDt cx
                          $ extendEnvR varn x0
                          $ extendEnvR varm as env
               in f envE ast

interpretLambda3S
  :: forall s ranked rn rm sh shm.
     (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm)
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( AstVarName (AstShaped s) rn sh
     , AstVarName (AstShaped s) rn sh
     , AstVarName (AstShaped s) rm shm
     , AstHVector s )
  -> ShapedOf ranked rn sh -> ShapedOf ranked rn sh -> ShapedOf ranked rm shm
  -> HVectorOf ranked
{-# INLINE interpretLambda3S #-}
interpretLambda3S f !env (!varDt, !varn, !varm, !ast) =
  \cx x0 as -> let envE = extendEnvS varDt cx
                          $ extendEnvS varn x0
                          $ extendEnvS varm as env
               in f envE ast

interpretLambdaRRRH
  :: forall s ranked rn n.
     (GoodScalar rn, KnownNat n, ADReady ranked)
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rn n
     , [AstDynamicVarName]
     , AstHVector s )
  -> ranked rn n -> ranked rn n -> HVector ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaRRRH #-}
interpretLambdaRRRH f !env (!varDt, !varn, !varm, !ast) =
  \cx x0 as -> let envE = extendEnvR varDt cx
                          $ extendEnvR varn x0 env
               in f (extendEnvHVector varm as envE) ast

interpretLambdaSSSH
  :: forall s ranked rn sh.
     (GoodScalar rn, Sh.Shape sh, ADReady ranked)
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( AstVarName (AstShaped s) rn sh
     , AstVarName (AstShaped s) rn sh
     , [AstDynamicVarName]
     , AstHVector s )
  -> ShapedOf ranked rn sh -> ShapedOf ranked rn sh -> HVector ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaSSSH #-}
interpretLambdaSSSH f !env (!varDt, !varn, !varm, !ast) =
  \cx x0 as -> let envE = extendEnvS varDt cx
                          $ extendEnvS varn x0 env
               in f (extendEnvHVector varm as envE) ast

interpretLambda4
  :: forall s ranked rn rm n m.
     (GoodScalar rn, GoodScalar rm, KnownNat n, KnownNat m)
  => (AstEnv ranked -> AstRanked s rn n -> ranked rn n)
  -> AstEnv ranked
  -> ( AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rm m
     , AstVarName (AstRanked s) rn n
     , AstVarName (AstRanked s) rm m
     , AstRanked s rn n )
  -> ranked rn n -> ranked rm m
  -> ranked rn n -> ranked rm m
  -> ranked rn n
{-# INLINE interpretLambda4 #-}
interpretLambda4 f !env (!varDx, !varDa, !varn, !varm, !ast) =
  \cx ca x0 as -> let envE = extendEnvR varDx cx
                             $ extendEnvR varDa ca
                             $ extendEnvR varn x0
                             $ extendEnvR varm as env
                  in f envE ast

interpretLambda4S
  :: forall s ranked rn rm sh shm.
     (GoodScalar rn, GoodScalar rm, Sh.Shape sh, Sh.Shape shm)
  => (AstEnv ranked -> AstShaped s rn sh -> ShapedOf ranked rn sh)
  -> AstEnv ranked
  -> ( AstVarName (AstShaped s) rn sh
     , AstVarName (AstShaped s) rm shm
     , AstVarName (AstShaped s) rn sh
     , AstVarName (AstShaped s) rm shm
     , AstShaped s rn sh )
  -> ShapedOf ranked rn sh -> ShapedOf ranked rm shm
  -> ShapedOf ranked rn sh -> ShapedOf ranked rm shm
  -> ShapedOf ranked rn sh
{-# INLINE interpretLambda4S #-}
interpretLambda4S f !env (!varDx, !varDa, !varn, !varm, !ast) =
  \cx ca x0 as -> let envE = extendEnvS varDx cx
                             $ extendEnvS varDa ca
                             $ extendEnvS varn x0
                             $ extendEnvS varm as env
                  in f envE ast

interpretLambdaRHRHR
  :: forall s ranked rn n.
     (GoodScalar rn, KnownNat n, ADReady ranked)
  => (AstEnv ranked -> AstRanked s rn n -> ranked rn n)
  -> AstEnv ranked
  -> ( AstVarName (AstRanked s) rn n
     , [AstDynamicVarName]
     , AstVarName (AstRanked s) rn n
     , [AstDynamicVarName]
     , AstRanked s rn n )
  -> ranked rn n -> HVector ranked
  -> ranked rn n -> HVector ranked
  -> ranked rn n
{-# INLINE interpretLambdaRHRHR #-}
interpretLambdaRHRHR f !env (!varDx, !varDa, !varn, !varm, !ast) =
  \cx ca x0 as -> let envE = extendEnvR varDx cx
                             $ extendEnvR varn x0 env
                  in f (extendEnvHVector varDa ca
                        $ extendEnvHVector varm as envE) ast

interpretLambdaSHSHS
  :: forall s ranked rn sh.
     (GoodScalar rn, Sh.Shape sh, ADReady ranked)
  => (AstEnv ranked -> AstShaped s rn sh -> ShapedOf ranked rn sh)
  -> AstEnv ranked
  -> ( AstVarName (AstShaped s) rn sh
     , [AstDynamicVarName]
     , AstVarName (AstShaped s) rn sh
     , [AstDynamicVarName]
     , AstShaped s rn sh )
  -> ShapedOf ranked rn sh -> HVector ranked
  -> ShapedOf ranked rn sh -> HVector ranked
  -> ShapedOf ranked rn sh
{-# INLINE interpretLambdaSHSHS #-}
interpretLambdaSHSHS f !env (!varDx, !varDa, !varn, !varm, !ast) =
  \cx ca x0 as -> let envE = extendEnvS varDx cx
                             $ extendEnvS varn x0 env
                  in f (extendEnvHVector varDa ca
                        $ extendEnvHVector varm as envE) ast

interpretLambdaRHRHH
  :: forall s ranked rn n.
     (GoodScalar rn, KnownNat n, ADReady ranked)
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( AstVarName (AstRanked s) rn n
     , [AstDynamicVarName]
     , AstVarName (AstRanked s) rn n
     , [AstDynamicVarName]
     , AstHVector s )
  -> ranked rn n -> HVector ranked
  -> ranked rn n -> HVector ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaRHRHH #-}
interpretLambdaRHRHH f !env (!varDx, !varDa, !varn, !varm, !ast) =
  \cx ca x0 as -> let envE = extendEnvR varDx cx
                             $ extendEnvR varn x0 env
                  in f (extendEnvHVector varDa ca
                        $ extendEnvHVector varm as envE) ast

interpretLambdaSHSHH
  :: forall s ranked rn sh.
     (GoodScalar rn, Sh.Shape sh, ADReady ranked)
  => (AstEnv ranked -> AstHVector s -> HVectorOf ranked)
  -> AstEnv ranked
  -> ( AstVarName (AstShaped s) rn sh
     , [AstDynamicVarName]
     , AstVarName (AstShaped s) rn sh
     , [AstDynamicVarName]
     , AstHVector s )
  -> ShapedOf ranked rn sh -> HVector ranked
  -> ShapedOf ranked rn sh -> HVector ranked
  -> HVectorOf ranked
{-# INLINE interpretLambdaSHSHH #-}
interpretLambdaSHSHH f !env (!varDx, !varDa, !varn, !varm, !ast) =
  \cx ca x0 as -> let envE = extendEnvS varDx cx
                             $ extendEnvS varn x0 env
                  in f (extendEnvHVector varDa ca
                        $ extendEnvHVector varm as envE) ast


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
