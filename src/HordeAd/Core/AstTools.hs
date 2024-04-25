{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | An assortment of operations working on AST of the code to be differentiated
-- or resulting from the differentiation.
module HordeAd.Core.AstTools
  ( -- * Shape calculation
    shapeAst, lengthAst, shapeAstHVector, shapeAstHFun, domainShapesAstHFun
    -- * Variable occurrence detection
  , varInAst, varInAstBool, varInIndex
  , varInAstS, varInIndexS
  , varInAstDynamic, varInAstHVector
  , varNameInAst, varNameInAstS, varNameInAstHVector
  , varInAstBindingsCase
    -- * Determining if a term is too small to require sharing
  , astIsSmall, astIsSmallS
    -- * Odds and ends
  , bindsToLet, bindsToLetS, bindsToHVectorLet
  ) where

import Prelude hiding (foldl')

import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.List (foldl')
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))

import HordeAd.Core.Ast
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances (matchingRank)
import HordeAd.Util.SizedList

-- * Shape calculation

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: forall n s r. (KnownNat n, GoodScalar r)
         => AstRanked s r n -> ShapeInt n
shapeAst = \case
  AstVar sh _var -> sh
  AstLet _ _ v -> shapeAst v
  AstShare _ v-> shapeAst v
  AstCond _b v _w -> shapeAst v
  AstMinIndex a -> initShape $ shapeAst a
  AstMaxIndex a -> initShape $ shapeAst a
  AstFloor a -> shapeAst a
  AstIota -> singletonShape (maxBound :: Int)  -- ought to be enough
  AstN1 _opCode t -> shapeAst t
  AstN2 _opCode t _ -> shapeAst t
  AstR1 _opCode t -> shapeAst t
  AstR2 _opCode t _ -> shapeAst t
  AstI2 _opCode t _ -> shapeAst t
  AstSumOfList args -> case args of
    [] -> error "shapeAst: AstSumOfList with no arguments"
    t : _ -> shapeAst t
  AstIndex v _is -> dropShape (shapeAst v)
  AstSum v -> tailShape $ shapeAst v
  AstScatter sh _ _ -> sh
  AstFromVector l -> case V.toList l of
    [] -> case sameNat (Proxy @n) (Proxy @1) of
      Just Refl -> singletonShape 0
      _ ->  error "shapeAst: AstFromVector with no arguments"
    t : _ -> V.length l :$: shapeAst t
  AstReplicate s v -> s :$: shapeAst v
  AstAppend x y -> case shapeAst x of
    ZSR -> error "shapeAst: impossible pattern needlessly required"
    xi :$: xsh -> case shapeAst y of
      ZSR -> error "shapeAst: impossible pattern needlessly required"
      yi :$: _ -> xi + yi :$: xsh
  AstSlice _i n v -> n :$: tailShape (shapeAst v)
  AstReverse v -> shapeAst v
  AstTranspose perm v -> backpermutePrefixShape perm (shapeAst v)
  AstReshape sh _v -> sh
  AstBuild1 k (_var, v) -> k :$: shapeAst v
  AstGather sh _v (_vars, _ix) -> sh
  AstCast t -> shapeAst t
  AstFromIntegral a -> shapeAst a
  AstConst a -> listToShape $ OR.shapeL a
  AstProject l p -> case shapeAstHVector l V.! p of
    DynamicRankedDummy @_ @sh _ _ -> listToShape $ shapeT @sh
    DynamicShapedDummy{} -> error "shapeAst: DynamicShapedDummy"
  AstLetHVectorIn _ _ v -> shapeAst v
  AstLetHFunIn _ _ v -> shapeAst v
  AstRFromS @sh _ -> listToShape $ shapeT @sh
  AstConstant a -> shapeAst a
  AstPrimalPart a -> shapeAst a
  AstDualPart a -> shapeAst a
  AstD u _ -> shapeAst u

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, GoodScalar r) => AstRanked s r (1 + n) -> Int
{-# INLINE lengthAst #-}
lengthAst v1 = case shapeAst v1 of
  ZSR -> error "lengthAst: impossible pattern needlessly required"
  k :$: _ -> k

shapeAstHVector :: AstHVector s -> VoidHVector
shapeAstHVector = \case
  AstMkHVector v -> V.map (voidFromDynamicF (shapeToList . shapeAst)) v
  AstHApply t _ll -> shapeAstHFun t
  AstLetHVectorInHVector _ _ v -> shapeAstHVector v
  AstLetHFunInHVector _ _ v -> shapeAstHVector v
  AstLetInHVector _ _ v -> shapeAstHVector v
  AstLetInHVectorS _ _ v -> shapeAstHVector v
  AstShareHVector _ v -> shapeAstHVector v
  AstBuildHVector1 k (_, v) -> replicate1VoidHVector k $ shapeAstHVector v
  AstMapAccumRDer k accShs bShs _eShs _f _df _rf _acc0 _es ->
    accShs V.++ replicate1VoidHVector k bShs
  AstMapAccumLDer k accShs bShs _eShs _f _df _rf _acc0 _es ->
    accShs V.++ replicate1VoidHVector k bShs

shapeAstHFun :: AstHFun -> VoidHVector
shapeAstHFun = \case
  AstLambda ~(_vvars, l) -> shapeAstHVector l
  AstVarHFun _shss shs _var -> shs

domainShapesAstHFun :: AstHFun -> [VoidHVector]
domainShapesAstHFun = \case
  AstLambda ~(vvars, _l) -> map voidFromVars vvars
  AstVarHFun shss _shs _var -> shss


-- * Variable occurrence detection

-- We assume no variable is shared between a binding and its nested binding
-- and nobody asks about occurrences of variables that are bound.
-- This keeps the occurrence checking code simple, because we never need
-- to compare variables to any variable in the bindings.
varInAst :: forall s r n. AstSpan s
         => AstVarId -> AstRanked s r n -> Bool
varInAst var = \case
  AstVar _ var2 -> fromEnum var == fromEnum var2
  AstLet _var2 u v -> varInAst var u || varInAst var v
  AstShare _ v -> varInAst var v
  AstCond b v w -> varInAstBool var b || varInAst var v || varInAst var w
  AstMinIndex a -> varInAst var a
  AstMaxIndex a -> varInAst var a
  AstFloor a -> varInAst var a
  AstIota -> False
  AstN1 _ t -> varInAst var t
  AstN2 _ t u -> varInAst var t || varInAst var u
  AstR1 _ t -> varInAst var t
  AstR2 _ t u -> varInAst var t || varInAst var u
  AstI2 _ t u -> varInAst var t || varInAst var u
  AstSumOfList l -> any (varInAst var) l
  AstIndex v ix -> varInAst var v || varInIndex var ix
  AstSum v -> varInAst var v
  AstScatter _ v (_vars, ix) -> varInIndex var ix || varInAst var v
  AstFromVector vl -> any (varInAst var) $ V.toList vl
  AstReplicate _ v -> varInAst var v
  AstAppend v u -> varInAst var v || varInAst var u
  AstSlice _ _ v -> varInAst var v
  AstReverse v -> varInAst var v
  AstTranspose _ v -> varInAst var v
  AstReshape _ v -> varInAst var v
  AstBuild1 _ (_var2, v) -> varInAst var v
  AstGather _ v (_vars, ix) -> varInIndex var ix || varInAst var v
  AstCast t -> varInAst var t
  AstFromIntegral t -> varInAst var t
  AstConst{} -> False
  AstProject l _p -> varInAstHVector var l  -- conservative
  AstLetHVectorIn _vars l v -> varInAstHVector var l || varInAst var v
  AstLetHFunIn _var2 f v -> varInAstHFun var f || varInAst var v
  AstRFromS v -> varInAstS var v
  AstConstant v -> varInAst var v
  AstPrimalPart a -> varInAst var a
  AstDualPart a -> varInAst var a
  AstD u u' -> varInAst var u || varInAst var u'

varInIndex :: AstVarId -> AstIndex n -> Bool
varInIndex var = any (varInAst var)

varInAstS :: forall s r sh. AstSpan s
          => AstVarId -> AstShaped s r sh -> Bool
varInAstS var = \case
  AstVarS var2 -> fromEnum var == fromEnum var2
  AstLetS _var2 u v -> varInAstS var u || varInAstS var v
  AstShareS _ v -> varInAstS var v
  AstCondS b v w -> varInAstBool var b || varInAstS var v || varInAstS var w
  AstMinIndexS a -> varInAstS var a
  AstMaxIndexS a -> varInAstS var a
  AstFloorS a -> varInAstS var a
  AstIotaS -> False
  AstN1S _ t -> varInAstS var t
  AstN2S _ t u -> varInAstS var t || varInAstS var u
  AstR1S _ t -> varInAstS var t
  AstR2S _ t u -> varInAstS var t || varInAstS var u
  AstI2S _ t u -> varInAstS var t || varInAstS var u
  AstSumOfListS l -> any (varInAstS var) l
  AstIndexS v ix -> varInAstS var v || varInIndexS var ix
  AstSumS v -> varInAstS var v
  AstScatterS v (_vars, ix) -> varInIndexS var ix || varInAstS var v
  AstFromVectorS vl -> any (varInAstS var) $ V.toList vl
  AstReplicateS v -> varInAstS var v
  AstAppendS v u -> varInAstS var v || varInAstS var u
  AstSliceS v -> varInAstS var v
  AstReverseS v -> varInAstS var v
  AstTransposeS v -> varInAstS var v
  AstReshapeS v -> varInAstS var v
  AstBuild1S (_var2, v) -> varInAstS var v
  AstGatherS v (_vars, ix) -> varInIndexS var ix || varInAstS var v
  AstCastS t -> varInAstS var t
  AstFromIntegralS a -> varInAstS var a
  AstConstS{} -> False
  AstProjectS l _p -> varInAstHVector var l  -- conservative
  AstLetHVectorInS _vars l v -> varInAstHVector var l || varInAstS var v
  AstLetHFunInS _var2 f v -> varInAstHFun var f || varInAstS var v
  AstSFromR v -> varInAst var v
  AstConstantS v -> varInAstS var v
  AstPrimalPartS a -> varInAstS var a
  AstDualPartS a -> varInAstS var a
  AstDS u u' -> varInAstS var u || varInAstS var u'

varInIndexS :: AstVarId -> AstIndexS sh -> Bool
varInIndexS var = any (varInAst var)

varInAstHVector :: AstSpan s
                => AstVarId -> AstHVector s -> Bool
varInAstHVector var = \case
  AstMkHVector l -> any (varInAstDynamic var) l
  AstHApply t ll -> varInAstHFun var t || any (any (varInAstDynamic var)) ll
  AstLetHVectorInHVector _vars2 u v ->
    varInAstHVector var u || varInAstHVector var v
  AstLetHFunInHVector _var2 f v ->
    varInAstHFun var f || varInAstHVector var v
  AstLetInHVector _var2 u v -> varInAst var u || varInAstHVector var v
  AstLetInHVectorS _var2 u v -> varInAstS var u || varInAstHVector var v
  AstShareHVector _ v -> varInAstHVector var v
  AstBuildHVector1 _ (_var2, v) -> varInAstHVector var v
  AstMapAccumRDer _k _accShs _bShs _eShs _f _df _rf acc0 es ->
    varInAstHVector var acc0 || varInAstHVector var es
  AstMapAccumLDer _k _accShs _bShs _eShs _f _df _rf acc0 es ->
    varInAstHVector var acc0 || varInAstHVector var es

varInAstDynamic :: AstSpan s
                => AstVarId -> AstDynamic s -> Bool
varInAstDynamic var = \case
  DynamicRanked t -> varInAst var t
  DynamicShaped t -> varInAstS var t
  DynamicRankedDummy{} -> False
  DynamicShapedDummy{} -> False

varInAstHFun :: AstVarId -> AstHFun -> Bool
varInAstHFun var = \case
  AstLambda{} -> False  -- we take advantage of the term being closed
  AstVarHFun _shss _shs var2 -> fromEnum var == fromEnum var2

varInAstBool :: AstVarId -> AstBool -> Bool
varInAstBool var = \case
  AstBoolNot b -> varInAstBool var b
  AstB2 _ arg1 arg2 -> varInAstBool var arg1 || varInAstBool var arg2
  AstBoolConst{} -> False
  AstRel _ arg1 arg2 -> varInAst var arg1 || varInAst var arg2
  AstRelS _ arg1 arg2 -> varInAstS var arg1 || varInAstS var arg2

varNameInAst :: AstSpan s2
             => AstVarName f r n -> AstRanked s2 r2 n2 -> Bool
varNameInAst (AstVarName varId) = varInAst varId

varNameInAstS :: AstSpan s2
              => AstVarName f r sh -> AstShaped s2 r2 sh2 -> Bool
varNameInAstS (AstVarName varId) = varInAstS varId

varNameInAstHVector :: AstSpan s
                    => AstVarName f r n -> AstHVector s -> Bool
varNameInAstHVector (AstVarName varId) = varInAstHVector varId

varInAstBindingsCase :: AstSpan s => AstVarId -> AstBindingsCase s -> Bool
varInAstBindingsCase var (AstBindingsSimple t) = varInAstDynamic var t
varInAstBindingsCase var (AstBindingsHVector _ t) = varInAstHVector var t


-- * Determining if a term is too small to require sharing

astIsSmall :: forall n s r. KnownNat n
           => Bool -> AstRanked s r n -> Bool
astIsSmall relaxed = \case
  AstVar{} -> True
  AstIota -> True
  AstReplicate _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via tricks, so prob. safe
  AstSlice _ _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTranspose _ v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstConst c -> OR.size c <= 1
  AstRFromS v -> astIsSmallS relaxed v
  AstConstant v -> astIsSmall relaxed v
  AstPrimalPart v -> astIsSmall relaxed v
  AstDualPart v -> astIsSmall relaxed v
  _ -> False

astIsSmallS :: forall sh s r. KnownShape sh
            => Bool -> AstShaped s r sh -> Bool
astIsSmallS relaxed = \case
  AstVarS{} -> True
  AstIotaS -> True
  AstReplicateS v ->
    relaxed && astIsSmallS relaxed v  -- materialized via tricks, so prob. safe
  AstSliceS v ->
    relaxed && astIsSmallS relaxed v  -- materialized via vector slice; cheap
  AstTransposeS v ->
    relaxed && astIsSmallS relaxed v  -- often cheap and often fuses
  AstConstS c -> OS.size c <= 1
  AstSFromR v -> astIsSmall relaxed v
  AstConstantS v -> astIsSmallS relaxed v
  AstPrimalPartS v -> astIsSmallS relaxed v
  AstDualPartS v -> astIsSmallS relaxed v
  _ -> False


-- * Odds and ends

bindsToLet :: forall n s s2 r. (AstSpan s, AstSpan s2, KnownNat n, GoodScalar r)
           => AstRanked s r n -> AstBindings s2 -> AstRanked s r n
{-# INLINE bindsToLet #-}  -- help list fusion
bindsToLet = foldl' bindToLet
 where
  bindToLet :: AstRanked s r n
            -> (AstVarId, AstBindingsCase s2)
            -> AstRanked s r n
  bindToLet !u (varId, AstBindingsSimple d) =
    let convertShaped :: (GoodScalar r2, KnownShape sh2)
                      => AstShaped s2 r2 sh2 -> AstRanked s r n
        convertShaped t =
          withShapeP (shapeToList $ shapeAst u) $ \proxy -> case proxy of
            Proxy @sh | Just Refl <- matchingRank @sh @n ->
              AstRFromS @sh $ AstLetS (AstVarName varId) t (AstSFromR u)
            _ -> error "bindToLet: wrong rank"
    in case d of
      DynamicRanked w -> AstLet (AstVarName varId) w u
      DynamicShaped w -> convertShaped w
      DynamicRankedDummy @r2 @sh2 _ _ ->
        withListSh (Proxy @sh2) $ \_ ->
          AstLet @_ @n @r2 @_ @s (AstVarName varId) (AstRFromS @sh2 @s @r2 0) u
      DynamicShapedDummy @r2 @sh2 _ _ -> convertShaped @r2 @sh2 0
  bindToLet u (_, AstBindingsHVector lids d) =
    AstLetHVectorIn lids d u

bindsToLetS :: forall sh s r. (AstSpan s, KnownShape sh)
            => AstShaped s r sh -> AstBindings s -> AstShaped s r sh
{-# INLINE bindsToLetS #-}  -- help list fusion
bindsToLetS = foldl' bindToLetS
 where
  bindToLetS :: AstShaped s r sh
             -> (AstVarId, AstBindingsCase s)
             -> AstShaped s r sh
  bindToLetS !u (varId, AstBindingsSimple d) = case d of
    DynamicRanked w ->
      withListSh (Proxy @sh) $ \_ ->
        AstSFromR $ AstLet (AstVarName varId) w (AstRFromS u)
    DynamicShaped w -> AstLetS (AstVarName varId) w u
    DynamicRankedDummy @r2 @sh2 _ _ ->
      withListSh (Proxy @sh2) $ \_ ->
        withListSh (Proxy @sh) $ \_ ->
          AstSFromR
          $ AstLet (AstVarName varId) (AstRFromS @sh2 @s @r2 0) (AstRFromS u)
    DynamicShapedDummy @r2 @sh2 _ _ ->
      AstLetS @sh2 @sh @r2 @_ @s (AstVarName varId) 0 u
  bindToLetS u (_, AstBindingsHVector lids d) =
    AstLetHVectorInS lids d u

bindsToHVectorLet
   :: forall s. AstSpan s
   => AstHVector s -> AstBindings s -> AstHVector s
{-# INLINE bindsToHVectorLet #-}   -- help list fusion
bindsToHVectorLet = foldl' bindToHVectorLet
 where
  bindToHVectorLet !u (varId, AstBindingsSimple d) = case d of
    DynamicRanked w -> AstLetInHVector (AstVarName varId) w u
    DynamicShaped w -> AstLetInHVectorS (AstVarName varId) w u
    DynamicRankedDummy @r2 @sh2 _ _ ->
      withListSh (Proxy @sh2) $ \_ ->
        AstLetInHVector (AstVarName varId) (AstRFromS @sh2 @s @r2 0) u
    DynamicShapedDummy @r2 @sh2 _ _ ->
      AstLetInHVectorS @sh2 @r2 @s (AstVarName varId) 0 u
  bindToHVectorLet u (_, AstBindingsHVector lids d) =
    AstLetHVectorInHVector lids d u
