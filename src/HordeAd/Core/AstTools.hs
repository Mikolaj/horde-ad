{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | An assortment of operations working on AST of the code to be differentiated
-- or resulting from the differentiation.
module HordeAd.Core.AstTools
  ( -- * Shape calculation
    shapeAstFull, shapeAst
  , lengthAst, shapeAstHVector, shapeAstHFun, domainShapesAstHFun
    -- * Variable occurrence detection
  , varInAst, varInAstBool, varInIndex
  , varInIndexS
  , varInAstDynamic
  , varNameInAst, varNameInAstHVector
  , varInAstBindingsCase
    -- * Determining if a term is too small to require sharing
  , astIsSmall
    -- * Odds and ends
  , bindsToLet, bindsToLetS, bindsToHVectorLet
  ) where

import Prelude hiding (foldl')

import Data.List (foldl')
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, sameNat, type (+))
import Unsafe.Coerce (unsafeCoerce)

import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape qualified as X
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.Ast
import HordeAd.Core.HVector
import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Util.SizedList

-- * Shape calculation

shapeAstFull :: forall s y. TensorKind y
             => AstTensor s y -> TensorKindFull y
shapeAstFull t = case t of
  AstTuple t1 t2 -> FTKProduct (shapeAstFull t1) (shapeAstFull t2)
  AstProject1 v -> case shapeAstFull v of
    FTKProduct ftk1 _ -> ftk1
  AstProject2 v -> case shapeAstFull v of
    FTKProduct _ ftk2 -> ftk2
  AstLetTupleIn _var1 _var2 _p v -> shapeAstFull v
  AstVar ftk _var -> ftk
  AstPrimalPart a -> shapeAstFull a
  AstDualPart a -> shapeAstFull a
  AstConstant a -> shapeAstFull a
  AstD u _ -> shapeAstFull u
  AstCond _b v _w -> shapeAstFull v
  AstReplicate snat v -> buildTensorKindFull snat (shapeAstFull v)
  AstBuild1 snat (_var, v) -> buildTensorKindFull snat (shapeAstFull v)

  AstLet _ _ v -> shapeAstFull v
  AstShare _ v-> shapeAstFull v
  AstMinIndex a -> FTKR $ initShape $ shapeAst a
  AstMaxIndex a -> FTKR $ initShape $ shapeAst a
  AstFloor a -> FTKR $ shapeAst a
  AstIota -> FTKR $ singletonShape (maxBound :: Int)  -- ought to be enough
  AstN1 _opCode v -> shapeAstFull v
  AstN2 _opCode v _ -> shapeAstFull v
  AstR1 _opCode v -> shapeAstFull v
  AstR2 _opCode v _ -> shapeAstFull v
  AstI2 _opCode v _ -> shapeAstFull v
  AstSumOfList args -> case args of
    [] -> error "shapeAstFull: AstSumOfList with no arguments"
    v : _ -> shapeAstFull v
  AstIndex v _is -> FTKR $ dropShape $ shapeAst v
  AstSum v -> FTKR $ tailShape $ shapeAst v
  AstScatter sh _ _ -> FTKR sh
  AstFromVector l -> case V.toList l of
    [] -> case stensorKind @y of
      STKR @_ @n _ _ -> case sameNat (Proxy @n) (Proxy @1) of
        Just Refl -> FTKR $ singletonShape 0
        Nothing -> error "shapeAstFull: AstFromVector with no arguments"
    v : _ -> FTKR $ V.length l :$: (shapeAst v)
  AstAppend x y -> case shapeAst x of
    ZSR -> error "shapeAstFull: impossible pattern needlessly required"
    xi :$: xsh -> case shapeAst y of
      ZSR -> error "shapeAstFull: impossible pattern needlessly required"
      yi :$: _ -> FTKR $ xi + yi :$: xsh
  AstSlice _i n v -> FTKR $ n :$: tailShape (shapeAst v)
  AstReverse v -> shapeAstFull v
  AstTranspose perm v ->
    FTKR $ Nested.Internal.Shape.shrPermutePrefix perm $ shapeAst v
  AstReshape sh _v -> FTKR sh
  AstGather sh _v (_vars, _ix) -> FTKR sh
  AstCast v -> FTKR $ shapeAst v
  AstFromIntegral a -> FTKR $ shapeAst a
  AstConst a -> FTKR $ Nested.rshape a
  AstProjectR l p -> case shapeAstHVector l V.! p of
    DynamicRankedDummy @_ @sh _ _ -> FTKR $ listToShape $ shapeT @sh
    DynamicShapedDummy{} -> error "shapeAstFull: DynamicShapedDummy"
  AstLetHVectorIn _ _ v -> shapeAstFull v
  AstLetHFunIn _ _ v -> shapeAstFull v
  AstRFromS @sh _ | Dict <- lemKnownNatRank (knownShS @sh) ->
    FTKR $ listToShape $ shapeT @sh

  AstLetS{} -> FTKS
  AstShareS{} -> FTKS
  AstMinIndexS{} -> FTKS
  AstMaxIndexS{} -> FTKS
  AstFloorS{} -> FTKS
  AstIotaS{} -> FTKS
  AstN1S{} -> FTKS
  AstN2S{} -> FTKS
  AstR1S{} -> FTKS
  AstR2S{} -> FTKS
  AstI2S{} -> FTKS
  AstSumOfListS{} -> FTKS
  AstIndexS{} -> FTKS
  AstSumS{} -> FTKS
  AstScatterS{} -> FTKS
  AstFromVectorS{} -> FTKS
  AstAppendS{} -> FTKS
  AstSliceS{} -> FTKS
  AstReverseS{} -> FTKS
  AstTransposeS @perm @sh2 perm _v ->
    withShapeP
      (permutePrefixList (Permutation.permToList' perm)
                         (shapeT @sh2)) $ \(Proxy @sh2Perm) ->
        gcastWith (unsafeCoerce Refl :: sh2Perm :~: Permutation.PermutePrefix perm sh2)
        FTKS
  AstReshapeS{} -> FTKS
  AstGatherS{} -> FTKS
  AstCastS{} -> FTKS
  AstFromIntegralS{} -> FTKS
  AstConstS{} -> FTKS
  AstProjectS{} -> FTKS
  AstLetHVectorInS{} -> FTKS
  AstLetHFunInS{} -> FTKS
  AstSFromR{} -> FTKS

  AstMkHVector v ->
    FTKUntyped
    $ V.map (voidFromDynamicF (shapeToList . shapeAst . unAstRanked)) v
  AstHApply v _ll -> shapeAstHFun v
  AstLetHVectorInHVector _ _ v -> shapeAstFull v
  AstLetHFunInHVector _ _ v -> shapeAstFull v
  AstLetInHVector _ _ v -> shapeAstFull v
  AstLetInHVectorS _ _ v -> shapeAstFull v
  AstShareHVector _ v -> shapeAstFull v
  AstBuildHVector1 k (_, v) ->
    FTKUntyped $ replicate1VoidHVector k $ shapeAstHVector v
  AstMapAccumRDer k accShs bShs _eShs _f _df _rf _acc0 _es ->
    FTKUntyped $ accShs V.++ replicate1VoidHVector k bShs
  AstMapAccumLDer k accShs bShs _eShs _f _df _rf _acc0 _es ->
    FTKUntyped $ accShs V.++ replicate1VoidHVector k bShs

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: forall n s r. (KnownNat n, GoodScalar r)
         => AstTensor s (TKR r n) -> IShR n
shapeAst t = case shapeAstFull t of
  FTKR sh -> sh

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, GoodScalar r) => AstTensor s (TKR r (1 + n)) -> Int
{-# INLINE lengthAst #-}
lengthAst v1 = case shapeAst v1 of
  ZSR -> error "lengthAst: impossible pattern needlessly required"
  k :$: _ -> k

shapeAstHVector :: AstTensor s TKUntyped -> VoidHVector
shapeAstHVector t = case shapeAstFull t of
  FTKUntyped shs -> shs

shapeAstHFun :: TensorKind y => AstHFun y -> TensorKindFull y
shapeAstHFun = \case
  AstLambda ~(_vvars, l) -> shapeAstFull l
  AstVarHFun _shss shs _var -> shs

domainShapesAstHFun :: AstHFun y -> [VoidHVector]
domainShapesAstHFun = \case
  AstLambda ~(vvars, _l) -> map voidFromVars vvars
  AstVarHFun shss _shs _var -> shss


-- * Variable occurrence detection

-- We assume no variable is shared between a binding and its nested binding
-- and nobody asks about occurrences of variables that are bound.
-- This keeps the occurrence checking code simple, because we never need
-- to compare variables to any variable in the bindings.
varInAst :: AstSpan s
         => AstVarId -> AstTensor s y -> Bool
varInAst var = \case
  AstTuple t1 t2 -> varInAst var t1 || varInAst var t2
  AstProject1 t -> varInAst var t
  AstProject2 t -> varInAst var t
  AstLetTupleIn _var1 _var2 p v -> varInAst var p || varInAst var v
  AstVar _ var2 -> var == varNameToAstVarId var2
  AstPrimalPart a -> varInAst var a
  AstDualPart a -> varInAst var a
  AstConstant v -> varInAst var v
  AstD u u' -> varInAst var u || varInAst var u'
  AstCond b v w -> varInAstBool var b || varInAst var v || varInAst var w
  AstReplicate _ v -> varInAst var v
  AstBuild1 _ (_var2, v) -> varInAst var v

  AstLet _var2 u v -> varInAst var u || varInAst var v
  AstShare _ v -> varInAst var v
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
  AstAppend v u -> varInAst var v || varInAst var u
  AstSlice _ _ v -> varInAst var v
  AstReverse v -> varInAst var v
  AstTranspose _ v -> varInAst var v
  AstReshape _ v -> varInAst var v
  AstGather _ v (_vars, ix) -> varInIndex var ix || varInAst var v
  AstCast t -> varInAst var t
  AstFromIntegral t -> varInAst var t
  AstConst{} -> False
  AstProjectR l _p -> varInAst var l  -- conservative
  AstLetHVectorIn _vars l v -> varInAst var l || varInAst var v
  AstLetHFunIn _var2 f v -> varInAstHFun var f || varInAst var v
  AstRFromS v -> varInAst var v

  AstLetS _var2 u v -> varInAst var u || varInAst var v
  AstShareS _ v -> varInAst var v
  AstMinIndexS a -> varInAst var a
  AstMaxIndexS a -> varInAst var a
  AstFloorS a -> varInAst var a
  AstIotaS -> False
  AstN1S _ t -> varInAst var t
  AstN2S _ t u -> varInAst var t || varInAst var u
  AstR1S _ t -> varInAst var t
  AstR2S _ t u -> varInAst var t || varInAst var u
  AstI2S _ t u -> varInAst var t || varInAst var u
  AstSumOfListS l -> any (varInAst var) l
  AstIndexS v ix -> varInAst var v || varInIndexS var ix
  AstSumS v -> varInAst var v
  AstScatterS v (_vars, ix) -> varInIndexS var ix || varInAst var v
  AstFromVectorS vl -> any (varInAst var) $ V.toList vl
  AstAppendS v u -> varInAst var v || varInAst var u
  AstSliceS v -> varInAst var v
  AstReverseS v -> varInAst var v
  AstTransposeS _perm v -> varInAst var v
  AstReshapeS v -> varInAst var v
  AstGatherS v (_vars, ix) -> varInIndexS var ix || varInAst var v
  AstCastS t -> varInAst var t
  AstFromIntegralS a -> varInAst var a
  AstConstS{} -> False
  AstProjectS l _p -> varInAst var l  -- conservative
  AstLetHVectorInS _vars l v -> varInAst var l || varInAst var v
  AstLetHFunInS _var2 f v -> varInAstHFun var f || varInAst var v
  AstSFromR v -> varInAst var v

  AstMkHVector l -> any (varInAstDynamic var) l
  AstHApply t ll -> varInAstHFun var t || any (any (varInAstDynamic var)) ll
  AstLetHVectorInHVector _vars2 u v ->
    varInAst var u || varInAst var v
  AstLetHFunInHVector _var2 f v ->
    varInAstHFun var f || varInAst var v
  AstLetInHVector _var2 u v -> varInAst var u || varInAst var v
  AstLetInHVectorS _var2 u v -> varInAst var u || varInAst var v
  AstShareHVector _ v -> varInAst var v
  AstBuildHVector1 _ (_var2, v) -> varInAst var v
  AstMapAccumRDer _k _accShs _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es
  AstMapAccumLDer _k _accShs _bShs _eShs _f _df _rf acc0 es ->
    varInAst var acc0 || varInAst var es

varInIndex :: AstVarId -> AstIndex n -> Bool
varInIndex var = any (varInAst var)

varInIndexS :: AstVarId -> AstIndexS sh -> Bool
varInIndexS var = any (varInAst var)

varInAstDynamic :: AstSpan s
                => AstVarId -> AstDynamic s -> Bool
varInAstDynamic var = \case
  DynamicRanked (AstRanked t) -> varInAst var t
  DynamicShaped (AstShaped t) -> varInAst var t
  DynamicRankedDummy{} -> False
  DynamicShapedDummy{} -> False

varInAstHFun :: AstVarId -> AstHFun y -> Bool
varInAstHFun var = \case
  AstLambda{} -> False  -- we take advantage of the term being closed
  AstVarHFun _shss _shs var2 -> fromEnum var == fromEnum var2

varInAstBool :: AstVarId -> AstBool -> Bool
varInAstBool var = \case
  AstBoolNot b -> varInAstBool var b
  AstB2 _ arg1 arg2 -> varInAstBool var arg1 || varInAstBool var arg2
  AstBoolConst{} -> False
  AstRel _ arg1 arg2 -> varInAst var arg1 || varInAst var arg2
  AstRelS _ arg1 arg2 -> varInAst var arg1 || varInAst var arg2

varNameInAst :: AstSpan s2
             => AstVarName f y -> AstTensor s2 y2 -> Bool
varNameInAst var = varInAst (varNameToAstVarId var)

varNameInAstHVector :: AstSpan s
                    => AstVarName f y -> AstTensor s TKUntyped -> Bool
varNameInAstHVector var = varInAst (varNameToAstVarId var)

varInAstBindingsCase :: AstSpan s => AstVarId -> AstBindingsCase s -> Bool
varInAstBindingsCase var (AstBindingsSimple t) = varInAstDynamic var t
varInAstBindingsCase var (AstBindingsHVector _ t) = varInAst var t


-- * Determining if a term is too small to require sharing

astIsSmall :: Bool -> AstTensor s y -> Bool
astIsSmall relaxed = \case
  AstTuple t1 t2 -> astIsSmall relaxed t1 && astIsSmall relaxed t2
  AstLetTupleIn{} -> False
  AstVar{} -> True
  AstPrimalPart v -> astIsSmall relaxed v
  AstDualPart v -> astIsSmall relaxed v
  AstConstant v -> astIsSmall relaxed v
  AstReplicate _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via tricks, so prob. safe

  AstIota -> True
  AstSlice _ _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTranspose _ v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstConst c -> Nested.rsize c <= 1
  AstRFromS v -> astIsSmall relaxed v

  AstIotaS -> True
  AstSliceS v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTransposeS _perm v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstConstS c ->
    Nested.ssize c <= 1
  AstSFromR v -> astIsSmall relaxed v

  _ -> False


-- * Odds and ends

astReplicate0N :: forall n s r. (AstSpan s, GoodScalar r)
               => IShR n -> r -> AstTensor s (TKR r n)
astReplicate0N sh =
  let go :: IShR n' -> AstTensor s (TKR r 0) -> AstTensor s (TKR r n')
      go ZSR v = v
      go (k :$: sh') v | Dict <- knownShR sh' = withSNat k $ \snat ->
        AstReplicate snat $ go sh' v
  in go sh . fromPrimal . AstConst . Nested.rscalar

bindsToLet :: forall n s s2 r. (AstSpan s, AstSpan s2, KnownNat n, GoodScalar r)
           => AstTensor s (TKR r n) -> AstBindings s2 -> AstTensor s (TKR r n)
{-# INLINE bindsToLet #-}  -- help list fusion
bindsToLet = foldl' bindToLet
 where
  bindToLet :: AstTensor s (TKR r n)
            -> (AstVarId, AstBindingsCase s2)
            -> AstTensor s (TKR r n)
  bindToLet !u (varId, AstBindingsSimple d) =
    let convertShaped :: (GoodScalar r2, KnownShS sh2)
                      => AstShaped s2 r2 sh2 -> AstTensor s (TKR r n)
        convertShaped (AstShaped t) =
          withShapeP (shapeToList $ shapeAst u) $ \proxy -> case proxy of
            Proxy @sh | Just Refl <- matchingRank @sh @n ->
              AstRFromS @sh $ AstLetS (mkAstVarName varId) t (AstSFromR u)
            _ -> error "bindToLet: wrong rank"
    in case d of
      DynamicRanked (AstRanked w) -> AstLet (mkAstVarName varId) w u
      DynamicShaped w -> convertShaped w
      DynamicRankedDummy @r2 @sh2 _ _ ->
          withListSh (Proxy @sh2) $ \sh2 ->
            AstLet @n @_ @(TKR r2 (X.Rank sh2)) @s (mkAstVarName varId) (astReplicate0N sh2 0) u
      DynamicShapedDummy @r2 @sh2 _ _ ->
           withListSh (Proxy @sh2) $ \sh2 ->
            AstLet @n @_ @(TKR r2 (X.Rank sh2)) @s (mkAstVarName varId) (astReplicate0N sh2 0) u
  bindToLet u (_, AstBindingsHVector lids d) = AstLetHVectorIn lids d u

bindsToLetS :: forall sh s r. (AstSpan s, GoodScalar r, KnownShS sh)
            => AstTensor s (TKS r sh) -> AstBindings s
            -> AstTensor s (TKS r sh)
{-# INLINE bindsToLetS #-}  -- help list fusion
bindsToLetS = foldl' bindToLetS
 where
  bindToLetS :: AstTensor s (TKS r sh)
             -> (AstVarId, AstBindingsCase s)
             -> AstTensor s (TKS r sh)
  bindToLetS !u (varId, AstBindingsSimple d) = case d of
    DynamicRanked (AstRanked w) ->
      withListSh (Proxy @sh) $ \_ ->
        AstSFromR $ AstLet (mkAstVarName varId) w (AstRFromS u)
    DynamicShaped (AstShaped w) -> AstLetS (mkAstVarName varId) w u
    DynamicRankedDummy @r2 @sh2 _ _ ->
        withListSh (Proxy @sh2) $ \sh2 ->
          withListSh (Proxy @sh) $ \_ ->
            AstSFromR
            $ AstLet (mkAstVarName varId) (astReplicate0N @_ @s @r2 sh2 0) (AstRFromS u)
    DynamicShapedDummy @r2 @sh2 _ _ ->
        withListSh (Proxy @sh2) $ \sh2 ->
          withListSh (Proxy @sh) $ \_ ->
            AstSFromR
            $ AstLet (mkAstVarName varId) (astReplicate0N @_ @s @r2 sh2 0) (AstRFromS u)
  bindToLetS u (_, AstBindingsHVector lids d) = AstLetHVectorInS lids d u

bindsToHVectorLet
   :: forall s. AstSpan s
   => AstTensor s TKUntyped -> AstBindings s -> AstTensor s TKUntyped
{-# INLINE bindsToHVectorLet #-}   -- help list fusion
bindsToHVectorLet = foldl' bindToHVectorLet
 where
  bindToHVectorLet !u (varId, AstBindingsSimple d) = case d of
    DynamicRanked (AstRanked w) -> AstLetInHVector (mkAstVarName varId) w u
    DynamicShaped (AstShaped w) -> AstLetInHVectorS (mkAstVarName varId) w u
    DynamicRankedDummy @r2 @sh2 _ _ ->
        withListSh (Proxy @sh2) $ \sh2 ->
          AstLetInHVector (mkAstVarName varId) (astReplicate0N @_ @s @r2 sh2 0) u
    DynamicShapedDummy @r2 @sh2 _ _ ->
        withListSh (Proxy @sh2) $ \sh2 ->
          AstLetInHVector (mkAstVarName varId) (astReplicate0N @_ @s @r2 sh2 0) u
  bindToHVectorLet u (_, AstBindingsHVector lids d) =
    AstLetHVectorInHVector lids d u
