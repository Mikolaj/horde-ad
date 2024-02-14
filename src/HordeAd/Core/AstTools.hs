{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | An assortment of operations working on AST of the code to be differentiated
-- or resulting from the differentiation.
module HordeAd.Core.AstTools
  ( -- * Shape calculation
    shapeAst, lengthAst, shapeAstHVector
    -- * Variable occurrence detection
  , varInAst, varInADShare, varInAstBool, varInIndex
  , varInAstS, varInIndexS
  , varNameInAst, varNameInADShare, varNameInAstS, varNameInAstHVector
    -- * Determining if a term is too small to require sharing
  , astIsSmall, astIsSmallS
    -- * Odds and ends
  , bindsToLet, bindsToLetS, bindsToHVectorLet
  ) where

import Prelude hiding (foldl')

import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import           Data.List (foldl')
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances (matchingRank)
import HordeAd.Util.SizedIndex

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
  AstLetADShare _ v-> shapeAst v
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
  AstFromList l -> case l of
    [] -> case sameNat (Proxy @n) (Proxy @1) of
      Just Refl -> singletonShape 0  -- the only case where we can guess sh
      _ -> error "shapeAst: AstFromList with no arguments"
    t : _ -> length l :$ shapeAst t
  AstFromVector l -> case V.toList l of
    [] -> case sameNat (Proxy @n) (Proxy @1) of
      Just Refl -> singletonShape 0
      _ ->  error "shapeAst: AstFromVector with no arguments"
    t : _ -> V.length l :$ shapeAst t
  AstReplicate s v -> s :$ shapeAst v
  AstAppend x y -> case shapeAst x of
    ZS -> error "shapeAst: impossible pattern needlessly required"
    xi :$ xsh -> case shapeAst y of
      ZS -> error "shapeAst: impossible pattern needlessly required"
      yi :$ _ -> xi + yi :$ xsh
  AstSlice _i n v -> n :$ tailShape (shapeAst v)
  AstReverse v -> shapeAst v
  AstTranspose perm v -> backpermutePrefixShape perm (shapeAst v)
  AstReshape sh _v -> sh
  AstBuild1 k (_var, v) -> k :$ shapeAst v
  AstGather sh _v (_vars, _ix) -> sh
  AstCast t -> shapeAst t
  AstFromIntegral a -> shapeAst a
  AstConst a -> listShapeToShape $ OR.shapeL a
  AstLetHVectorIn _ _ v -> shapeAst v
  AstRFromS @sh _ -> listShapeToShape $ Sh.shapeT @sh
  AstConstant a -> shapeAst a
  AstPrimalPart a -> shapeAst a
  AstDualPart a -> shapeAst a
  AstD u _ -> shapeAst u
  AstFwd (_var, v) _l _ds -> shapeAst v
  AstFold _f x0 _as -> shapeAst x0
  AstFoldDer _f _df _rf x0 _as -> shapeAst x0
  AstFoldZip _f x0 _as -> shapeAst x0
  AstFoldZipDer _f _df _rf x0 _as -> shapeAst x0
  AstScan _f x0 as -> lengthAst as + 1 :$ shapeAst x0
  AstScanDer _f _df _rf x0 as -> lengthAst as + 1 :$ shapeAst x0
  AstScanZip _f x0 as ->
    let len = case V.uncons as of
          Nothing -> 0
          Just (a, _) -> case shapeDynamicAst a of
            [] -> error "shapeAst: no scan arguments"
            k : _ -> k
    in len + 1 :$ shapeAst x0
  AstScanZipDer _f _df _rf x0 as ->
    let len = case V.uncons as of
          Nothing -> 0
          Just (a, _) -> case shapeDynamicAst a of
            [] -> error "shapeAst: no scan arguments"
            k : _ -> k
    in len + 1 :$ shapeAst x0

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, GoodScalar r) => AstRanked s r (1 + n) -> Int
lengthAst v1 = case shapeAst v1 of
  ZS -> error "lengthAst: impossible pattern needlessly required"
  k :$ _ -> k

shapeDynamicAst :: DynamicTensor (AstRanked s) -> [Int]
shapeDynamicAst = shapeDynamicF (shapeToList . shapeAst)

shapeAstHVector :: AstHVector s -> VoidHVector
shapeAstHVector = \case
  AstHVector v -> V.map (voidFromDynamicF (shapeToList . shapeAst)) v
  AstLetHVectorInHVector _ _ v -> shapeAstHVector v
  AstLetInHVector _ _ v -> shapeAstHVector v
  AstLetInHVectorS _ _ v -> shapeAstHVector v
  AstBuildHVector1 k (_, v) -> withSNat k $ \ snatK ->
    replicate1VoidHVector snatK $ shapeAstHVector v
  AstRev (vars, _) _ -> voidFromVars vars
  AstRevDt (vars, _) _ _ -> voidFromVars vars
  AstRevS (vars, _) _ -> voidFromVars vars
  AstRevDtS (vars, _) _ _ -> voidFromVars vars
  AstMapAccumR k accShs bShs _eShs _f _acc0 _es ->
    accShs V.++ replicate1VoidHVector k bShs
  AstMapAccumRDer k accShs bShs _eShs _f _df _rf _acc0 _es ->
    accShs V.++ replicate1VoidHVector k bShs

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
  AstLetADShare l v -> varInADShare var l || varInAst var v
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
  AstFromList l -> any (varInAst var) l  -- down from rank 1 to 0
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
  AstLetHVectorIn _vars l v -> varInAstHVector var l || varInAst var v
  AstRFromS v -> varInAstS var v
  AstConstant v -> varInAst var v
  AstPrimalPart a -> varInAst var a
  AstDualPart a -> varInAst var a
  AstD u u' -> varInAst var u || varInAst var u'
  AstFwd _f l ds ->  -- _f has no non-bound variables
    let f = varInAstDynamic var
    in any f l || any f ds
  AstFold _f x0 as -> varInAst var x0 || varInAst var as
  AstFoldDer _f _df _rf x0 as -> varInAst var x0 || varInAst var as
  AstFoldZip _f x0 as -> varInAst var x0 || any (varInAstDynamic var) as
  AstFoldZipDer _f _df _rf x0 as ->
    varInAst var x0 || any (varInAstDynamic var) as
  AstScan _f x0 as -> varInAst var x0 || varInAst var as
  AstScanDer _f _df _rf x0 as -> varInAst var x0 || varInAst var as
  AstScanZip _f x0 as -> varInAst var x0 || any (varInAstDynamic var) as
  AstScanZipDer _f _df _rf x0 as ->
    varInAst var x0 || any (varInAstDynamic var) as

varInIndex :: AstVarId -> AstIndex n -> Bool
varInIndex var = any (varInAst var)

varInAstS :: forall s r sh. AstSpan s
          => AstVarId -> AstShaped s r sh -> Bool
varInAstS var = \case
  AstVarS var2 -> fromEnum var == fromEnum var2
  AstLetS _var2 u v -> varInAstS var u || varInAstS var v
  AstLetADShareS l v -> varInADShare var l || varInAstS var v
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
  AstFromListS l -> any (varInAstS var) l  -- down from rank 1 to 0
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
  AstLetHVectorInS _vars l v -> varInAstHVector var l || varInAstS var v
  AstSFromR v -> varInAst var v
  AstConstantS v -> varInAstS var v
  AstPrimalPartS a -> varInAstS var a
  AstDualPartS a -> varInAstS var a
  AstDS u u' -> varInAstS var u || varInAstS var u'
  AstFwdS _f l ds ->  -- _f has no non-bound variables
    let f = varInAstDynamic var
    in any f l || any f ds
  AstFoldS _f x0 as -> varInAstS var x0 || varInAstS var as
  AstFoldDerS _f _df _rf x0 as -> varInAstS var x0 || varInAstS var as
  AstFoldZipS _f x0 as -> varInAstS var x0 || any (varInAstDynamic var) as
  AstFoldZipDerS _f _df _rf x0 as ->
    varInAstS var x0 || any (varInAstDynamic var) as
  AstScanS _f x0 as -> varInAstS var x0 || varInAstS var as
  AstScanDerS _f _df _rf x0 as -> varInAstS var x0 || varInAstS var as
  AstScanZipS _f x0 as -> varInAstS var x0 || any (varInAstDynamic var) as
  AstScanZipDerS _f _df _rf x0 as ->
    varInAstS var x0 || any (varInAstDynamic var) as

varInIndexS :: AstVarId -> AstIndexS sh -> Bool
varInIndexS var = any (varInAst var)

varInADShare :: AstVarId -> ADShare -> Bool
varInADShare = varInADShareF varInAstDynamic varInAstHVector

varInAstHVector :: AstSpan s
                => AstVarId -> AstHVector s -> Bool
varInAstHVector var = \case
  AstHVector l -> any (varInAstDynamic var) l
  AstLetHVectorInHVector _vars2 u v ->
    varInAstHVector var u || varInAstHVector var v
  AstLetInHVector _var2 u v -> varInAst var u || varInAstHVector var v
  AstLetInHVectorS _var2 u v -> varInAstS var u || varInAstHVector var v
  AstBuildHVector1 _ (_var2, v) -> varInAstHVector var v
  AstRev _f l ->  -- _f has no non-bound variables
    any (varInAstDynamic var) l
  AstRevDt _f l dt ->  -- _f has no non-bound variables
    let f = varInAstDynamic var
    in any f l || varInAst var dt
  AstRevS _f l ->  -- _f has no non-bound variables
    any (varInAstDynamic var) l
  AstRevDtS _f l dt ->  -- _f has no non-bound variables
    let f = varInAstDynamic var
    in any f l || varInAstS var dt
  AstMapAccumR _k _accShs _bShs _eShs _f acc0 es ->
    any (varInAstDynamic var) acc0 || any (varInAstDynamic var) es
  AstMapAccumRDer _k _accShs _bShs _eShs _f _df _rf acc0 es ->
    any (varInAstDynamic var) acc0 || any (varInAstDynamic var) es

varInAstDynamic :: AstSpan s
                => AstVarId -> AstDynamic s -> Bool
varInAstDynamic var = \case
  DynamicRanked t -> varInAst var t
  DynamicShaped t -> varInAstS var t
  DynamicRankedDummy{} -> False
  DynamicShapedDummy{} -> False

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

varNameInADShare :: AstVarName f r n -> ADShare -> Bool
varNameInADShare (AstVarName varId) = varInADShare varId

varNameInAstS :: AstSpan s2
              => AstVarName f r sh -> AstShaped s2 r2 sh2 -> Bool
varNameInAstS (AstVarName varId) = varInAstS varId

varNameInAstHVector :: AstSpan s
                    => AstVarName f r n -> AstHVector s -> Bool
varNameInAstHVector (AstVarName varId) = varInAstHVector varId


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
  AstConst{} -> valueOf @n == (0 :: Int)
  AstRFromS v -> astIsSmallS relaxed v
  AstConstant v -> astIsSmall relaxed v
  AstPrimalPart v -> astIsSmall relaxed v
  AstDualPart v -> astIsSmall relaxed v
  _ -> False

astIsSmallS :: forall sh s r. Sh.Shape sh
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
  AstConstS{} -> null (Sh.shapeT @sh)
  AstSFromR v -> astIsSmall relaxed v
  AstConstantS v -> astIsSmallS relaxed v
  AstPrimalPartS v -> astIsSmallS relaxed v
  AstDualPartS v -> astIsSmallS relaxed v
  _ -> False


-- * Odds and ends

bindsToLet :: forall n s r. (AstSpan s, KnownNat n, GoodScalar r)
           => AstRanked s r n -> AstBindingsD (AstRanked s) -> AstRanked s r n
{-# INLINE bindsToLet #-}  -- help list fusion
bindsToLet = foldl' bindToLet
 where
  bindToLet :: AstRanked s r n
            -> (AstVarId, AstBindingsCase (AstRanked s))
            -> AstRanked s r n
  bindToLet !u (varId, AstBindingsSimple d) =
    let convertShaped :: (GoodScalar r2, Sh.Shape sh2)
                      => AstShaped s r2 sh2 -> AstRanked s r n
        convertShaped t =
          Sh.withShapeP (shapeToList $ shapeAst u) $ \proxy -> case proxy of
            Proxy @sh | Just Refl <- matchingRank @sh @n ->
              AstRFromS @sh $ AstLetS (AstVarName varId) t (AstSFromR u)
            _ -> error "bindToLet: wrong rank"
    in case d of
      DynamicRanked w -> AstLet (AstVarName varId) w u
      DynamicShaped w -> convertShaped w
      DynamicRankedDummy @r2 @sh2 _ _ ->
        withListShape (Sh.shapeT @sh2) $ \(_ :: ShapeInt n3) ->
          gcastWith (unsafeCoerce Refl :: n3 :~: Sh.Rank sh2) $
          AstLet @n3 @n @r2 @_ @s (AstVarName varId) (AstRFromS @sh2 @s @r2 0) u
      DynamicShapedDummy @r2 @sh2 _ _ -> convertShaped @r2 @sh2 0
  bindToLet u (_, AstBindingsHVector lids d) =
    AstLetHVectorIn lids d u

bindsToLetS :: forall sh s r. (AstSpan s, Sh.Shape sh)
            => AstShaped s r sh -> AstBindingsD (AstRanked s) -> AstShaped s r sh
{-# INLINE bindsToLetS #-}  -- help list fusion
bindsToLetS = foldl' bindToLetS
 where
  bindToLetS :: AstShaped s r sh
             -> (AstVarId, AstBindingsCase (AstRanked s))
             -> AstShaped s r sh
  bindToLetS !u (varId, AstBindingsSimple d) = case d of
    DynamicRanked w ->
      withListShape (Sh.shapeT @sh) $ \sh -> case sh of
        (_ :: ShapeInt n) | Just Refl <- matchingRank @sh @n ->
          AstSFromR $ AstLet (AstVarName varId) w (AstRFromS u)
        _ -> error "bindToLetS: wrong rank"
    DynamicShaped w -> AstLetS (AstVarName varId) w u
    DynamicRankedDummy @r2 @sh2 _ _ ->
      withListShape (Sh.shapeT @sh2) $ \(_ :: ShapeInt n3) ->
        gcastWith (unsafeCoerce Refl :: n3 :~: Sh.Rank sh2) $
        withListShape (Sh.shapeT @sh) $ \(_ :: ShapeInt m) ->
          gcastWith (unsafeCoerce Refl :: m :~: Sh.Rank sh) $
          AstSFromR $ AstLet @n3 @m @r2 @_ @s
                      (AstVarName varId) (AstRFromS @sh2 @s @r2 0) (AstRFromS u)
    DynamicShapedDummy @r2 @sh2 _ _ ->
      AstLetS @sh2 @sh @r2 @_ @s (AstVarName varId) 0 u
  bindToLetS u (_, AstBindingsHVector lids d) =
    AstLetHVectorInS lids d u

bindsToHVectorLet
   :: forall s. AstSpan s
   => AstHVector s -> AstBindingsD (AstRanked s) -> AstHVector s
{-# INLINE bindsToHVectorLet #-}   -- help list fusion
bindsToHVectorLet = foldl' bindToHVectorLet
 where
  bindToHVectorLet !u (varId, AstBindingsSimple d) = case d of
    DynamicRanked w -> AstLetInHVector (AstVarName varId) w u
    DynamicShaped w -> AstLetInHVectorS (AstVarName varId) w u
    DynamicRankedDummy @r2 @sh2 _ _ ->
      withListShape (Sh.shapeT @sh2) $ \(_ :: ShapeInt n) ->
        gcastWith (unsafeCoerce Refl :: n :~: Sh.Rank sh2) $
        AstLetInHVector @n @r2 @s (AstVarName varId) (AstRFromS @sh2 @s @r2 0) u
    DynamicShapedDummy @r2 @sh2 _ _ ->
      AstLetInHVectorS @sh2 @r2 @s (AstVarName varId) 0 u
  bindToHVectorLet u (_, AstBindingsHVector lids d) =
    AstLetHVectorInHVector lids d u
