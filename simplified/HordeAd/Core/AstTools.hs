{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | An assortment of operations on AST of the code to be differentiated
-- or resulting from the differentiation.
module HordeAd.Core.AstTools
  ( shapeAst, lengthAst
  , intVarInAst, intVarInAstBool, intVarInIndex
  , intVarInAstS, intVarInIndexS
  , SubstitutionPayload(..)
  , substitute1Ast, substitute1AstDomains
  , substitute1AstBool, substitute1AstS
  , astIsSmall, astIsSmallS
  , unwrapAstDomains, bindsToLet, bindsToLetS
  , bindsToDomainsLet
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import           Data.List (foldl')
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
import HordeAd.Core.SizedIndex
import HordeAd.Core.Types
import HordeAd.Internal.OrthotopeOrphanInstances (sameShape)

-- * Shape calculation

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: forall n s r. (KnownNat n, GoodScalar r)
         => AstRanked s r n -> ShapeInt n
shapeAst v1 = case v1 of
  AstVar sh _var -> sh
  AstLet _ _ v -> shapeAst v
  AstLetADShare _ v-> shapeAst v
  AstNm _opCode args -> case args of
    [] -> error "shapeAst: AstNm with no arguments"
    t : _ -> shapeAst t
  AstOp _opCode args -> case args of
    [] -> error "shapeAst: AstOp with no arguments"
    t : _ -> shapeAst t
  AstOpIntegral _opCode args -> case args of
    [] -> error "shapeAst: AstOpIntegral with no arguments"
    t : _ -> shapeAst t
  AstSumOfList args -> case args of
    [] -> error "shapeAst: AstSumOfList with no arguments"
    t : _ -> shapeAst t
  AstIota -> singletonShape (maxBound :: Int)  -- ought to be enough
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
  AstSToR @sh _ -> listShapeToShape $ OS.shapeT @sh
  AstConst a -> listShapeToShape $ OR.shapeL a
  AstConstant a -> shapeAst a
  AstPrimalPart a -> shapeAst a
  AstDualPart a -> shapeAst a
  AstD u _ -> shapeAst u
  AstLetDomains _ _ v -> shapeAst v
  AstCond _b v _w -> shapeAst v
  AstFloor a -> shapeAst a
  AstMinIndex a -> initShape $ shapeAst a
  AstMaxIndex a -> initShape $ shapeAst a

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, GoodScalar r) => AstRanked s r (1 + n) -> Int
lengthAst v1 = case shapeAst v1 of
  ZS -> error "lengthAst: impossible pattern needlessly required"
  k :$ _ -> k


-- * Variable occurence detection

-- We assume no variable is shared between a binding and its nested binding
-- and nobody asks about occurences of variables that are bound.
-- This keeps the occurence checking code simple, because we never need
-- to compare variables to any variable in the bindings.
-- This code works, in fact, for any variables, not only int variables.
intVarInAst :: forall s r n. AstSpan s => AstVarId -> AstRanked s r n -> Bool
intVarInAst var = \case
  AstVar _ var2 -> var == var2
  AstLet _var2 u v -> intVarInAst var u || intVarInAst var v
  AstLetADShare l v | Just Refl <- sameAstSpan @s @AstPrimal ->
    intVarInADShare intIdInAstDynamic (astVarIdToAstId var) l
    || intVarInAst var v
  AstLetADShare{} -> False
  AstNm _ l -> any (intVarInAst var) l
  AstOp _ l -> any (intVarInAst var) l
  AstOpIntegral _ l -> any (intVarInAst var) l
  AstSumOfList l -> any (intVarInAst var) l
  AstIota -> False
  AstIndex v ix -> intVarInAst var v || intVarInIndex var ix
  AstSum v -> intVarInAst var v
  AstScatter _ v (_vars, ix) -> intVarInIndex var ix || intVarInAst var v
  AstFromList l -> any (intVarInAst var) l  -- down from rank 1 to 0
  AstFromVector vl -> any (intVarInAst var) $ V.toList vl
  AstReplicate _ v -> intVarInAst var v
  AstAppend v u -> intVarInAst var v || intVarInAst var u
  AstSlice _ _ v -> intVarInAst var v
  AstReverse v -> intVarInAst var v
  AstTranspose _ v -> intVarInAst var v
  AstReshape _ v -> intVarInAst var v
  AstBuild1 _ (_var2, v) -> intVarInAst var v
  AstGather _ v (_vars, ix) -> intVarInIndex var ix || intVarInAst var v
  AstCast t -> intVarInAst var t
  AstFromIntegral t -> intVarInAst var t
  AstSToR v -> intVarInAstS var v
  AstConst{} -> False
  AstConstant v -> intVarInAst var v
  AstPrimalPart a -> intVarInAst var a
  AstDualPart a -> intVarInAst var a
  AstD u u' -> intVarInAst var u || intVarInAst var u'
  AstLetDomains _vars l v -> intVarInAstDomains var l || intVarInAst var v
  AstCond b v w ->
    intVarInAstBool var b || intVarInAst var v || intVarInAst var w
  AstFloor a -> intVarInAst var a
  AstMinIndex a -> intVarInAst var a
  AstMaxIndex a -> intVarInAst var a

intVarInAstDomains :: AstSpan s => AstVarId -> AstDomains s -> Bool
intVarInAstDomains var = \case
  AstDomains l -> let f (DynamicExists d) = intVarInAstDynamic var d
                  in any f l
  AstDomainsLet _var2 u v -> intVarInAst var u || intVarInAstDomains var v
  AstDomainsLetS _var2 u v -> intVarInAstS var u || intVarInAstDomains var v

intVarInAstDynamic :: AstSpan s => AstVarId -> AstDynamic s r -> Bool
intVarInAstDynamic var = \case
  AstRToD t -> intVarInAst var t
  AstSToD t -> intVarInAstS var t

intIdInAstDynamic :: AstSpan s => AstId -> AstDynamic s r -> Bool
intIdInAstDynamic var = \case
  AstRToD t -> intVarInAst (astIdToAstVarId var) t
  AstSToD t -> intVarInAstS (astIdToAstVarId var) t

intVarInAstBool :: AstVarId -> AstBool -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> any (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> any (intVarInAst var) l
  AstRelS _ l -> any (intVarInAstS var) l

intVarInIndex :: AstVarId -> AstIndex n -> Bool
intVarInIndex var = any (intVarInAst var)

intVarInAstS :: forall s r sh. AstSpan s => AstVarId -> AstShaped s r sh -> Bool
intVarInAstS var = \case
  AstVarS var2 -> var == var2
  AstLetS _var2 u v -> intVarInAstS var u || intVarInAstS var v
  AstLetADShareS l v | Just Refl <- sameAstSpan @s @AstPrimal ->
    intVarInADShare intIdInAstDynamic (astVarIdToAstId var) l
    || intVarInAstS var v
  AstLetADShareS{} -> False
  AstNmS _ l -> any (intVarInAstS var) l
  AstOpS _ l -> any (intVarInAstS var) l
  AstOpIntegralS _ l -> any (intVarInAstS var) l
  AstSumOfListS l -> any (intVarInAstS var) l
  AstIotaS -> False
  AstIndexS v ix -> intVarInAstS var v || intVarInIndexS var ix
  AstSumS v -> intVarInAstS var v
  AstScatterS v (_vars, ix) -> intVarInIndexS var ix || intVarInAstS var v
  AstFromListS l -> any (intVarInAstS var) l  -- down from rank 1 to 0
  AstFromVectorS vl -> any (intVarInAstS var) $ V.toList vl
  AstReplicateS v -> intVarInAstS var v
  AstAppendS v u -> intVarInAstS var v || intVarInAstS var u
  AstSliceS v -> intVarInAstS var v
  AstReverseS v -> intVarInAstS var v
  AstTransposeS v -> intVarInAstS var v
  AstReshapeS v -> intVarInAstS var v
  AstBuild1S (_var2, v) -> intVarInAstS var v
  AstGatherS v (_vars, ix) -> intVarInIndexS var ix || intVarInAstS var v
  AstCastS t -> intVarInAstS var t
  AstFromIntegralS a -> intVarInAstS var a
  AstRToS v -> intVarInAst var v
  AstConstS{} -> False
  AstConstantS v -> intVarInAstS var v
  AstPrimalPartS a -> intVarInAstS var a
  AstDualPartS a -> intVarInAstS var a
  AstDS u u' -> intVarInAstS var u || intVarInAstS var u'
  AstLetDomainsS _vars l v -> intVarInAstDomains var l || intVarInAstS var v
  AstCondS b v w ->
    intVarInAstBool var b || intVarInAstS var v || intVarInAstS var w
  AstFloorS a -> intVarInAstS var a
  AstMinIndexS a -> intVarInAstS var a
  AstMaxIndexS a -> intVarInAstS var a

intVarInIndexS :: AstVarId -> AstIndexS sh -> Bool
intVarInIndexS var = any (intVarInAst var)


-- * Substitution

data SubstitutionPayload s r =
    forall n. KnownNat n
    => SubstitutionPayloadRanked (AstRanked s r n)
  | forall sh. OS.Shape sh
    => SubstitutionPayloadShaped (AstShaped s r sh)

-- We assume no variable is shared between a binding and its nested binding
-- and nobody substitutes into variables that are bound.
-- This keeps the substitution code simple, because we never need to compare
-- variables to any variable in the bindings.
substitute1Ast :: forall n s s2 r r2.
                  (GoodScalar r, GoodScalar r2, KnownNat n, AstSpan s, AstSpan s2)
               => SubstitutionPayload s2 r2 -> AstVarId -> AstRanked s r n
               -> AstRanked s r n
substitute1Ast i var v1 = case v1 of
  AstVar sh var2 ->
    if var == var2
    then case i of
      SubstitutionPayloadRanked @_ @_ @m t -> case sameAstSpan @s @s2 of
        Just Refl -> case sameNat (Proxy @m) (Proxy @n) of
          Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
            Just Refl -> assert (shapeAst t == sh) t
            _ -> error "substitute1Ast: scalar"
          _ -> error "substitute1Ast: rank"
        _ -> error "substitute1Ast: span"
      _ -> error "substitute1Ast: type"
    else v1
  AstLet var2 u v ->
    AstLet var2 (substitute1Ast i var u) (substitute1Ast i var v)
  AstLetADShare{} -> error "substitute1Ast: AstLetADShare"
  AstNm opCode args -> AstNm opCode $ map (substitute1Ast i var) args
  AstOp opCode args -> AstOp opCode $ map (substitute1Ast i var) args
  AstOpIntegral opCode args ->
    AstOpIntegral opCode $ map (substitute1Ast i var) args
  AstSumOfList args -> AstSumOfList $ map (substitute1Ast i var) args
  AstIota -> v1
  AstIndex v ix ->
    AstIndex (substitute1Ast i var v) (fmap (substitute1Ast i var) ix)
  AstSum v -> AstSum (substitute1Ast i var v)
  AstScatter sh v (vars, ix) ->
    AstScatter sh (substitute1Ast i var v)
                  (vars, fmap (substitute1Ast i var) ix)
  AstFromList l -> AstFromList $ map (substitute1Ast i var) l
  AstFromVector l -> AstFromVector $ V.map (substitute1Ast i var) l
  AstReplicate s v -> AstReplicate s (substitute1Ast i var v)
  AstAppend x y -> AstAppend (substitute1Ast i var x) (substitute1Ast i var y)
  AstSlice i2 n v -> AstSlice i2 n (substitute1Ast i var v)
  AstReverse v -> AstReverse (substitute1Ast i var v)
  AstTranspose perm v -> AstTranspose perm (substitute1Ast i var v)
  AstReshape sh v -> AstReshape sh (substitute1Ast i var v)
  AstBuild1 k (var2, v) -> AstBuild1 k (var2, substitute1Ast i var v)
  AstGather sh v (vars, ix) ->
    AstGather sh (substitute1Ast i var v)
                  (vars, fmap (substitute1Ast i var) ix)
  AstCast v -> AstCast $ substitute1Ast i var v
  AstFromIntegral v -> AstFromIntegral $ substitute1Ast i var v
  AstSToR v -> AstSToR $ substitute1AstS i var v
  AstConst _a -> v1
  AstConstant a -> AstConstant $ substitute1Ast i var a
  AstPrimalPart a -> AstPrimalPart $ substitute1Ast i var a
  AstDualPart a -> AstDualPart $ substitute1Ast i var a
  AstD u u' -> AstD (substitute1Ast i var u) (substitute1Ast i var u')
  AstLetDomains vars l v ->
    AstLetDomains vars (substitute1AstDomains i var l)
                       (substitute1Ast i var v)
  AstCond b v w -> AstCond (substitute1AstBool i var b)
                           (substitute1Ast i var v)
                           (substitute1Ast i var w)
  AstFloor a -> AstFloor (substitute1Ast i var a)
  AstMinIndex a -> AstMinIndex (substitute1Ast i var a)
  AstMaxIndex a -> AstMaxIndex (substitute1Ast i var a)

substitute1AstDynamic
  :: (GoodScalar r, GoodScalar r2, AstSpan s, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarId -> AstDynamic s r
  -> AstDynamic s r
substitute1AstDynamic i var = \case
  AstRToD t -> AstRToD $ substitute1Ast i var t
  AstSToD t -> AstSToD $ substitute1AstS i var t

substitute1AstDomains
  :: (GoodScalar r2, AstSpan s, AstSpan s2)
  => SubstitutionPayload s2 r2 -> AstVarId -> AstDomains s -> AstDomains s
substitute1AstDomains i var = \case
  AstDomains l ->
    AstDomains $ V.map (\(DynamicExists d) ->
                          DynamicExists $ substitute1AstDynamic i var d) l
  AstDomainsLet var2 u v ->
    AstDomainsLet var2 (substitute1Ast i var u)
                       (substitute1AstDomains i var v)
  AstDomainsLetS var2 u v ->
    AstDomainsLetS var2 (substitute1AstS i var u)
                        (substitute1AstDomains i var v)

substitute1AstBool :: (GoodScalar r2, AstSpan s2)
                   => SubstitutionPayload s2 r2 -> AstVarId -> AstBool
                   -> AstBool
substitute1AstBool i var b1 = case b1 of
  AstBoolOp opCodeBool args ->
    AstBoolOp opCodeBool $ map (substitute1AstBool i var) args
  AstBoolConst _a -> b1
  AstRel opCodeRel args -> AstRel opCodeRel $ map (substitute1Ast i var) args
  AstRelS opCodeRel args -> AstRelS opCodeRel $ map (substitute1AstS i var) args

substitute1AstS :: forall sh s s2 r r2.
                   (GoodScalar r, GoodScalar r2, OS.Shape sh, AstSpan s, AstSpan s2)
                => SubstitutionPayload s2 r2 -> AstVarId -> AstShaped s r sh
                -> AstShaped s r sh
substitute1AstS i var v1 = case v1 of
  AstVarS var2 ->
    if var == var2
    then case i of
      SubstitutionPayloadShaped @_ @_ @sh2 t -> case sameAstSpan @s @s2 of
        Just Refl -> case sameShape @sh2 @sh of
          Just Refl -> case testEquality (typeRep @r2) (typeRep @r) of
            Just Refl -> t
            _ -> error "substitute1AstS: scalar"
          _ -> error "substitute1AstS: shape"
        _ -> error "substitute1Ast: span"
      _ -> error "substitute1AstS: type"
    else v1
  AstLetS var2 u v ->
    AstLetS var2 (substitute1AstS i var u) (substitute1AstS i var v)
  AstLetADShareS{} -> error "substitute1AstS: AstLetADShareS"
  AstNmS opCode args -> AstNmS opCode $ map (substitute1AstS i var) args
  AstOpS opCode args -> AstOpS opCode $ map (substitute1AstS i var) args
  AstOpIntegralS opCode args ->
    AstOpIntegralS opCode $ map (substitute1AstS i var) args
  AstSumOfListS args -> AstSumOfListS $ map (substitute1AstS i var) args
  AstIotaS -> v1
  AstIndexS v ix ->
    AstIndexS (substitute1AstS i var v) (fmap (substitute1Ast i var) ix)
  AstSumS v -> AstSumS (substitute1AstS i var v)
  AstScatterS v (vars, ix) ->
    AstScatterS (substitute1AstS i var v)
                (vars, fmap (substitute1Ast i var) ix)
  AstFromListS l -> AstFromListS $ map (substitute1AstS i var) l
  AstFromVectorS l -> AstFromVectorS $ V.map (substitute1AstS i var) l
  AstReplicateS v -> AstReplicateS (substitute1AstS i var v)
  AstAppendS x y ->
    AstAppendS (substitute1AstS i var x) (substitute1AstS i var y)
  AstSliceS @i v -> AstSliceS @i (substitute1AstS i var v)
  AstReverseS v -> AstReverseS (substitute1AstS i var v)
  AstTransposeS @perm v -> AstTransposeS @perm (substitute1AstS i var v)
  AstReshapeS v -> AstReshapeS (substitute1AstS i var v)
  AstBuild1S (var2, v) -> AstBuild1S (var2, substitute1AstS i var v)
  AstGatherS v (vars, ix) ->
    AstGatherS (substitute1AstS i var v)
               (vars, fmap (substitute1Ast i var) ix)
  AstCastS v -> AstCastS $ substitute1AstS i var v
  AstFromIntegralS a -> AstFromIntegralS (substitute1AstS i var a)
  AstRToS v -> AstRToS $ substitute1Ast i var v
  AstConstS _a -> v1
  AstConstantS a -> AstConstantS (substitute1AstS i var a)
  AstPrimalPartS a -> AstPrimalPartS $ substitute1AstS i var a
  AstDualPartS a -> AstDualPartS $ substitute1AstS i var a
  AstDS u u' -> AstDS (substitute1AstS i var u) (substitute1AstS i var u')
  AstLetDomainsS vars l v ->
    AstLetDomainsS vars (substitute1AstDomains i var l)
                        (substitute1AstS i var v)
  AstCondS b v w -> AstCondS (substitute1AstBool i var b)
                             (substitute1AstS i var v)
                             (substitute1AstS i var w)
  AstFloorS a -> AstFloorS (substitute1AstS i var a)
  AstMinIndexS a -> AstMinIndexS (substitute1AstS i var a)
  AstMaxIndexS a -> AstMaxIndexS (substitute1AstS i var a)

-- * Determining if a term is too small to require sharing

astIsSmall :: forall n s r. KnownNat n
           => Bool -> AstRanked s r n -> Bool
astIsSmall relaxed = \case
  AstVar{} -> True
  AstIota -> True
  AstConst{} -> valueOf @n == (0 :: Int)
  AstConstant v -> astIsSmall relaxed v
  AstReplicate _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via tricks, so prob. safe
  AstSlice _ _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTranspose _ v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstSToR v -> astIsSmallS relaxed v
  _ -> False

astIsSmallS :: forall sh s r. OS.Shape sh
            => Bool -> AstShaped s r sh -> Bool
astIsSmallS relaxed = \case
  AstVarS{} -> True
  AstIotaS -> True
  AstConstS{} -> null (OS.shapeT @sh)
  AstConstantS v -> astIsSmallS relaxed v
  AstReplicateS v ->
    relaxed && astIsSmallS relaxed v  -- materialized via tricks, so prob. safe
  AstSliceS v ->
    relaxed && astIsSmallS relaxed v  -- materialized via vector slice; cheap
  AstTransposeS v ->
    relaxed && astIsSmallS relaxed v  -- often cheap and often fuses
  AstRToS v -> astIsSmall relaxed v
  _ -> False


-- * Odds and ends

unwrapAstDomains :: AstDomains s -> Data.Vector.Vector (DynamicExists (AstDynamic s))
unwrapAstDomains = \case
  AstDomains l -> l
  AstDomainsLet _ _ v -> unwrapAstDomains v
  AstDomainsLetS _ _ v -> unwrapAstDomains v

bindsToLet :: forall n s r. (KnownNat n, AstSpan s)
           => AstRanked s r n -> [(AstId, DynamicExists (AstDynamic s))]
           -> AstRanked s r n
{-# INLINE bindsToLet #-}  -- help list fusion
bindsToLet = foldl' bindToLet
 where
  bindToLet :: AstRanked s r n -> (AstId, DynamicExists (AstDynamic s))
            -> AstRanked s r n
  bindToLet u (var, DynamicExists @_ @r2 d) = case d of
    AstRToD w -> AstLet (astIdToAstVarId var) w u
    AstSToD @sh w ->  -- rare or impossible, but let's implement it anyway:
      let p = length $ OS.shapeT @sh
      in case someNatVal $ toInteger p of
        Just (SomeNat @p _proxy) ->
          -- I can't use sameNat to compare the types, because no KnownNat!
          gcastWith (unsafeCoerce Refl :: OS.Rank sh :~: p) $
          AstLet (astIdToAstVarId var) (AstSToR w) u
        Nothing -> error "bindsToLet: impossible someNatVal error"

bindsToLetS :: forall sh s r. (OS.Shape sh, AstSpan s)
            => AstShaped s r sh -> [(AstId, DynamicExists (AstDynamic s))]
            -> AstShaped s r sh
{-# INLINE bindsToLetS #-}  -- help list fusion
bindsToLetS = foldl' bindToLetS
 where
  bindToLetS :: AstShaped s r sh -> (AstId, DynamicExists (AstDynamic s))
             -> AstShaped s r sh
  bindToLetS u (var, DynamicExists @_ @r2 d) = case d of
    AstRToD @n w ->  -- rare or impossible, but let's implement it anyway:
      let sh = shapeToList $ shapeAst w
      in if valueOf @n == length sh
         then OS.withShapeP sh $ \(_proxy :: Proxy sh2) ->
           gcastWith (unsafeCoerce Refl :: n :~: OS.Rank sh2)
           $ AstLetS (astIdToAstVarId var) (AstRToS @sh2 w) u
         else error "bindsToLetS: rank mismatch"
    AstSToD w -> AstLetS (astIdToAstVarId var) w u

bindsToDomainsLet
   :: AstDomains s -> [(AstId, DynamicExists (AstDynamic s))] -> AstDomains s
{-# INLINE bindsToDomainsLet #-}   -- help list fusion
bindsToDomainsLet = foldl' bindToDomainsLet
 where
  bindToDomainsLet u (var, DynamicExists d) = case d of
    AstRToD w -> AstDomainsLet (astIdToAstVarId var) w u
    AstSToD w -> AstDomainsLetS (astIdToAstVarId var) w u
