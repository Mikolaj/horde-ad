{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | An assortment of operations working on AST of the code to be differentiated
-- or resulting from the differentiation.
module HordeAd.Core.AstTools
  ( -- * Shape calculation
    shapeAst, lengthAst
    -- * Variable occurence detection
  , varInAst, varInAstBool, varInIndex
  , varInAstS, varInIndexS, varNameInAst, varNameInAstS
    -- * Determining if a term is too small to require sharing
  , astIsSmall, astIsSmallS
    -- * Odds and ends
  , unwrapAstDomains, bindsToLet, bindsToLetS, bindsToDomainsLet
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import           Data.List (foldl')
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality (gcastWith, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
import HordeAd.Core.Types
import HordeAd.Util.SizedIndex

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
  AstCond _b v _w -> shapeAst v
  AstMinIndex a -> initShape $ shapeAst a
  AstMaxIndex a -> initShape $ shapeAst a
  AstFloor a -> shapeAst a
  AstIota -> singletonShape (maxBound :: Int)  -- ought to be enough
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
  AstSToR @sh _ -> listShapeToShape $ OS.shapeT @sh
  AstConstant a -> shapeAst a
  AstPrimalPart a -> shapeAst a
  AstDualPart a -> shapeAst a
  AstD u _ -> shapeAst u
  AstLetDomains _ _ v -> shapeAst v

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
varInAst :: forall s s2 r n. (AstSpan s, AstSpan s2)
         => AstVarId s -> AstRanked s2 r n -> Bool
varInAst var = \case
  AstVar _ var2 -> fromEnum var == fromEnum var2
                   && case sameAstSpan @s @s2 of
                        Just Refl -> True
                        _ -> error "varInAst: wrong span"
  AstLet _var2 u v -> varInAst var u || varInAst var v
  AstLetADShare l v | Just Refl <- sameAstSpan @s @PrimalSpan ->
    varInADShare intIdInAstDynamic (astVarIdToAstId var) l
    || varInAst var v
  AstLetADShare{} -> False
  AstCond b v w ->
    varInAstBool var b || varInAst var v || varInAst var w
  AstMinIndex a -> varInAst var a
  AstMaxIndex a -> varInAst var a
  AstFloor a -> varInAst var a
  AstIota -> False
  AstNm _ l -> any (varInAst var) l
  AstOp _ l -> any (varInAst var) l
  AstOpIntegral _ l -> any (varInAst var) l
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
  AstSToR v -> varInAstS var v
  AstConstant v -> varInAst var v
  AstPrimalPart a -> varInAst var a
  AstDualPart a -> varInAst var a
  AstD u u' -> varInAst var u || varInAst var u'
  AstLetDomains _vars l v -> varInAstDomains var l || varInAst var v

varInAstDomains :: (AstSpan s, AstSpan s2)
                => AstVarId s -> AstDomains s2 -> Bool
varInAstDomains var = \case
  AstDomains l -> let f (DynamicExists d) = varInAstDynamic var d
                  in any f l
  AstDomainsLet _var2 u v -> varInAst var u || varInAstDomains var v
  AstDomainsLetS _var2 u v -> varInAstS var u || varInAstDomains var v

varInAstDynamic :: (AstSpan s, AstSpan s2)
                   => AstVarId s -> AstDynamic s2 r -> Bool
varInAstDynamic var = \case
  AstRToD t -> varInAst var t
  AstSToD t -> varInAstS var t

intIdInAstDynamic :: AstSpan s => AstId -> AstDynamic s r -> Bool
intIdInAstDynamic var = \case
  AstRToD t -> varInAst (astIdToAstVarId @PrimalSpan var) t
  AstSToD t -> varInAstS (astIdToAstVarId @PrimalSpan var) t

varInAstBool :: AstSpan s => AstVarId s -> AstBool -> Bool
varInAstBool var = \case
  AstBoolOp _ l -> any (varInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> any (varInAst var) l
  AstRelS _ l -> any (varInAstS var) l

varInIndex :: AstSpan s => AstVarId s -> AstIndex n -> Bool
varInIndex var = any (varInAst var)

varInAstS :: forall s s2 r sh. (AstSpan s, AstSpan s2)
          => AstVarId s -> AstShaped s2 r sh -> Bool
varInAstS var = \case
  AstVarS var2 -> fromEnum var == fromEnum var2
                  && case sameAstSpan @s @s2 of
                       Just Refl -> True
                       _ -> error "varInAst: wrong span"
  AstLetS _var2 u v -> varInAstS var u || varInAstS var v
  AstLetADShareS l v | Just Refl <- sameAstSpan @s @PrimalSpan ->
    varInADShare intIdInAstDynamic (astVarIdToAstId var) l
    || varInAstS var v
  AstLetADShareS{} -> False
  AstCondS b v w ->
    varInAstBool var b || varInAstS var v || varInAstS var w
  AstMinIndexS a -> varInAstS var a
  AstMaxIndexS a -> varInAstS var a
  AstFloorS a -> varInAstS var a
  AstIotaS -> False
  AstNmS _ l -> any (varInAstS var) l
  AstOpS _ l -> any (varInAstS var) l
  AstOpIntegralS _ l -> any (varInAstS var) l
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
  AstRToS v -> varInAst var v
  AstConstantS v -> varInAstS var v
  AstPrimalPartS a -> varInAstS var a
  AstDualPartS a -> varInAstS var a
  AstDS u u' -> varInAstS var u || varInAstS var u'
  AstLetDomainsS _vars l v -> varInAstDomains var l || varInAstS var v

varInIndexS :: AstSpan s => AstVarId s -> AstIndexS sh -> Bool
varInIndexS var = any (varInAst var)

varNameInAst :: (AstSpan s, AstSpan s2)
             => AstVarName s (AstRanked s) r n -> AstRanked s2 r2 n2 -> Bool
varNameInAst (AstVarName var) = varInAst var

varNameInAstS :: (AstSpan s, AstSpan s2)
              => AstVarName s f r sh -> AstShaped s2 r2 sh2 -> Bool
varNameInAstS (AstVarName var) = varInAstS var


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
  AstSToR v -> astIsSmallS relaxed v
  AstConstant v -> astIsSmall relaxed v
  AstPrimalPart v -> astIsSmall relaxed v
  AstDualPart v -> astIsSmall relaxed v
  _ -> False

astIsSmallS :: forall sh s r. OS.Shape sh
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
  AstConstS{} -> null (OS.shapeT @sh)
  AstRToS v -> astIsSmall relaxed v
  AstConstantS v -> astIsSmallS relaxed v
  AstPrimalPartS v -> astIsSmallS relaxed v
  AstDualPartS v -> astIsSmallS relaxed v
  _ -> False


-- * Odds and ends

unwrapAstDomains :: AstDomains s
                 -> Data.Vector.Vector (DynamicExists (AstDynamic s))
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
    AstRToD w -> AstLet (AstVarName $ astIdToAstVarId var) w u
    AstSToD @sh w ->  -- rare or impossible, but let's implement it anyway:
      let p = length $ OS.shapeT @sh
      in case someNatVal $ toInteger p of
        Just (SomeNat @p _proxy) ->
          -- I can't use sameNat to compare the types, because no KnownNat!
          gcastWith (unsafeCoerce Refl :: OS.Rank sh :~: p) $
          AstLet (AstVarName $ astIdToAstVarId var) (AstSToR w) u
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
           $ AstLetS (AstVarName $ astIdToAstVarId var) (AstRToS @sh2 w) u
         else error "bindsToLetS: rank mismatch"
    AstSToD w -> AstLetS (AstVarName $ astIdToAstVarId var) w u

bindsToDomainsLet
   :: AstDomains s -> [(AstId, DynamicExists (AstDynamic s))] -> AstDomains s
{-# INLINE bindsToDomainsLet #-}   -- help list fusion
bindsToDomainsLet = foldl' bindToDomainsLet
 where
  bindToDomainsLet u (var, DynamicExists d) = case d of
    AstRToD w -> AstDomainsLet (AstVarName $ astIdToAstVarId var) w u
    AstSToD w -> AstDomainsLetS (AstVarName $ astIdToAstVarId var) w u