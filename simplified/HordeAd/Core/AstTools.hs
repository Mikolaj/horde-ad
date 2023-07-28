{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | An assortment of operations on AST of the code to be differentiated
-- or resulting from the differentiation.
module HordeAd.Core.AstTools
  ( shapeAst, lengthAst
  , intVarInAst, intVarInAstBool, intVarInIndex
  , intVarInAstS, intVarInIndexS, varNameInAst, varNameInAstS
  , astIsSmall, astIsSmallS
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
import HordeAd.Core.SizedIndex
import HordeAd.Core.Types

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
-- This code works, in fact, for any variables, not only int variables.
intVarInAst :: forall s s2 r n. (AstSpan s, AstSpan s2)
            => AstVarId s -> AstRanked s2 r n -> Bool
intVarInAst var = \case
  AstVar _ var2 -> fromEnum var == fromEnum var2
                   && case sameAstSpan @s @s2 of
                        Just Refl -> True
                        _ -> error "intVarInAst: wrong span"
  AstLet _var2 u v -> intVarInAst var u || intVarInAst var v
  AstLetADShare l v | Just Refl <- sameAstSpan @s @PrimalSpan ->
    intVarInADShare intIdInAstDynamic (astVarIdToAstId var) l
    || intVarInAst var v
  AstLetADShare{} -> False
  AstCond b v w ->
    intVarInAstBool var b || intVarInAst var v || intVarInAst var w
  AstMinIndex a -> intVarInAst var a
  AstMaxIndex a -> intVarInAst var a
  AstFloor a -> intVarInAst var a
  AstIota -> False
  AstNm _ l -> any (intVarInAst var) l
  AstOp _ l -> any (intVarInAst var) l
  AstOpIntegral _ l -> any (intVarInAst var) l
  AstSumOfList l -> any (intVarInAst var) l
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
  AstConst{} -> False
  AstSToR v -> intVarInAstS var v
  AstConstant v -> intVarInAst var v
  AstPrimalPart a -> intVarInAst var a
  AstDualPart a -> intVarInAst var a
  AstD u u' -> intVarInAst var u || intVarInAst var u'
  AstLetDomains _vars l v -> intVarInAstDomains var l || intVarInAst var v

intVarInAstDomains :: (AstSpan s, AstSpan s2)
                   => AstVarId s -> AstDomains s2 -> Bool
intVarInAstDomains var = \case
  AstDomains l -> let f (DynamicExists d) = intVarInAstDynamic var d
                  in any f l
  AstDomainsLet _var2 u v -> intVarInAst var u || intVarInAstDomains var v
  AstDomainsLetS _var2 u v -> intVarInAstS var u || intVarInAstDomains var v

intVarInAstDynamic :: (AstSpan s, AstSpan s2)
                   => AstVarId s -> AstDynamic s2 r -> Bool
intVarInAstDynamic var = \case
  AstRToD t -> intVarInAst var t
  AstSToD t -> intVarInAstS var t

intIdInAstDynamic :: AstSpan s => AstId -> AstDynamic s r -> Bool
intIdInAstDynamic var = \case
  AstRToD t -> intVarInAst (astIdToAstVarId @PrimalSpan var) t
  AstSToD t -> intVarInAstS (astIdToAstVarId @PrimalSpan var) t

intVarInAstBool :: AstSpan s => AstVarId s -> AstBool -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> any (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> any (intVarInAst var) l
  AstRelS _ l -> any (intVarInAstS var) l

intVarInIndex :: AstSpan s => AstVarId s -> AstIndex n -> Bool
intVarInIndex var = any (intVarInAst var)

intVarInAstS :: forall s s2 r sh. (AstSpan s, AstSpan s2)
             => AstVarId s -> AstShaped s2 r sh -> Bool
intVarInAstS var = \case
  AstVarS var2 -> fromEnum var == fromEnum var2
                  && case sameAstSpan @s @s2 of
                       Just Refl -> True
                       _ -> error "intVarInAst: wrong span"
  AstLetS _var2 u v -> intVarInAstS var u || intVarInAstS var v
  AstLetADShareS l v | Just Refl <- sameAstSpan @s @PrimalSpan ->
    intVarInADShare intIdInAstDynamic (astVarIdToAstId var) l
    || intVarInAstS var v
  AstLetADShareS{} -> False
  AstCondS b v w ->
    intVarInAstBool var b || intVarInAstS var v || intVarInAstS var w
  AstMinIndexS a -> intVarInAstS var a
  AstMaxIndexS a -> intVarInAstS var a
  AstFloorS a -> intVarInAstS var a
  AstIotaS -> False
  AstNmS _ l -> any (intVarInAstS var) l
  AstOpS _ l -> any (intVarInAstS var) l
  AstOpIntegralS _ l -> any (intVarInAstS var) l
  AstSumOfListS l -> any (intVarInAstS var) l
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
  AstConstS{} -> False
  AstRToS v -> intVarInAst var v
  AstConstantS v -> intVarInAstS var v
  AstPrimalPartS a -> intVarInAstS var a
  AstDualPartS a -> intVarInAstS var a
  AstDS u u' -> intVarInAstS var u || intVarInAstS var u'
  AstLetDomainsS _vars l v -> intVarInAstDomains var l || intVarInAstS var v

intVarInIndexS :: AstSpan s => AstVarId s -> AstIndexS sh -> Bool
intVarInIndexS var = any (intVarInAst var)

varNameInAst :: (AstSpan s, AstSpan s2)
             => AstVarName s (AstRanked s) r n -> AstRanked s2 r2 n2 -> Bool
varNameInAst (AstVarName var) = intVarInAst var

varNameInAstS :: (AstSpan s, AstSpan s2)
              => AstVarName s f r sh -> AstShaped s2 r2 sh2 -> Bool
varNameInAstS (AstVarName var) = intVarInAstS var


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
