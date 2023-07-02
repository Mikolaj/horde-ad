{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | An assortment of operations on AST of the code to be differentiated
-- or resulting from the differentiation.
module HordeAd.Core.AstTools
  ( shapeAst, lengthAst
  , intVarInAst, intVarInAstInt, intVarInAstBool, intVarInIndex
  , intVarInAstS, intVarInIndexS
  , SubstitutionPayload(..)
  , substitute1Ast, substitute1AstDomains, substitute1AstInt, substitute1AstBool
  , substitute1AstS
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
import HordeAd.Internal.OrthotopeOrphanInstances (sameShape)

-- * Shape calculation

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: forall n r. (KnownNat n, GoodScalar r)
         => AstRanked r n -> ShapeInt n
shapeAst v1 = case v1 of
  AstVar sh _var -> sh
  AstLet _ _ v -> shapeAst v
  AstLetADShare _ v-> shapeAst v
  AstOp _opCode args -> case args of
    [] -> error "shapeAst: AstOp with no arguments"
    t : _ -> shapeAst t
  AstSumOfList args -> case args of
    [] -> error "shapeAst: AstSumOfList with no arguments"
    t : _ -> shapeAst t
  AstIota -> singletonShape (maxBound :: Int)  -- ought to be enough
  AstIndex v (_is :: Index m AstInt) -> dropShape @m (shapeAst v)
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
  AstSToR @sh _ -> listShapeToShape $ OS.shapeT @sh
  AstConst a -> listShapeToShape $ OR.shapeL a
  AstConstant (AstPrimalPart a) -> shapeAst a
  AstD (AstPrimalPart u) _ -> shapeAst u
  AstLetDomains _ _ v -> shapeAst v

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, GoodScalar r) => AstRanked r (1 + n) -> Int
lengthAst v1 = case shapeAst v1 of
  ZS -> error "lengthAst: impossible pattern needlessly required"
  k :$ _ -> k


-- * Variable occurence detection

-- We assume no variable is shared between a binding and its nested binding
-- and nobody asks about occurences of variables that are bound.
-- This keeps the occurence checking code simple, because we never need
-- to compare variables to any variable in the bindings.
intVarInAst :: AstVarId -> AstRanked r n -> Bool
intVarInAst var = \case
  AstVar{} -> False  -- not an int variable
  AstLet _var2 u v -> intVarInAst var u || intVarInAst var v
  AstLetADShare _l v -> intVarInAst var v
    -- this is a (we assume) conservative approximation, to avoid a costly
    -- traversal; in (almost?) all cases this is also the true answer,
    -- because the let definitions come from the outside and so can't
    -- contain a local variable we (always?) ask about
  AstOp _ l -> any (intVarInAst var) l
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
  AstSToR v -> intVarInAstS var v
  AstConst{} -> False
  AstConstant (AstPrimalPart v) -> intVarInAst var v
  AstD (AstPrimalPart u) (AstDualPart u') ->
    intVarInAst var u || intVarInAst var u'
  AstLetDomains _vars l v -> intVarInAstDomains var l || intVarInAst var v

intVarInAstDomains :: AstVarId -> AstDomains r -> Bool
intVarInAstDomains var = \case
  AstDomains l ->
    let f (AstRToD t) = intVarInAst var t
        f (AstSToD t) = intVarInAstS var t
    in any f l
  AstDomainsLet _var2 u v -> intVarInAst var u || intVarInAstDomains var v
  AstDomainsLetS _var2 u v -> intVarInAstS var u || intVarInAstDomains var v

intVarInAstInt :: AstVarId -> AstInt -> Bool
intVarInAstInt var = \case
  AstIntVar var2 -> var == var2  -- the only int variable not in binder position
  AstIntOp _ l -> any (intVarInAstInt var) l
  AstIntConst{} -> False
  AstIntFloor (AstPrimalPart v) -> intVarInAst var v
  AstIntFloorS (AstPrimalPartS v) -> intVarInAstS var v
  AstIntCond b x y ->
    intVarInAstBool var b || intVarInAstInt var x || intVarInAstInt var y
  AstMinIndex1 (AstPrimalPart v) -> intVarInAst var v
  AstMaxIndex1 (AstPrimalPart v) -> intVarInAst var v
  AstMinIndex1S (AstPrimalPartS v) -> intVarInAstS var v
  AstMaxIndex1S (AstPrimalPartS v) -> intVarInAstS var v

intVarInAstBool :: AstVarId -> AstBool -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> any (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> any (intVarInAst var . unAstPrimalPart) l
  AstRelS _ l -> any (intVarInAstS var . unAstPrimalPartS) l
  AstRelInt _ l  -> any (intVarInAstInt var) l

intVarInIndex :: AstVarId -> AstIndex n -> Bool
intVarInIndex var = any (intVarInAstInt var)

intVarInAstS :: AstVarId -> AstShaped r sh -> Bool
intVarInAstS var = \case
  AstVarS{} -> False  -- not an int variable
  AstLetS _var2 u v -> intVarInAstS var u || intVarInAstS var v
  AstLetADShareS _l v -> intVarInAstS var v
    -- this is a (we assume) conservative approximation, to avoid a costly
    -- traversal; in (almost?) all cases this is also the true answer,
    -- because the let definitions come from the outside and so can't
    -- contain a local variable we (always?) ask about
  AstOpS _ l -> any (intVarInAstS var) l
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
  AstRToS v -> intVarInAst var v
  AstConstS{} -> False
  AstConstantS (AstPrimalPartS v) -> intVarInAstS var v
  AstDS (AstPrimalPartS u) (AstDualPartS u') ->
    intVarInAstS var u || intVarInAstS var u'
  AstLetDomainsS _vars l v -> intVarInAstDomains var l || intVarInAstS var v

intVarInIndexS :: AstVarId -> AstIndexS sh -> Bool
intVarInIndexS var = any (intVarInAstInt var)


-- * Substitution

data SubstitutionPayload =
    SubstitutionPayloadInt AstInt
  | forall r n. (KnownNat n, GoodScalar r)
                => SubstitutionPayloadRanked (AstRanked r n)
  | forall r sh. (OS.Shape sh, GoodScalar r)
                 => SubstitutionPayloadShaped (AstShaped r sh)

-- We assume no variable is shared between a binding and its nested binding
-- and nobody substitutes into variables that are bound.
-- This keeps the substitution code simple, because we never need to compare
-- variables to any variable in the bindings.
--
-- The Either is a hack until we merge Ast and AstInt.
substitute1Ast :: forall n r.
                  (GoodScalar r, KnownNat n)
               => SubstitutionPayload -> AstVarId -> AstRanked r n
               -> AstRanked r n
substitute1Ast i var v1 = case v1 of
  AstVar sh var2 ->
    if var == var2
    then case i of
      SubstitutionPayloadRanked @r2 @m t ->
        case sameNat (Proxy @m) (Proxy @n) of
          Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
            Just Refl -> assert (shapeAst t == sh) t
            _ -> error "substitute1Ast: type of payload"
          _ -> error "substitute1Ast: payload"
      _ -> error "substitute1Ast: n"
    else v1
  AstLet var2 u v ->
    AstLet var2 (substitute1Ast i var u) (substitute1Ast i var v)
  AstLetADShare{} -> error "substitute1Ast: AstLetADShare"
  AstOp opCode args -> AstOp opCode $ map (substitute1Ast i var) args
  AstSumOfList args -> AstSumOfList $ map (substitute1Ast i var) args
  AstIota -> v1
  AstIndex v is ->
    AstIndex (substitute1Ast i var v) (fmap (substitute1AstInt i var) is)
  AstSum v -> AstSum (substitute1Ast i var v)
  AstScatter sh v (vars, ix) ->
    AstScatter sh (substitute1Ast i var v)
                  (vars, fmap (substitute1AstInt i var) ix)
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
                  (vars, fmap (substitute1AstInt i var) ix)
  AstSToR v -> AstSToR $ substitute1AstS i var v
  AstConst _a -> v1
  AstConstant (AstPrimalPart a) ->
    AstConstant (AstPrimalPart $ substitute1Ast i var a)
  AstD (AstPrimalPart u) (AstDualPart u') ->
    AstD (AstPrimalPart $ substitute1Ast i var u)
         (AstDualPart $ substitute1Ast i var u')
  AstLetDomains vars l v ->
    AstLetDomains vars (substitute1AstDomains i var l)
                       (substitute1Ast i var v)

substitute1AstDynamic
  :: GoodScalar r
  => SubstitutionPayload -> AstVarId -> AstDynamic r
  -> AstDynamic r
substitute1AstDynamic i var = \case
  AstRToD t -> AstRToD $ substitute1Ast i var t
  AstSToD t -> AstSToD $ substitute1AstS i var t

substitute1AstDomains
  :: GoodScalar r
  => SubstitutionPayload -> AstVarId -> AstDomains r
  -> AstDomains r
substitute1AstDomains i var = \case
  AstDomains l -> AstDomains $ V.map (substitute1AstDynamic i var) l
  AstDomainsLet var2 u v ->
    AstDomainsLet var2 (substitute1Ast i var u)
                       (substitute1AstDomains i var v)
  AstDomainsLetS var2 u v ->
    AstDomainsLetS var2 (substitute1AstS i var u)
                        (substitute1AstDomains i var v)

substitute1AstInt :: SubstitutionPayload -> AstVarId -> AstInt
                  -> AstInt
substitute1AstInt i var i2 = case i2 of
  AstIntVar var2 ->
    if var == var2 then case i of
      SubstitutionPayloadInt t -> t
      _ -> error "substitute1AstInt: payload"
    else i2
  AstIntOp opCodeInt args ->
    AstIntOp opCodeInt $ map (substitute1AstInt i var) args
  AstIntConst _a -> i2
  AstIntFloor (AstPrimalPart v) ->
    AstIntFloor $ AstPrimalPart $ substitute1Ast i var v
  AstIntFloorS (AstPrimalPartS v) ->
    AstIntFloorS $ AstPrimalPartS $ substitute1AstS i var v
  AstIntCond b a1 a2 ->
    AstIntCond (substitute1AstBool i var b)
               (substitute1AstInt i var a1) (substitute1AstInt i var a2)
  AstMinIndex1 (AstPrimalPart v) ->
    AstMinIndex1 $ AstPrimalPart $ substitute1Ast i var v
  AstMaxIndex1 (AstPrimalPart v) ->
    AstMaxIndex1 $ AstPrimalPart $ substitute1Ast i var v
  AstMinIndex1S (AstPrimalPartS v) ->
    AstMinIndex1S $ AstPrimalPartS $ substitute1AstS i var v
  AstMaxIndex1S (AstPrimalPartS v) ->
    AstMaxIndex1S $ AstPrimalPartS $ substitute1AstS i var v

substitute1AstBool :: SubstitutionPayload -> AstVarId -> AstBool
                   -> AstBool
substitute1AstBool i var b1 = case b1 of
  AstBoolOp opCodeBool args ->
    AstBoolOp opCodeBool $ map (substitute1AstBool i var) args
  AstBoolConst _a -> b1
  AstRel opCodeRel args ->
    AstRel opCodeRel
    $ map (AstPrimalPart . substitute1Ast i var . unAstPrimalPart) args
  AstRelS opCodeRel args ->
    AstRelS opCodeRel
    $ map (AstPrimalPartS . substitute1AstS i var . unAstPrimalPartS) args
  AstRelInt opCodeRel args ->
    AstRelInt opCodeRel $ map (substitute1AstInt i var) args

substitute1AstS :: forall sh r.
                   (GoodScalar r, OS.Shape sh)
                => SubstitutionPayload -> AstVarId -> AstShaped r sh
                -> AstShaped r sh
substitute1AstS i var v1 = case v1 of
  AstVarS var2 ->
    if var == var2
    then case i of
      SubstitutionPayloadShaped @r2 @sh2 t -> case sameShape @sh2 @sh of
        Just Refl -> case testEquality (typeRep @r) (typeRep @r2) of
          Just Refl -> t
          _ -> error "substitute1AstS: type of payload"
        _ -> error "substitute1AstS: payload"
      _ -> error "substitute1AstS: n"
    else v1
  AstLetS var2 u v ->
    AstLetS var2 (substitute1AstS i var u) (substitute1AstS i var v)
  AstLetADShareS{} -> error "substitute1AstS: AstLetADShareS"
  AstOpS opCode args -> AstOpS opCode $ map (substitute1AstS i var) args
  AstSumOfListS args -> AstSumOfListS $ map (substitute1AstS i var) args
  AstIotaS -> v1
  AstIndexS v is ->
    AstIndexS (substitute1AstS i var v) (fmap (substitute1AstInt i var) is)
  AstSumS v -> AstSumS (substitute1AstS i var v)
  AstScatterS v (vars, ix) ->
    AstScatterS (substitute1AstS i var v)
                (vars, fmap (substitute1AstInt i var) ix)
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
               (vars, fmap (substitute1AstInt i var) ix)
  AstRToS v -> AstRToS $ substitute1Ast i var v
  AstConstS _a -> v1
  AstConstantS (AstPrimalPartS a) ->
    AstConstantS (AstPrimalPartS $ substitute1AstS i var a)
  AstDS (AstPrimalPartS u) (AstDualPartS u') ->
    AstDS (AstPrimalPartS $ substitute1AstS i var u)
          (AstDualPartS $ substitute1AstS i var u')
  AstLetDomainsS vars l v ->
    AstLetDomainsS vars (substitute1AstDomains i var l)
                        (substitute1AstS i var v)


-- * Determining if a term is too small to require sharing

astIsSmall :: forall n r. KnownNat n
           => Bool -> AstRanked r n -> Bool
astIsSmall relaxed = \case
  AstVar{} -> True
  AstIota -> True
  AstIndex AstIota _ -> True  -- TODO: what if ix contains a big tensor?
  AstConst{} -> valueOf @n == (0 :: Int)
  AstConstant (AstPrimalPart v) -> astIsSmall relaxed v
  AstReplicate _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via tricks, so prob. safe
  AstSlice _ _ v ->
    relaxed && astIsSmall relaxed v  -- materialized via vector slice; cheap
  AstTranspose _ v ->
    relaxed && astIsSmall relaxed v  -- often cheap and often fuses
  AstSToR v -> astIsSmallS relaxed v
  _ -> False

astIsSmallS :: forall sh r. OS.Shape sh
            => Bool -> AstShaped r sh -> Bool
astIsSmallS relaxed = \case
  AstVarS{} -> True
  AstIotaS -> True
  AstIndexS AstIotaS _ -> True  -- TODO: what if ix contains a big tensor?
  AstConstS{} -> null (OS.shapeT @sh)
  AstConstantS (AstPrimalPartS v) -> astIsSmallS relaxed v
  AstReplicateS v ->
    relaxed && astIsSmallS relaxed v  -- materialized via tricks, so prob. safe
  AstSliceS v ->
    relaxed && astIsSmallS relaxed v  -- materialized via vector slice; cheap
  AstTransposeS v ->
    relaxed && astIsSmallS relaxed v  -- often cheap and often fuses
  AstRToS v -> astIsSmall relaxed v
  _ -> False


-- * Odds and ends

unwrapAstDomains :: AstDomains r -> Data.Vector.Vector (AstDynamic r)
unwrapAstDomains = \case
  AstDomains l -> l
  AstDomainsLet _ _ v -> unwrapAstDomains v
  AstDomainsLetS _ _ v -> unwrapAstDomains v

bindsToLet :: forall n r. KnownNat n
           => AstRanked r n -> [(AstVarId, DynamicExists AstDynamic)]
           -> AstRanked r n
{-# INLINE bindsToLet #-}  -- help list fusion
bindsToLet = foldl' bindToLet
 where
  bindToLet :: AstRanked r n -> (AstVarId, DynamicExists AstDynamic)
            -> AstRanked r n
  bindToLet u (var, DynamicExists @r2 d) = case d of
    AstRToD w -> AstLet var w u
    AstSToD @sh w ->  -- rare or impossible, but let's implement it anyway:
      let p = length $ OS.shapeT @sh
      in case someNatVal $ toInteger p of
        Just (SomeNat @p _proxy) ->
          -- I can't use sameNat to compare the types, because no KnownNat!
          gcastWith (unsafeCoerce Refl :: OS.Rank sh :~: p) $
          AstLet var (AstSToR w) u
        Nothing -> error "bindsToLet: impossible someNatVal error"

bindsToLetS :: forall sh r. OS.Shape sh
            => AstShaped r sh -> [(AstVarId, DynamicExists AstDynamic)]
            -> AstShaped r sh
{-# INLINE bindsToLetS #-}  -- help list fusion
bindsToLetS = foldl' bindToLetS
 where
  bindToLetS :: AstShaped r sh -> (AstVarId, DynamicExists AstDynamic)
             -> AstShaped r sh
  bindToLetS u (var, DynamicExists @r2 d) = case d of
    AstRToD @n w ->  -- rare or impossible, but let's implement it anyway:
      let sh = shapeToList $ shapeAst w
      in if valueOf @n == length sh
         then OS.withShapeP sh $ \(_proxy :: Proxy sh2) ->
           gcastWith (unsafeCoerce Refl :: n :~: OS.Rank sh2)
           $ AstLetS var (AstRToS @sh2 w) u
         else error "bindsToLetS: rank mismatch"
    AstSToD w -> AstLetS var w u

bindsToDomainsLet
   :: AstDomains r -> [(AstVarId, DynamicExists AstDynamic)] -> AstDomains r
{-# INLINE bindsToDomainsLet #-}   -- help list fusion
bindsToDomainsLet = foldl' bindToDomainsLet
 where
  bindToDomainsLet u (var, DynamicExists d) = case d of
    AstRToD w -> AstDomainsLet var w u
    AstSToD w -> AstDomainsLetS var w u
