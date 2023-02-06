{-# LANGUAGE DataKinds, GADTs #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Vectorization of the build operation in Ast.
module HordeAd.Core.AstVectorize
  ( build1VOccurenceUnknown
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList

-- | The application @build1VOccurenceUnknown k (var, v)@ vectorizes
-- the term @AstBuildPair1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurenceUnknown
  :: (KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1VOccurenceUnknown k (var, v0) =
  if intVarInAst var v0
  then build1V k (var, v0)
  else AstKonst k v0

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuildPair1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
build1V
  :: (KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1V k (var, v0) =
  case v0 of
    AstVar{} ->
      error "build1V: AstVar can't have free int variables"

    AstOp opCode args ->
      AstOp opCode $ map (\v -> build1VOccurenceUnknown k (var, v)) args

    AstConst{} ->
      error "build1V: AstConst can't have free int variables"
    AstConstant{} -> AstConstant $ AstPrimalPart1 $ AstBuildPair1 k (var, v0)
      -- this is very fast when interpreted in a smart way, but constant
      -- character needs to be exposed for nested cases;
      -- TODO: similarly propagate AstConstant upwards elsewhere
    AstScale (AstPrimalPart1 r) d ->
      AstScale (AstPrimalPart1 $ AstBuildPair1 k (var, r))  -- no need to vect
               (build1VOccurenceUnknown k (var, d))
    AstCond b v w ->
      build1V
        k (var, AstIndexN (AstFromList [v, w])
                          (singletonIndex $ AstIntCond b 0 1))

    AstConstInt{} -> AstConstant $ AstPrimalPart1 $ AstBuildPair1 k (var, v0)
    AstIndexN v is -> build1VIxOccurenceUnknown k (var, v, is)
      -- @var@ is in @v@ or @is@; TODO: simplify is first or even fully
      -- evaluate (may involve huge data processing) if contains no vars
      -- and then some things simplify a lot, e.g., if constant index,
      -- we may just pick the right element of a AstFromList
    AstSum v -> AstTranspose $ AstSum $ AstTranspose
                $ build1V k (var, v)
      -- that's because @build1 k (f . g) == map1 f (build1 k g)@
      -- and @map1 f == transpose . f . transpose@
      -- TODO: though only for some f; check and fail early
    AstFromList l ->
      AstTranspose
      $ AstFromList (map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstFromVector l ->
      AstTranspose
      $ AstFromVector (V.map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstKonst s v -> AstTranspose $ AstKonst s $ AstTranspose
                    $ build1V k (var, v)
    AstAppend v w -> AstTranspose $ AstAppend
                       (AstTranspose $ build1VOccurenceUnknown k (var, v))
                       (AstTranspose $ build1VOccurenceUnknown k (var, w))
    AstSlice i s v -> AstTranspose $ AstSlice i s $ AstTranspose
                      $ build1V k (var, v)
    AstReverse v -> AstTranspose $ AstReverse $ AstTranspose
                    $ build1V k (var, v)
    AstTranspose v ->
      build1V k (var, AstTransposeGeneral [1, 0] v)
    AstTransposeGeneral perm v -> AstTransposeGeneral (0 : map succ perm)
                                  $ build1V k (var, v)
    AstFlatten v ->
      build1V k (var, AstReshape (flattenShape $ shapeAst v0) v)
        -- TODO: alternatively we could introduce a subtler operation than
        -- AstReshape that just flattens n levels down; it probably
        -- vectorizes to itself just fine; however AstReshape is too useful
    AstReshape sh v -> AstReshape (k :$ sh) $ build1V k (var, v)
    AstBuildPair1{} -> AstBuildPair1 k (var, v0)
      -- This is a recoverable problem because, e.g., this may be nested
      -- inside projections. So we add to the term and wait for rescue.
      -- It probably speeds up vectorization a tiny bit if we nest
      -- AstBuildPair1 instead of rewriting into AstBuildPair.
    AstGatherPair1 (var2, ix2 :: Index p (AstInt r)) v k2 ->
      AstGatherPair (var ::: var2 ::: Z, AstIntVar var :. ix2)
                    (build1VOccurenceUnknown k (var, v))
                    (k :$ k2 :$ dropShape @p (shapeAst v))
      -- AstScatterPair (var2, ix2) v sh -> ...
      -- no idea how to vectorize AstScatterPair, so let's not add prematurely
    AstGatherPair (vars, ix2) v sh ->
      AstGatherPair (var ::: vars, AstIntVar var :. ix2)
                    (build1VOccurenceUnknown k (var, v))
                    (k :$ sh)

    AstOMap{} -> AstConstant $ AstPrimalPart1 $ AstBuildPair1 k (var, v0)
    -- All other patterns are redundant due to GADT typing.

-- | The application @build1VIxOccurenceUnknown k (var, v, is)@ vectorizes
-- the term @AstBuildPair1 k (var, AstIndexN v is)@, where it's unknown whether
-- @var@ occurs in any of @v@, @is@.
--
-- We try to push indexing down as far as needed to eliminate any occurences
-- of @var@ from @v@ (but not necessarily from @is@), which is enough
-- to replace @AstBuildPair1@ with @AstGatherPair1@ and so complete
-- the vectorization. If @var@ occurs only in the first (outermost)
-- element of @is@, we attempt to simplify the term even more than that.
build1VIxOccurenceUnknown
  :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast (m + n) r, AstIndex m r)
  -> Ast (1 + n) r
build1VIxOccurenceUnknown k (var, v0, ZI) = build1VOccurenceUnknown k (var, v0)
build1VIxOccurenceUnknown k (var, v0, is@(iN :. restN)) =
  if | intVarInAst var v0 -> build1VIx k (var, v0, is)  -- push deeper
     | any (intVarInAstInt var) restN -> AstGatherPair1 (var, is) v0 k
     | intVarInAstInt var iN ->
       let w = AstIndexN v0 restN
       in case build1VIxSimplify k var w iN of
            Just u -> u  -- an extremely simple form found
            Nothing -> AstGatherPair1 (var, is) v0 k
              -- we didn't really need it anyway
     | otherwise -> AstKonst k (AstIndexN v0 is)

-- | The application @build1VIx k (var, v, is)@ vectorizes
-- the term @AstBuildPair1 k (var, AstIndexN v is)@, where it's known that
-- @var@ occurs in @v@. It may or may not additionally occur in @is@.
--
-- We try to push indexing down as far as needed to eliminate any occurences
-- of @var@ from @v@ (but not necessarily from @is@), which is enough
-- to replace @AstBuildPair1@ with @AstGatherPair1@ and so complete
-- the vectorization. We also partially evaluate/simplify the terms,
-- if possible in constant time.
build1VIx
  :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
  => Int -> (AstVarName Int, Ast (m + n) r, AstIndex m r)
  -> Ast (1 + n) r
build1VIx k (var, v0, ZI) = build1V k (var, v0)
build1VIx k (var, v0, is@(_ :. _)) =
  let (rest1, i1) = unsnocIndex1 is  -- TODO: rename to (init1, last1)?
  in case v0 of
    AstVar{} ->
      error "build1VIx: AstVar can't have free int variables"

    AstOp opCode args ->
      AstOp opCode $ map (\v -> build1VIxOccurenceUnknown k (var, v, is)) args

    AstConst{} ->
      error "build1VIx: AstConst can't have free int variables"
    AstConstant{} ->
      AstConstant $ AstPrimalPart1 $ AstBuildPair1 k (var, AstIndexN v0 is)
    AstScale (AstPrimalPart1 r) d ->
      AstScale (AstPrimalPart1 $ AstBuildPair1 k (var, AstIndexN r is))
               (build1VIxOccurenceUnknown k (var, d, is))
    AstCond b v w ->
      build1VIx k (var, AstFromList [v, w], AstIntCond b 0 1 :. is)

    AstConstInt{} ->
      AstConstant $ AstPrimalPart1 $ AstBuildPair1 @n k (var, AstIndexN v0 is)

    AstIndexN v is2 -> build1VIxOccurenceUnknown k (var, v, appendIndex is is2)
    AstSum v ->
      build1V k
        (var, AstSum (AstTranspose $ AstIndexN (AstTranspose v) is))
          -- that's because @index (sum v) i == sum (map (index i) v)@
    AstFromList l | intVarInAstInt var i1 ->
      -- This is pure desperation. I build separately for each list element,
      -- instead of picking the right element for each build iteration
      -- (which to pick depends on the build variable).
      -- @build1VIxSimplify@ is not applicable, because var is in v0.
      -- The only thing to do is constructing a AstGatherPair1 via a trick.
      -- There's no other reduction left to perform and hope the build vanishes.
      let t = AstFromList $ map (\v ->
            build1VOccurenceUnknown k (var, AstIndexN v rest1)) l
      in AstGatherPair1 (var, i1 :. AstIntVar var :. ZI) t k
    AstFromList l ->
      AstIndexN (AstFromList $ map (\v ->
        build1VOccurenceUnknown k (var, AstIndexN v rest1)) l)
                                  (singletonIndex i1)
    AstFromVector l | intVarInAstInt var i1 ->
      let t = AstFromVector $ V.map (\v ->
            build1VOccurenceUnknown k (var, AstIndexN v rest1)) l
      in AstGatherPair1 (var, i1 :. AstIntVar var :. ZI) t k
    AstFromVector l ->
      AstIndexN (AstFromVector $ V.map (\v ->
        build1VOccurenceUnknown k (var, AstIndexN v rest1)) l)
                                  (singletonIndex i1)
    -- Partially evaluate in constant time:
    AstKonst _k v -> build1VIx k (var, v, rest1)
    AstAppend v w ->
      let vlen = AstIntConst $ lengthAst v
          is2 = fmap (\i -> AstIntOp PlusIntOp [i, vlen]) is
      in build1V k (var, AstCond (AstRelInt LsOp [i1, vlen])
                                 (AstIndexN v is)
                                 (AstIndexN w is2))
           -- this is basically partial evaluation, but in constant
           -- time unlike evaluating AstFromList, etc.
    AstSlice i2 _k v ->
      build1VIx k (var, v, fmap (\i ->
        AstIntOp PlusIntOp [i, AstIntConst i2]) is)
    AstReverse v ->
      let revIs = AstIntOp MinusIntOp [AstIntConst (lengthAst v - 1), i1]
                  :. rest1
      in build1VIx k (var, v, revIs)
    AstTranspose v -> case (rest1, shapeAst v) of
      (ZI, ZS) ->
        error "build1VIx: AstTranspose: impossible pattern needlessly required"
      (ZI, _ :$ ZS) -> build1VIx k (var, v, is)
        -- if rank too low, the operation is set to be identity
      (ZI, _) -> AstBuildPair1 k (var, AstIndexN v0 is)  -- we give up see below
      (i2 :. rest2, _) -> build1VIx k (var, v, i2 :. i1 :. rest2)
    AstTransposeGeneral perm v ->
      let lenp = length perm
          is2 = permutePrefixIndex perm is
      in if | valueOf @(m + n) < lenp ->
                build1VIx k (var, v, is)
                  -- the operation is an identity if rank too small
            | valueOf @m < lenp ->
                AstBuildPair1 k (var, AstIndexN v0 is)  -- we give up
                  -- TODO: for this we really need generalized indexes that
                  -- first project, then transpose and so generalized gather;
                  -- or instead push down transpose, but it may be expensive
                  -- or get stuck as well (transpose of a list of lists
                  -- would need to shuffle all the individual elements);
                  -- or perhaps it's enough to pass a permutation
                  -- in build1VIx and wrap the argument
                  -- to gather in AstTransposeGeneral with the permutation
            | otherwise -> build1VIx k (var, v, is2)
    AstFlatten v -> case rest1 of
      ZI ->
        let ixs2 = fromLinearIdx (fmap AstIntConst (shapeAst v)) i1
        in build1VIx k (var, v, ixs2)
      _ -> error "build1VIx: AstFlatten: impossible pattern needlessly required"
    AstReshape{} -> AstBuildPair1 k (var, AstIndexN v0 is)  -- we give up
      {- TODO: This angle of attack fails, because AstSlice with variable
         first argument doesn't vectorize in build1VOccurenceUnknown. For it
         to vectorize, we'd need a new operation, akin to gather,
         with the semantics of build (slice), a gradient, a way to vectorize
         it, in turn, normally and with indexing applied, etc.;
         vectorizing this operation would probably force a generalization
         that acts like gatherN, but produces not a 1-element from the spot
         an index points at, but some fixed k elements and then, unlike gatherN,
         does not flatten the segments, but makes a tensor out of them intact;
         or, if that helps, the operation may just drop a variable
         initial segment of subtensors (of different length in each)
      let i = toLinearIdx2 (fmap AstIntConst sh) is
          -- This converts indexing into a slice and flatten, which in general
          -- is avoided, because it causes costly linearlization, but here
          -- we are going to reshape outside, anyway, and also we are desperate.
          -- BTW, slice has to accept variable first argument precisely
          -- to be usable for convering indexing into. Note that this argument
          -- does not affect shape, so shapes remain static.
          u = AstSlice i (product $ drop (length is) sh) $ AstFlatten v
      in AstReshape (n : sh) $ build1V k (var, u)
      -}
    AstBuildPair1 _n2 (var2, v) ->
      -- Here we seize the chance to recover earlier failed vectorization,
      -- by choosing only one element of this whole build, eliminating it.
      build1VIx k (var, substituteAst i1 var2 v, rest1)
    AstGatherPair1 (var2, ix2) v _n2 ->
      let ix3 = fmap (substituteAstInt i1 var2) ix2
      in build1VIxOccurenceUnknown k (var, v, appendIndex rest1 ix3)
           -- we don't know if var occurs in v; it could have been in ix2
    AstGatherPair (Z, ix2) v _sh ->
      build1VIx k (var, AstIndexN v ix2, is)
    AstGatherPair (var2 ::: vars, ix2) v (_ :$ sh') ->
      let ix3 = fmap (substituteAstInt i1 var2) ix2
      in build1VIx
           k (var, unsafeCoerce $ AstGatherPair (vars, ix3) v sh', rest1)
          -- GHC with the plugin doesn't cope with this
          -- (https://github.com/clash-lang/ghc-typelits-natnormalise/issues/71)
          -- so unsafeCoerce is back
    AstGatherPair{} ->
      error "build1VIx: AstGatherPair: impossible pattern needlessly required"

    AstOMap{} ->
      AstConstant $ AstPrimalPart1 $ AstBuildPair1 k (var, AstIndexN v0 is)
    -- All other patterns are redundant due to GADT typing.

-- TODO: we probably need to simplify iN to some normal form, but possibly
-- this would be even better to do and take advantage of earlier,
-- perhaps even avoiding pushing all the other indexing down
-- | The application @build1VIxSimplify k var v iN@ vectorizes and simplifies
-- the term @AstBuildPair1 k (var, AstIndexN v [iN])@, where it's known that
-- @var@ does not occur in @v@ but occurs in @iN@. This is done by pattern
-- matching on @iN@ as opposed to on @v@.
build1VIxSimplify
  :: forall n r.
     Int -> AstVarName Int -> Ast (1 + n) r -> AstInt r
  -> Maybe (Ast (1 + n) r)
build1VIxSimplify k var v0 iN = case iN of
  AstIntVar var2 | var2 == var ->
    Just $ AstSlice 0 k v0
  AstIntOp PlusIntOp [AstIntVar var2, AstIntConst i2] | var2 == var ->
      Just $ AstSlice i2 k v0
  AstIntOp PlusIntOp [AstIntConst i2, AstIntVar var2] | var2 == var ->
      Just $ AstSlice i2 k v0
  _ -> Nothing
    -- TODO: many more cases; not sure how systematic it can be;
    -- more cases arise if shapes can contain Ast variables;
    -- @Data.Array.Shaped@ doesn't help in these extra cases;
    -- however, AstGatherPair(1) covers all this, at the cost of (relatively
    -- simple) expressions on tape
