{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving,
             StandaloneDeriving, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Term-simplifying combinators corresponding to the Ast constructors.
-- They simplify only on the basis of inspecting the roots of their
-- argument term trees. If the arguments get modified as a result,
-- the modified forms are again inspected and may be simplified.
-- However, no unbounded depth inspection nor simplification of terms
-- takes place. This limited simplification is enough to uncover redexes
-- for the vectorization rules to fire and to undo some of the complication
-- introduced by vectorization. The intention is to leave as much
-- of the original terms provided by the user as possible while making
-- sure everything introduced by vectorization is maximally simplified.
--
-- The combinator can also be used to simplify a whole term, bottom-up.
module HordeAd.Core.AstSimplify
  ( isIdentityPerm, permCycle, permSwapSplit
  , funToAstR, funToAstI, funToAstIndex
  , astReshape
  , astIndexZ, astSum, astFromList, astFromVector, astKonst
  , astAppend, astSlice, astReverse, astTranspose, astFlatten
  , astGather1, astGatherN
  , astIntCond
  , simplifyAst
  , substituteAst, substituteAstInt, substituteAstBool
  , resetVarCOunter
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (replicateM)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.List (elemIndex)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  ( KnownNat
  , OrderingI (..)
  , SomeNat (..)
  , cmpNat
  , sameNat
  , someNatVal
  , type (+)
  , type (-)
  )
import           Numeric.LinearAlgebra (Numeric)
import           System.IO.Unsafe (unsafePerformIO)
import           Unsafe.Coerce (unsafeCoerce)

import HordeAd.Core.Ast
import HordeAd.Core.SizedIndex
import HordeAd.Internal.SizedList

-- * Permutation operations

isIdentityPerm :: Permutation -> Bool
isIdentityPerm = and . zipWith (==) [0 ..]

permCycle :: Int -> Permutation
permCycle 0 = []
permCycle 1 = []
permCycle n = [k `mod` n | k <- [1 .. n]]

-- | Produces a (possibly trival) two-element swap involving the first element
-- and the permutation that needs to be applied first, before the swap,
-- to produce the same result as the original permutation.
-- Addtionally, the latter permutation is represented as operating
-- on all but the first element of a list (the first element is fixed)
-- and so is one element shorter than the original permutation.
permSwapSplit :: Permutation -> Maybe (Int, Permutation)
permSwapSplit = \case
  [] -> Nothing
  perm | isIdentityPerm perm -> Nothing
  i : rest -> case elemIndex 0 rest of
    Nothing -> assert (i == 0) $ Just (0, map (\k -> k - 1) rest)
    Just j -> let f k = if k == 0 then i - 1 else k - 1
              in Just (j, map f rest)


-- * Generating variables names

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 1)

-- Only for tests.
resetVarCOunter :: IO ()
resetVarCOunter = writeIORefU unsafeAstVarCounter 1

unsafeGetFreshAstVar :: IO (AstVarName a)
{-# INLINE unsafeGetFreshAstVar #-}
unsafeGetFreshAstVar = AstVarName <$> atomicAddCounter_ unsafeAstVarCounter 1

funToAstR :: ShapeInt n -> (Ast n r -> Ast m r)
          -> (AstVarName (OR.Array n r), Ast m r)
{-# NOINLINE funToAstR #-}
funToAstR sh f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return (freshAstVar, f (AstVar sh freshAstVar))

funToAstI :: (AstInt r -> t) -> (AstVarName Int, t)
{-# NOINLINE funToAstI #-}
funToAstI f = unsafePerformIO $ do
  freshAstVar <- unsafeGetFreshAstVar
  return (freshAstVar, f (AstIntVar freshAstVar))

funToAstIndex :: forall m p r. KnownNat m
              => (AstIndex m r -> AstIndex p r) -> (AstVarList m, AstIndex p r)
{-# NOINLINE funToAstIndex #-}
funToAstIndex f = unsafePerformIO $ do
  varList <- replicateM (valueOf @m) unsafeGetFreshAstVar
  return (listToSized varList, f (listToIndex $ map AstIntVar varList))


-- * Combinators that simplify but introduce new variable names

-- TODO: decide whether to use always and perhaps remove AstFlatten
-- or not to use for Flatten, but fuse with Flatten, etc.
astReshape :: forall p m r. (KnownNat p, KnownNat m, Show r, Numeric r)
           => ShapeInt m -> Ast p r -> Ast m r
{-# NOINLINE astReshape #-}
astReshape shOut v = unsafePerformIO $ do
  let shIn = shapeAst v
      asGather = do
        varList <- replicateM (lengthShape shOut) unsafeGetFreshAstVar
        let vars :: AstVarList m
            vars = listToSized varList
            ix :: AstIndex m r
            ix = listToIndex $ map AstIntVar varList
            asts :: AstIndex p r
            asts = let i = toLinearIdx @m @0 (fmap AstIntConst shOut) ix
                   in fmap simplifyAstInt
                      $ fromLinearIdx (fmap AstIntConst shIn) i
                        -- we generate these, so we simplify
        return $! astGatherN @m @0 shOut v (vars, asts)
  case sameNat (Proxy @p) (Proxy @m) of
    Just Refl -> if shIn == shOut
                 then return v
                 else asGather
    _ -> asGather

astTranspose :: forall n r. KnownNat n
             => Permutation -> Ast n r -> Ast n r
astTranspose perm t | isIdentityPerm perm = t
astTranspose perm1 (AstTranspose perm2 t) =
  let perm2Matched =
        perm2 ++ take (length perm1 - length perm2) (drop (length perm2) [0 ..])
      perm = permutePrefixList perm1 perm2Matched
  in astTranspose perm t
astTranspose perm u = AstTranspose perm u

-- TODO: perhaps merge with above
astTransposeAsGather :: forall n r. (KnownNat n, Show r, Numeric r)
                     => Permutation -> Ast n r -> Ast n r
{-# NOINLINE astTransposeAsGather #-}
astTransposeAsGather perm v = unsafePerformIO $ do
  let p = length perm
  varList <- replicateM p unsafeGetFreshAstVar
  return $! case someNatVal $ toInteger p of
    Just (SomeNat (_proxy :: Proxy p)) ->
      let vars :: AstVarList p
          vars = listToSized varList
          asts :: AstIndex p r
          asts = listToIndex $ map (\i -> AstIntVar $ varList !! i) perm
      in case cmpNat (Proxy @p) (Proxy @n) of
           EQI -> astGatherN @p @(n - p)
                             (permutePrefixShape perm (shapeAst v)) v
                             (vars, asts)
           LTI -> astGatherN @p @(n - p)
                             (permutePrefixShape perm (shapeAst v)) v
                             (vars, asts)
           _ -> error "astTransposeAsGather: permutation longer than rank"
    Nothing -> error "astTransposeAsGather: impossible someNatVal error"

-- * The simplifying combinators

astIndexZ :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r)
          => Ast (m + n) r -> AstIndex m r -> Ast n r
astIndexZ v0 ZI = v0
astIndexZ v0 ix@(i1 :. (rest1 :: AstIndex m1 r)) = case v0 of
  AstVar{} -> AstIndexZ v0 ix
  AstOp opCode args -> -- AstIndexZ v0 ix
    AstOp opCode (map (`astIndexZ` ix) args)
    -- we can't have a normal form that does not have the capacity
    -- to hide redexes arbitrarily deep inside AstOp,
    -- so we push indexing down AstOp as much as possible; fortunately,
    -- as long as redexes get reduced, this is beneficial;
    -- the worst case is variables in projection or the projected term
    -- preventing reduction and so the projection getting duplicated for nought;
    -- TODO: test often if this is not disastrous
  AstConst{} -> AstIndexZ v0 ix
  AstConstant{} -> AstIndexZ v0 ix
  AstConstInt{} -> AstIndexZ v0 ix
  AstIndexZ v ix2 ->
    astIndexZ v (appendIndex ix2 ix)
  AstSum v ->
    let perm3 = permCycle $ valueOf @m + 1
    in astSum $ astIndexZ (astTranspose perm3 v) ix
  AstFromList l | AstIntConst i <- i1 ->
    astIndexZ (l !! i) rest1
  AstFromList l ->
    AstIndexZ (astFromList $ map (`astIndexZ` rest1) l) (singletonIndex i1)
  AstFromVector l | AstIntConst i <- i1 ->
    astIndexZ (l V.! i) rest1
  AstFromVector l ->
    AstIndexZ (astFromVector $ V.map (`astIndexZ` rest1) l) (singletonIndex i1)
  AstKonst _k v ->
    astIndexZ v rest1
  AstAppend v w ->
    let vlen = AstIntConst $ lengthAst v
        ix2 = simplifyAstInt (AstIntOp MinusIntOp [i1, vlen]) :. rest1
    in astCond (simplifyAstBool $ AstRelInt LsOp [i1, vlen])
               (astIndexZ v ix)
               (astIndexZ w ix2)
  AstSlice i _k v ->
    astIndexZ v (simplifyAstInt (AstIntOp PlusIntOp [i1, AstIntConst i])
                 :. rest1)
  AstReverse v ->
    let revIs = simplifyAstInt (AstIntOp MinusIntOp
                                         [AstIntConst (lengthAst v - 1), i1])
                :. rest1
    in astIndexZ v revIs
  AstTranspose perm v | valueOf @m >= length perm ->
    astIndexZ v (permutePrefixIndex perm ix)
  AstTranspose perm v ->
    astIndexZ (astTransposeAsGather perm v) ix
  AstFlatten v ->
    case rest1 of
      ZI ->
        let ixs2 = fmap simplifyAstInt
                   $ fromLinearIdx (fmap AstIntConst (shapeAst v)) i1
        in astIndexZ v ixs2
      _ ->
        error "astIndexZ: AstFlatten: impossible pattern needlessly required"
  AstReshape sh v ->
    astIndexZ (astReshape sh v) ix
  AstBuild1 _n2 (var2, v) ->  -- only possible tests
    astIndexZ (substituteAst i1 var2 v) rest1
  AstGather1 _n2 v (var2, ix2) ->
    let ix3 = fmap (substituteAstInt i1 var2) ix2
    in astIndexZ v (appendIndex ix3 rest1)
  AstGatherN _sh v (Z, ix2) -> astIndexZ v (appendIndex ix2 ix)
  AstGatherN (_ :$ sh') v (var2 ::: vars, ix2) ->
    let ix3 = fmap (substituteAstInt i1 var2) ix2
        w :: Ast (m1 + n) r
        w = unsafeCoerce $ astGatherN sh' v (vars, ix3)
    in astIndexZ @m1 @n w rest1
  AstGatherN{} ->
    error "astIndexZ: AstGatherN: impossible pattern needlessly required"

astSum :: Ast (1 + n) r -> Ast n r
astSum = AstSum

astFromList :: KnownNat n
            => [Ast n r] -> Ast (1 + n) r
astFromList [a] = astKonst 1 a
astFromList l = AstFromList l

astFromVector :: KnownNat n
              => Data.Vector.Vector (Ast n r) -> Ast (1 + n) r
astFromVector v | V.length v == 1 = astKonst 1 (v V.! 1)
astFromVector l = AstFromVector l

astKonst :: KnownNat n => Int -> Ast n r -> Ast (1 + n) r
astKonst k = \case
  AstTranspose perm v ->
    astTranspose (0 : map succ perm) $ astKonst k v
  AstReshape sh v ->
    AstReshape (k :$ sh) $ astKonst k v
  v -> AstKonst k v

astAppend :: KnownNat n
          => Ast (1 + n) r -> Ast (1 + n) r -> Ast (1 + n) r
astAppend = AstAppend

astSlice :: KnownNat n
         => Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
astSlice = AstSlice

astReverse :: KnownNat n
           => Ast (1 + n) r -> Ast (1 + n) r
astReverse = AstReverse

astFlatten :: KnownNat n
           => Ast n r -> Ast 1 r
astFlatten = AstFlatten

-- Assumption: var does not occur in v0.
astGather1 :: forall p n r. (KnownNat p, KnownNat n, Show r, Numeric r)
           => Int -> Ast (p + n) r -> (AstVarName Int, AstIndex p r)
           -> Ast (1 + n) r
astGather1 k v0 (var, ix) =
  let v3 = astIndexZ v0 ix
  in if intVarInAst var v3
     then case v3 of
       AstIndexZ v2 ix2@(iN :. restN) ->
         if | intVarInAst var v2 ->  -- can this happen?
              AstGather1 k v0 (var, ix)
            | any (intVarInAstInt var) restN ->
              AstGather1 k v2 (var, ix2)
            | intVarInAstInt var iN ->
                let w :: Ast (1 + n) r
                    w = astIndexZ v2 restN
                in case gatherSimplify k var w iN of
                  Just u -> u  -- an extremely simple form found
                  Nothing -> AstGather1 k v2 (var, ix2)
                    -- we didn't really need it anyway
            | otherwise -> astKonst k (AstIndexZ v2 ix2)
       _ -> AstGather1 k v0 (var, ix)  -- can this happen?
     else astKonst k v3

astGatherN :: forall m n p r.
              (KnownNat m, KnownNat p, KnownNat n, Show r, Numeric r)
           => ShapeInt (m + n) -> Ast (p + n) r -> (AstVarList m, AstIndex p r)
           -> Ast (m + n) r
astGatherN _sh v0 (Z, ix) = astIndexZ v0 ix
astGatherN (k :$ sh') v0 (_ ::: vars, ZI) =
  astKonst k (astGatherN sh' v0 (vars, ZI))  -- a shortcut
astGatherN sh@(k :$ sh') v0 (var ::: vars, ix@(_ :. _)) =
  let v3 = astIndexZ @p @n v0 ix
  in if any (flip intVarInAst v3) (var ::: vars)
     then case v3 of
       AstIndexZ v2 ix2 ->
         if | any (flip intVarInAst v2) (var ::: vars) ->  -- can this happen?
              AstGatherN sh v0 (var ::: vars, ix)
            | any (intVarInAstInt var) ix2 ->
              AstGatherN sh v2 (var ::: vars, ix2)
            | otherwise -> astKonst k (astGatherN sh' v2 (vars, ix2))
              -- a generalization of gatherSimplify needed to simplify more
              -- or we could run astGather1 repeatedly, but even then we can't
              -- get into fromList, which may simplify or complicate a term,
              -- and sometimes is not possible without leaving a small
              -- gather outside
       AstGatherN sh2 v2 (vars2, ix2) ->
         if | any (flip intVarInAst v2) (var ::: vars) ->  -- can this happen?
              AstGatherN sh v0 (var ::: vars, ix)
            | otherwise ->
              AstGatherN (appendShape (takeShape @m sh) sh2)
                         v2 (appendSized (var ::: vars) vars2, ix2)
       _ -> AstGatherN sh v0 (var ::: vars, ix)  -- can this happen?
     else astGatherN sh v3 (var ::: vars, ZI)
astGatherN _ _ _ =
  error "astGatherN: AstGatherN: impossible pattern needlessly required"

-- TODO: we probably need to simplify iN to some normal form, but possibly
-- this would be even better to do and take advantage of earlier,
-- perhaps even avoiding pushing all the other indexing down
-- | The application @gatherSimplify k var v iN@ vectorizes and simplifies
-- the term @AstBuild1 k (var, AstIndexZ v [iN])@, where it's known that
-- @var@ does not occur in @v@ but occurs in @iN@. This is done by pattern
-- matching on @iN@ as opposed to on @v@.
gatherSimplify
  :: (KnownNat n, Show r, Numeric r)
  => Int -> AstVarName Int -> Ast (1 + n) r -> AstInt r
  -> Maybe (Ast (1 + n) r)
gatherSimplify k var v0 iN =
  case iN of
    AstIntVar var2 | var2 == var ->
      Just $ astSliceLax 0 k v0
    AstIntOp PlusIntOp [AstIntVar var2, AstIntConst i2]
      | var2 == var ->
        Just $ astSliceLax i2 k v0
    AstIntOp PlusIntOp [AstIntConst i2, AstIntVar var2]
      | var2 == var ->
        Just $ astSliceLax i2 k v0
    _ -> Nothing
      -- TODO: many more cases; not sure how systematic it can be;
      -- more cases arise if shapes can contain Ast variables;
      -- @Data.Array.Shaped@ doesn't help in these extra cases;
      -- however, AstGather* covers all this, at the cost of (relatively
      -- simple) expressions on tape

-- This is to be used only in gatherSimplify. The normal slice
-- still crashes with illegal parameters.
-- This function is so complex in order to guarantee that even though
-- vectorization changes tensor values, it doesn't change their shapes.
astSliceLax :: (KnownNat n, Show r, Numeric r)
            => Int -> Int -> Ast (1 + n) r -> Ast (1 + n) r
astSliceLax i k v =
  let len = lengthAst v
      kMax = len - i
      sh = shapeToList $ shapeAst v
      v2 = AstConst $ OR.constant (k - kMax : tail sh) 0
      !_A = assert (i < len
                    `blame` "astSlice: offset not smaller than tensor length"
                    `swith` (i, len)) ()
  in if | i == 0 && k == len -> v
        | k <= kMax -> AstSlice i k v
        | i == 0 -> AstAppend v v2
        | otherwise -> AstAppend (AstSlice i kMax v) v2

astIntCond :: AstBool r -> AstInt r -> AstInt r -> AstInt r
astIntCond = AstIntCond

astMinIndex1 :: Ast 1 r -> AstInt r
astMinIndex1 = AstMinIndex1

astMaxIndex1 :: Ast 1 r -> AstInt r
astMaxIndex1 = AstMaxIndex1


-- * The simplifying bottom-up pass

-- The constant, primal-part only terms are not vectorized, never
-- introduced by vectorization (let's keep checking it's true)
-- and so don't need to be simplified.
simplifyAstPrimal :: AstPrimalPart n r -> AstPrimalPart n r
simplifyAstPrimal (AstPrimalPart t) = AstPrimalPart t

simplifyAst
  :: (Show r, Numeric r, KnownNat n)
  => Ast n r -> Ast n r
simplifyAst t = case t of
  AstVar{} -> t
  AstOp opCode args -> AstOp opCode (map simplifyAst args)
    -- We do not simplify, e.g., addition or multiplication by zero.
    -- There are too many cases and values are often unknown.
  AstConst{} -> t
  AstConstant a -> AstConstant $ simplifyAstPrimal a
  AstConstInt i -> AstConstInt $ simplifyAstInt i
  AstIndexZ v ix -> astIndexZ (simplifyAst v) (fmap (simplifyAstInt) ix)
  AstSum v -> astSum (simplifyAst v)
  AstFromList l -> astFromList (map (simplifyAst) l)
  AstFromVector l -> astFromVector (V.map (simplifyAst) l)
  AstKonst k v -> astKonst k (simplifyAst v)
  AstAppend x y -> astAppend (simplifyAst x) (simplifyAst y)
  AstSlice i k v -> astSlice i k (simplifyAst v)
  AstReverse v -> astReverse (simplifyAst v)
  AstTranspose perm v -> astTranspose perm $ simplifyAst v
  AstFlatten v -> astFlatten $ simplifyAst v
  AstReshape sh v -> astReshape sh (simplifyAst v)
  AstBuild1 k (var, v) -> AstBuild1 k (var, simplifyAst v)
    -- should never appear outside test runs, but let's test the inside, too
  AstGather1 k v (var, ix) ->
    astGather1 k (simplifyAst v) (var, fmap (simplifyAstInt) ix)
  AstGatherN sh v (vars, ix) ->
    astGatherN sh (simplifyAst v) (vars, fmap (simplifyAstInt) ix)

-- Integer terms need to be simplified, because they are sometimes
-- created by vectorization and can be a deciding factor in whether
-- dual terms can be simplified in turn.
simplifyAstInt :: (Show r, Numeric r)
               => AstInt r -> AstInt r
simplifyAstInt t = case t of
  AstIntVar{} -> t
  AstIntOp opCodeInt args ->
    simplifyAstIntOp opCodeInt (map simplifyAstInt args)
  AstIntConst{} -> t
  AstIntFloor v -> AstIntFloor $ simplifyAst v
    -- Equality of floats is suspect, so no attempt to simplify.
  AstIntCond b a1 a2 -> astIntCond (simplifyAstBool b)
                                   (simplifyAstInt a1)
                                   (simplifyAstInt a2)
  AstMinIndex1 v -> astMinIndex1 $ simplifyAst v
  AstMaxIndex1 v -> astMaxIndex1 $ simplifyAst v

simplifyAstBool :: (Show r, Numeric r)
                => AstBool r -> AstBool r
simplifyAstBool t = case t of
  AstBoolOp opCodeBool args -> AstBoolOp opCodeBool (map simplifyAstBool args)
    -- We do not simplify, e.g., conjunction with False. Worth considering.
  AstBoolConst{} -> t
  AstRel{} -> t
    -- these are primal part expressions, so never vectorized but potentially
    -- large, so we ignore them, even if rarely they could contribute
    -- to simplifying the dual expressions affected by vectorization
    -- in which they are nested; if we ever notice such large expressions
    -- that are actually *introduced* into AstRel by vectorization,
    -- we are going to need to start simplifyign them as well
    -- even just to try to reduce their size
  AstRelInt opCodeRel args -> AstRelInt opCodeRel (map simplifyAstInt args)
    -- We do not simplify, e.g., equality of syntactically equal terms.
    -- There are too many cases and values are often unknown.

-- TODO: let's aim at SOP (Sum-of-Products) form, just as
-- ghc-typelits-natnormalise does. Also, let's associate to the right.
simplifyAstIntOp :: OpCodeInt -> [AstInt r] -> AstInt r
simplifyAstIntOp PlusIntOp [AstIntConst u, AstIntConst v] = AstIntConst $ u + v
simplifyAstIntOp PlusIntOp [ AstIntConst u
                           , AstIntOp PlusIntOp [AstIntConst v, w] ] =
  simplifyAstIntOp PlusIntOp [AstIntConst $ u + v, w]
simplifyAstIntOp PlusIntOp [AstIntConst 0, v] = v
simplifyAstIntOp PlusIntOp [u, AstIntConst 0] = u
simplifyAstIntOp PlusIntOp [AstIntOp PlusIntOp [u, v], w] =
  simplifyAstIntOp PlusIntOp [u, simplifyAstIntOp PlusIntOp [v, w]]
simplifyAstIntOp MinusIntOp [AstIntConst u, AstIntConst v] = AstIntConst $ u - v
simplifyAstIntOp MinusIntOp [AstIntConst 0, v] =
  simplifyAstIntOp NegateIntOp [v]
simplifyAstIntOp MinusIntOp [u, AstIntConst 0] = u
simplifyAstIntOp TimesIntOp [AstIntConst u, AstIntConst v] = AstIntConst $ u * v
simplifyAstIntOp TimesIntOp [ AstIntConst u
                            , AstIntOp TimesIntOp [AstIntConst v, w] ] =
  simplifyAstIntOp TimesIntOp [AstIntConst $ u * v, w]
simplifyAstIntOp TimesIntOp [AstIntConst 0, _v] = AstIntConst 0
simplifyAstIntOp TimesIntOp [_u, AstIntConst 0] = AstIntConst 0
simplifyAstIntOp TimesIntOp [AstIntConst 1, v] = v
simplifyAstIntOp TimesIntOp [u, AstIntConst 1] = u
simplifyAstIntOp TimesIntOp [AstIntOp TimesIntOp [u, v], w] =
  simplifyAstIntOp TimesIntOp [u, simplifyAstIntOp TimesIntOp [v, w]]
simplifyAstIntOp TimesIntOp [AstIntOp PlusIntOp [u, v], w] =
  simplifyAstIntOp PlusIntOp [ simplifyAstIntOp TimesIntOp [u, w]
                             , simplifyAstIntOp TimesIntOp [v, w] ]
simplifyAstIntOp TimesIntOp [u, AstIntOp PlusIntOp [v, w]] =
  simplifyAstIntOp PlusIntOp [ simplifyAstIntOp TimesIntOp [u, v]
                             , simplifyAstIntOp TimesIntOp [u, w] ]
simplifyAstIntOp NegateIntOp [AstIntConst u] = AstIntConst $ negate u
simplifyAstIntOp AbsIntOp [AstIntConst u] = AstIntConst $ abs u
simplifyAstIntOp SignumIntOp [AstIntConst u] = AstIntConst $ signum u
simplifyAstIntOp MaxIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ max u v
simplifyAstIntOp MinIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ min u v
simplifyAstIntOp QuotIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ quot u v
simplifyAstIntOp QuotIntOp [AstIntConst 0, _v] = AstIntConst 0
simplifyAstIntOp QuotIntOp [u, AstIntConst 1] = u
simplifyAstIntOp QuotIntOp [ AstIntOp RemIntOp [_u, AstIntConst v]
                           , AstIntConst v' ]
  | v' >= v && v >= 0 = 0
simplifyAstIntOp QuotIntOp [AstIntOp QuotIntOp [u, v], w] =
  simplifyAstIntOp QuotIntOp [u, simplifyAstIntOp TimesIntOp [v, w]]
simplifyAstIntOp RemIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ rem u v
simplifyAstIntOp RemIntOp [AstIntConst 0, _v] = 0
simplifyAstIntOp RemIntOp [_u, AstIntConst 1] = 0
simplifyAstIntOp RemIntOp [AstIntOp RemIntOp [u, AstIntConst v], AstIntConst v']
  | v' >= v && v >= 0 = AstIntOp RemIntOp [u, AstIntConst v]
simplifyAstIntOp RemIntOp [AstIntOp RemIntOp [u, AstIntConst v], AstIntConst v']
  | rem v v' == 0 && v > 0 = simplifyAstIntOp RemIntOp [u, AstIntConst v']
simplifyAstIntOp DivIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ div u v
simplifyAstIntOp DivIntOp [AstIntConst 0, _v] = AstIntConst 0
simplifyAstIntOp DivIntOp [u, AstIntConst 1] = u
simplifyAstIntOp DivIntOp [ AstIntOp ModIntOp [_u, AstIntConst v]
                          , AstIntConst v' ]
  | v' >= v && v >= 0 = 0
simplifyAstIntOp DivIntOp [AstIntOp QuotIntOp [u, v], w] =
  simplifyAstIntOp DivIntOp [u, simplifyAstIntOp TimesIntOp [v, w]]
simplifyAstIntOp ModIntOp [AstIntConst u, AstIntConst v] =
  AstIntConst $ mod u v
simplifyAstIntOp ModIntOp [AstIntConst 0, _v] = 0
simplifyAstIntOp ModIntOp [_u, AstIntConst 1] = 0
simplifyAstIntOp ModIntOp [AstIntOp ModIntOp [u, AstIntConst v], AstIntConst v']
  | v' >= v && v >= 0 = AstIntOp ModIntOp [u, AstIntConst v]
simplifyAstIntOp ModIntOp [AstIntOp ModIntOp [u, AstIntConst v], AstIntConst v']
  | mod v v' == 0 && v > 0 = simplifyAstIntOp ModIntOp [u, AstIntConst v']
simplifyAstIntOp opCodeInt arg = AstIntOp opCodeInt arg

-- We have to simplify after substitution or simplifying is not idempotent.
substituteAst :: (Show r, Numeric r, KnownNat n)
              => AstInt r -> AstVarName Int -> Ast n r -> Ast n r
substituteAst i var v1 = simplifyAst $ substitute1Ast i var v1

substituteAstInt :: (Show r, Numeric r)
                 => AstInt r -> AstVarName Int -> AstInt r -> AstInt r
substituteAstInt i var i2 = simplifyAstInt $ substitute1AstInt i var i2

substituteAstBool :: (Show r, Numeric r)
                  => AstInt r -> AstVarName Int -> AstBool r -> AstBool r
substituteAstBool i var b1 = simplifyAstBool $ substitute1AstBool i var b1
