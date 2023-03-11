{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -freduction-depth=10000 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Vectorization of the build operation in Ast.
module HordeAd.Core.AstVectorize
  ( traceRuleEnabledRef
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Control.Monad (when)
import           Data.IORef
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+), type (-))
import           Numeric.LinearAlgebra (Numeric, Vector)
import           System.IO (Handle, hFlush, hPutStrLn, stderr, stdout)
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.Internal.SizedList

-- * Ast instances of Tensor (and Primal) that use vectorization

instance ( Numeric r, RealFloat r, RealFloat (Vector r)
         , Show r, Numeric r )  -- needed only to display errors properly
         => Tensor (Ast 0 r) where
  type TensorOf n (Ast 0 r) = Ast n r
  type IntOf (Ast 0 r) = AstInt r

  tshape = shapeAst
  tminIndex0 = AstMinIndex1
  tmaxIndex0 = AstMaxIndex1
  tfloor = AstIntFloor

  tindex = AstIndexZ
  tsum = AstSum
  tfromIndex0 = AstConstant . AstPrimalPart . AstConstInt
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstScatter sh t (funToAstIndex f)  -- introduces new vars

  tfromList = AstFromList
  tfromList0N sh = AstReshape sh . AstFromList
  tfromVector = AstFromVector
  tfromVector0N sh = AstReshape sh . AstFromVector
  tkonst = AstKonst
  tappend = AstAppend
  tslice = AstSlice
  treverse = AstReverse
  ttranspose = AstTranspose
  treshape = AstReshape
  tbuild1 = astBuild1
  tgather sh t f = AstGatherZ sh t (funToAstIndex f)  -- introduces new vars

  tscalar = id  -- Ast confuses the two ranks
  tunScalar = id

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1 :: (KnownNat n, Show r, Numeric r, Num (Vector r))
          => Int -> (AstInt r -> Ast n r) -> Ast (1 + n) r
astBuild1 k f = build1Vectorize k $ funToAstI f

instance ( Numeric r, RealFloat r, RealFloat (Vector r)
         , Show r, Numeric r )
         => Tensor (AstPrimalPart 0 r) where
  type TensorOf n (AstPrimalPart 0 r) = AstPrimalPart n r
  type IntOf (AstPrimalPart 0 r) = AstInt r

  tshape = shapeAst . unAstPrimalPart
  tminIndex0 = AstMinIndex1 . unAstPrimalPart
  tmaxIndex0 = AstMaxIndex1 . unAstPrimalPart
  tfloor = AstIntFloor . unAstPrimalPart

  tindex v ix = AstPrimalPart $ AstIndexZ (unAstPrimalPart v) ix
  tsum = AstPrimalPart . AstSum . unAstPrimalPart
  tfromIndex0 = AstPrimalPart . AstConstInt
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstPrimalPart $ AstScatter sh (unAstPrimalPart t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstPrimalPart . AstFromList . map unAstPrimalPart
  tfromList0N sh =
    AstPrimalPart . AstReshape sh . AstFromList . map unAstPrimalPart
  tfromVector = AstPrimalPart . AstFromVector . V.map unAstPrimalPart
  tfromVector0N sh =
    AstPrimalPart . AstReshape sh . AstFromVector . V.map unAstPrimalPart
  tkonst k = AstPrimalPart . AstKonst k . unAstPrimalPart
  tappend u v =
    AstPrimalPart $ AstAppend (unAstPrimalPart u) (unAstPrimalPart v)
  tslice i k = AstPrimalPart . AstSlice i k  . unAstPrimalPart
  treverse = AstPrimalPart . AstReverse . unAstPrimalPart
  ttranspose perm = AstPrimalPart . AstTranspose perm . unAstPrimalPart
  treshape sh = AstPrimalPart . AstReshape sh  . unAstPrimalPart
  tbuild1 k f = AstPrimalPart $ AstBuild1 k
                $ funToAstI  -- this introduces new variable names
                $ unAstPrimalPart . f
                -- TODO: $ AstConstant . f
                -- that's the correct one, but unvectorized tests fail with it
  tgather sh t f = AstPrimalPart $ AstGatherZ sh (unAstPrimalPart t)
                   $ funToAstIndex f  -- this introduces new variable names

  tscalar = id
  tunScalar = id

instance HasPrimal (Ast 0 r) where
  type ScalarOf (Ast 0 r) = r
  type Primal (Ast 0 r) = AstPrimalPart 0 r
  type DualOf n (Ast 0 r) = ()  -- TODO: data AstDualPart: dScale, dAdd, dkonst1
  tconst = AstConstant . AstPrimalPart . AstConst
  tconstant = AstConstant
  tprimalPart = AstPrimalPart
  tdualPart = error "TODO"
  tD = error "TODO"
  type DynamicTensor (Ast 0 r) = AstDynamic r
  tdummyD = AstDynamicDummy
  tisDummyD t = case t of
    AstDynamicDummy -> True
    _ -> False
  taddD = AstDynamicPlus
  tfromR = AstDynamicFrom
  tfromD = AstFromDynamic

instance HasPrimal (AstPrimalPart 0 r) where
  type ScalarOf (AstPrimalPart 0 r) = r
  type Primal (AstPrimalPart 0 r) = AstPrimalPart 0 r
  type DualOf n (AstPrimalPart 0 r) = ()
  tconst = AstPrimalPart . AstConst
  tconstant = AstPrimalPart . AstConstant
  tprimalPart = id
  tdualPart = error "TODO"
  tD = error "TODO"
  -- TODO: if ever used, define, if not, use an Error type
  type DynamicTensor (AstPrimalPart 0 r) = Maybe r
  tdummyD = undefined
  tisDummyD = undefined
  taddD = undefined
  tfromR = undefined
  tfromD = undefined


-- * Vectorization

-- TODO: due to 2 missing cases, it still sometimes fails, that is, produces
-- the main @AstBuild1@, perhaps in many copies nested in other terms.
-- But there is hope it can always succeed for terms that shaped tensors
-- would type-check (ranked tensors are not fussy enough).
-- | The application @build1Vectorize k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, that is, rewrites it to a term
-- with the same value, but not containing the outermost @AstBuild1@
-- constructor and not increasing (and potentially decreasing)
-- the total number of @AstBuild1@ occuring in the term.
build1Vectorize
  :: (KnownNat n, Show r, Numeric r, Num (Vector r))
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1Vectorize k (var, v0) = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = 1000 * traceWidth
      startTerm = AstBuild1 k (var, v0)
  when enabled $ do
    writeIORef traceNestingLevel 0
    hPutStrLnFlush stderr $
      "\n"
      ++ "START of vectorization for term "
      ++ ellipsisString width (show startTerm)
      ++ "\n"
  let !endTerm = build1VOccurenceUnknown k (var, v0)
  when enabled $ do
    hPutStrLnFlush stderr $
      "\n"
      ++ "END of vectorization yields "
      ++ ellipsisString width (show endTerm)
      ++ "\n"
  let !_A = assert (shapeAst startTerm == shapeAst endTerm
                   `blame` "build1Vectorize: term shape changed"
                   `swith`(shapeAst startTerm, shapeAst endTerm)) ()
  return endTerm

-- This abbreviation is used a lot below.
astTr :: forall n r. Ast (2 + n) r -> Ast (2 + n) r
astTr = AstTranspose [1, 0]

-- | The application @build1VOccurenceUnknown k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's unknown whether
-- @var@ occurs in @v@.
build1VOccurenceUnknown
  :: (KnownNat n, Show r, Numeric r, Num (Vector r))
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1VOccurenceUnknown k (var, v0) =
  let traceRule = mkTraceRule "build1VOcc" (AstBuild1 k (var, v0)) v0 1
  in if intVarInAst var v0
     then build1V k (var, v0)
     else traceRule $
       astKonst k v0

-- | The application @build1V k (var, v)@ vectorizes
-- the term @AstBuild1 k (var, v)@, where it's known that
-- @var@ occurs in @v@.
build1V
  :: (KnownNat n, Show r, Numeric r, Num (Vector r))
  => Int -> (AstVarName Int, Ast n r) -> Ast (1 + n) r
build1V k (var, v00) =
  let v0 = simplifyStepNonIndex v00
      bv = AstBuild1 k (var, v0)
      traceRule = mkTraceRule "build1V" bv v0 1
  -- Almost surely the term will be transformed, so it can just as well
  -- we one-step simplified first (many steps if guaranteed net beneficial).
  in case v0 of
    AstVar{} ->
      error "build1V: AstVar can't have free int variables"

    AstOp opCode args -> traceRule $
      AstOp opCode $ map (\v -> build1VOccurenceUnknown k (var, v)) args

    AstConst{} ->
      error "build1V: AstConst can't have free int variables"
    AstConstant{} -> traceRule $
      AstConstant $ AstPrimalPart bv
      -- This is very fast when interpreted in a smart way, but constant
      -- character needs to be exposed for nested cases.
      -- We don't vectorize under AstConstant, because vectorizing AstConstInt
      -- is laborious. The bad consequence is that the AstBuild1 terms
      -- prevent fusion of the terms they contain with the terms outside.
      -- Fortunately this can't gridlock occurences of integer variables,
      -- because they are all bound by AstBuild1 terms either inside
      -- AstConstant, in which case the enclosing AstBuild1 prevents
      -- the variable from being free in the non-constant term,
      -- or outside, in which case vectorization makes sure to eliminate
      -- the variable or bind it with AstGatherZ. The latter case is
      -- why we have to enter AstConstant during vectorization
      -- and simplify enough to reach the integer variables.

    AstIndexZ v is -> traceRule $
      build1VIndex k (var, v, is)
      -- @var@ is in @v@ or @is@; TODO: simplify is first or even fully
      -- evaluate (may involve huge data processing) if contains no vars
      -- and then some things simplify a lot, e.g., if constant index,
      -- we may just pick the right element of a AstFromList
    AstSum v -> traceRule $
      astSum $ astTr $ build1V k (var, v)
    AstConstInt{} -> traceRule
      bv  -- vectorizing this would require mapping all AstInt operations
          -- to Ast operations, including RemIntOp, AstIntCond, etc.,
          -- so this is a big effort for a minor feature and handling recursive
          -- cases like AstMinIndex1, where integer variables can appear
          -- inside Ast term, may even be impossible in the current system
    AstScatter sh v (vars, ix) -> traceRule $
      astScatter (k :$ sh)
                 (build1VOccurenceUnknown k (var, v))
                 (var ::: vars, AstIntVar var :. ix)
        -- note that this is only the easier half of vectorization of scatter;
        -- the harder half requires simplification and probably a new
        -- normal form

    AstFromList l -> traceRule $
      astTr $ astFromList (map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstFromVector l -> traceRule $
      astTr $ astFromVector (V.map (\v -> build1VOccurenceUnknown k (var, v)) l)
    AstKonst s v -> traceRule $
      astTr $ astKonst s $ build1V k (var, v)
    AstAppend v w -> traceRule $
      astTr $ astAppend (astTr $ build1VOccurenceUnknown k (var, v))
                        (astTr $ build1VOccurenceUnknown k (var, w))
    AstSlice i s v -> traceRule $
      astTr $ astSlice i s $ astTr $ build1V k (var, v)
    AstReverse v -> traceRule $
      astTr $ astReverse $ astTr $ build1V k (var, v)
      -- that's because @build1 k (f . g) == map1 f (build1 k g)@
      -- and @map1 f == transpose . f . transpose@
      -- TODO: though only for some f; check and fail early;
      -- probably only f that don't change shapes or ranks at least
    AstTranspose perm v -> traceRule $
      astTranspose (simplifyPermutation $ 0 : map succ perm)
                   (build1V k (var, v))
    AstReshape sh v -> traceRule $
      astReshape (k :$ sh) $ build1V k (var, v)
    AstBuild1{} -> error "build1V: impossible case of AstBuild1"
    AstGatherZ sh v (vars, ix) -> traceRule $
      astGatherStep (k :$ sh)
                    (build1VOccurenceUnknown k (var, v))
                    (var ::: vars, AstIntVar var :. ix)
    AstFromDynamic{} -> error "build1V: AstFromDynamic is not for library users"

-- | The application @build1VIndex k (var, v, ix)@ vectorizes
-- the term @AstBuild1 k (var, AstIndexZ v ix)@, where it's unknown whether
-- @var@ occurs in any of @v@, @ix@.
--
-- We try to push indexing down as far as needed to eliminate any occurences
-- of @var@ from @v@ (but not necessarily from @ix@), which is enough
-- to replace @AstBuild1@ with @AstGatherZ@ and so complete
-- the vectorization. If @var@ occurs only in the first (outermost)
-- element of @ix@, we attempt to simplify the term even more than that.
--
-- This pushing down is performed by alternating steps of simplification,
-- in @astIndexStep@, that eliminated indexing from the top of a term
-- position (except two permissible normal forms) and vectorization,
-- @build1VOccurenceUnknown@, that recursively goes down under constructors
-- until it encounter indexing again.
-- We have to do this in lockstep so that we simplify terms only as much
-- as needed to vectorize.
build1VIndex
  :: forall m n r. (KnownNat m, KnownNat n, Show r, Numeric r, Num (Vector r))
  => Int -> (AstVarName Int, Ast (m + n) r, AstIndex m r)
  -> Ast (1 + n) r
build1VIndex k (var, v0, ZI) = build1VOccurenceUnknown k (var, v0)
build1VIndex k (var, v0, ix@(_ :. _)) =
  let traceRule = mkTraceRule "build1VIndex"
                              (AstBuild1 k (var, AstIndexZ v0 ix))
                              v0 1
  in if intVarInAst var v0
     then case astIndexStep v0 ix of  -- push deeper
       AstIndexZ v1 (i1 :. ZI) | intVarInAst var v1 -> traceRule $
         build1VIndexNormalForm k (var, v1, i1)
       v -> traceRule $
         build1VOccurenceUnknown k (var, v)  -- peel off yet another constructor
     else traceRule $
            astGatherStep (k :$ dropShape (shapeAst v0)) v0 (var ::: Z, ix)

-- I analyze here all the possible normal forms with indexing on top
-- in the hard case where the build variable appears in v1
-- (in the easy case they are covered by general rules).
build1VIndexNormalForm
  :: forall n r. (KnownNat n, Show r, Numeric r, Num (Vector r))
  => Int -> (AstVarName Int, Ast n r, AstInt r)  -- n + 1 breaks plugins
  -> Ast n r
build1VIndexNormalForm k (var, v1, i1) = case v1 of
  AstFromList l ->
    if intVarInAstInt var i1
    then -- This is pure desperation. I build separately for each list element,
         -- instead of picking the right element for each build iteration
         -- (which to pick depends on the build variable).
         -- There's no other reduction left to perform and hope the build
         -- vanishes. The astGatherStep is applicable via a trick based
         -- on making the variable not occur freely in its argument term
         -- by binding the variable in nested gathers (or by reducing it away).
         -- By the inductive invariant, this succeeds.
         let f :: Ast (n - 1) r -> Ast n r
             f v = build1VOccurenceUnknown k (var, v)
             t :: Ast (1 + n) r
             t = astFromList $ map f l
         in astGatherStep (k :$ dropShape (shapeAst t)) t
                          (var ::: Z, i1 :. AstIntVar var :. ZI)
    else
      AstIndexZ (astFromList $ map (\v ->
        build1VOccurenceUnknown k (var, v)) l) (singletonIndex i1)
  AstFromVector l ->
    if intVarInAstInt var i1
    then let f :: Ast (n - 1) r -> Ast n r
             f v = build1VOccurenceUnknown k (var, v)
             t :: Ast (1 + n) r
             t = astFromVector $ V.map f l
         in astGatherStep (k :$ dropShape (shapeAst t)) t
                          (var ::: Z, i1 :. AstIntVar var :. ZI)
    else
      AstIndexZ (astFromVector $ V.map (\v ->
        build1VOccurenceUnknown k (var, v)) l) (singletonIndex i1)
  _ -> error $ "build1VIndexNormalForm: not a normal form"
               ++ show (k, var, v1, i1)


-- * Rule tracing machinery

-- TODO: set from the testing commandline, just as eqEpsilonRef in EqEpsilon.hs
traceRuleEnabledRef :: IORef Bool
{-# NOINLINE traceRuleEnabledRef #-}
traceRuleEnabledRef = unsafePerformIO $ newIORef False

traceNestingLevel :: IORef Int
{-# NOINLINE traceNestingLevel #-}
traceNestingLevel = unsafePerformIO $ newIORef 0

traceWidth :: Int
traceWidth = 80

padString :: Int -> String -> String
padString width full = let cropped = take width full
                       in if length full <= width
                          then take width $ cropped ++ repeat ' '
                          else take (width - 3) cropped ++ "..."

ellipsisString :: Int -> String -> String
ellipsisString width full = let cropped = take width full
                            in if length full <= width
                               then cropped
                               else take (width - 3) cropped ++ "..."

mkTraceRule :: (KnownNat n, Show r, Numeric r, Show ca)
            => String -> Ast n r -> ca -> Int -> Ast n r -> Ast n r
mkTraceRule prefix from caseAnalysed nwords to = unsafePerformIO $ do
  enabled <- readIORef traceRuleEnabledRef
  let width = traceWidth
      constructorName =
        unwords $ take nwords $ words $ take 20 $ show caseAnalysed
      ruleName = prefix ++ "." ++ constructorName
      ruleNamePadded = take 20 $ ruleName ++ repeat ' '
  when enabled $ do
    nestingLevel <- readIORef traceNestingLevel
    modifyIORef' traceNestingLevel succ
    let paddedNesting = take 3 $ show nestingLevel ++ repeat ' '
    -- Force in the correct order:
    let !stringFrom = show from
    let !stringTo = show to
    hPutStrLnFlush stderr $ paddedNesting ++ "rule " ++ ruleNamePadded
                            ++ " sends " ++ padString width stringFrom
                            ++ " to " ++ padString width stringTo
    let !_A = assert (shapeAst from == shapeAst to
                     `blame` "mkTraceRule: term shape changed"
                     `swith`(shapeAst from, shapeAst to, from, to)) ()
    modifyIORef' traceNestingLevel pred
  return $! to

hPutStrLnFlush :: Handle -> String -> IO ()
hPutStrLnFlush target s = do
  hFlush stdout >> hFlush stderr
  hPutStrLn target s
  hFlush stdout >> hFlush stderr
