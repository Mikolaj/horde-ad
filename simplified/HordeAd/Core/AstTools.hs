{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | An assortment of operations on AST of the code to be differentiated.
module HordeAd.Core.AstTools
  ( shapeAst, lengthAst
  , intVarInAst, intVarInAstInt, intVarInAstBool, intVarInIndex
  , substitute1Ast, substitute1AstDomains, substitute1AstInt, substitute1AstBool
  , astIsSmall
  , printAstVarName
  , printAstSimple, printAstPretty, printAstDomainsSimple, printAstDomainsPretty
  , printGradient6Simple, printGradient6Pretty
  , printPrimal6Simple, printPrimal6Pretty
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import           Data.Either (fromLeft, fromRight)
import           Data.List (intersperse)
import           Data.Proxy (Proxy (Proxy))
import           Data.Strict.IntMap (IntMap)
import qualified Data.Strict.IntMap as IM
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))

import HordeAd.Core.Ast
import HordeAd.Core.SizedIndex
import HordeAd.Core.SizedList

-- * Shape calculation

-- This is cheap and dirty. We don't shape-check the terms and we don't
-- unify or produce (partial) results with variables. Instead, we investigate
-- only one path and fail if it doesn't contain enough information
-- to determine shape. If we don't switch to @Data.Array.Shaped@
-- or revert to fully dynamic shapes, we need to redo this with more rigour.
shapeAst :: forall n r. (KnownNat n, ShowAst r)
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
  AstIndexZ v (_is :: Index m (AstInt r)) -> dropShape @m (shapeAst v)
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
  AstSlice _n k v -> k :$ tailShape (shapeAst v)
  AstReverse v -> shapeAst v
  AstTranspose perm v -> backpermutePrefixShape perm (shapeAst v)
  AstReshape sh _v -> sh
  AstBuild1 k (_var, v) -> k :$ shapeAst v
  AstGatherZ sh _v (_vars, _ix) -> sh
  AstConst a -> listShapeToShape $ OR.shapeL a
  AstConstant (AstPrimalPart a) -> shapeAst a
  AstD (AstPrimalPart u) _ -> shapeAst u
  AstLetDomains _ _ v -> shapeAst v

-- Length of the outermost dimension.
lengthAst :: (KnownNat n, ShowAst r) => AstRanked r (1 + n) -> Int
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
  AstIndexZ v ix -> intVarInAst var v || intVarInIndex var ix
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
  AstGatherZ _ v (_vars, ix) -> intVarInIndex var ix || intVarInAst var v
  AstConst{} -> False
  AstConstant (AstPrimalPart v) -> intVarInAst var v
  AstD (AstPrimalPart u) (AstDualPart u') ->
    intVarInAst var u || intVarInAst var u'
  AstLetDomains _vars l v -> intVarInAstDomains var l || intVarInAst var v

intVarInAstDomains :: AstVarId -> AstDomains r -> Bool
intVarInAstDomains var = \case
  AstDomains l -> any (\(AstDynamic t) -> intVarInAst var t) l
  AstDomainsLet _var2 u v -> intVarInAst var u || intVarInAstDomains var v

intVarInAstInt :: AstVarId -> AstInt r -> Bool
intVarInAstInt var = \case
  AstIntVar var2 -> var == var2  -- the only int variable not in binder position
  AstIntOp _ l -> any (intVarInAstInt var) l
  AstIntConst{} -> False
  AstIntFloor (AstPrimalPart v) -> intVarInAst var v
  AstIntCond b x y ->
    intVarInAstBool var b || intVarInAstInt var x || intVarInAstInt var y
  AstMinIndex1 (AstPrimalPart v) -> intVarInAst var v
  AstMaxIndex1 (AstPrimalPart v) -> intVarInAst var v

intVarInAstBool :: AstVarId -> AstBool r -> Bool
intVarInAstBool var = \case
  AstBoolOp _ l -> any (intVarInAstBool var) l
  AstBoolConst{} -> False
  AstRel _ l -> any (intVarInAst var . unAstPrimalPart) l
  AstRelInt _ l  -> any (intVarInAstInt var) l

intVarInIndex :: AstVarId -> AstIndex n r -> Bool
intVarInIndex var = any (intVarInAstInt var)


-- * Substitution

-- We assume no variable is shared between a binding and its nested binding
-- and nobody substitutes into variables that are bound.
-- This keeps the substitution code simple, because we never need to compare
-- variables to any variable in the bindings.
--
-- The Either is a hack until we merge Ast and AstInt.
substitute1Ast :: forall m n r. (ShowAst r, KnownNat m, KnownNat n)
               => Either (AstRanked r m) (AstInt r) -> AstVarId -> AstRanked r n
               -> AstRanked r n
substitute1Ast i var v1 = case v1 of
  AstVar sh var2 ->
    if var == var2
    then case sameNat (Proxy @m) (Proxy @n) of
      Just Refl -> let t = fromLeft (error "substitute1Ast: Var") i
                   in assert (shapeAst t == sh) t
      _ -> error "substitute1Ast: n"
    else v1
  AstLet var2 u v ->
    AstLet var2 (substitute1Ast i var u) (substitute1Ast i var v)
  AstLetADShare{} -> error "substitute1Ast: AstLetADShare"
  AstOp opCode args -> AstOp opCode $ map (substitute1Ast i var) args
  AstSumOfList args -> AstSumOfList $ map (substitute1Ast i var) args
  AstIota -> v1
  AstIndexZ v is ->
    AstIndexZ (substitute1Ast i var v) (fmap (substitute1AstInt i var) is)
  AstSum v -> AstSum (substitute1Ast i var v)
  AstScatter sh v (vars, ix) ->
    AstScatter sh (substitute1Ast i var v)
                  (vars, fmap (substitute1AstInt i var) ix)
  AstFromList l -> AstFromList $ map (substitute1Ast i var) l
  AstFromVector l -> AstFromVector $ V.map (substitute1Ast i var) l
  AstReplicate s v -> AstReplicate s (substitute1Ast i var v)
  AstAppend x y -> AstAppend (substitute1Ast i var x) (substitute1Ast i var y)
  AstSlice k s v -> AstSlice k s (substitute1Ast i var v)
  AstReverse v -> AstReverse (substitute1Ast i var v)
  AstTranspose perm v -> AstTranspose perm (substitute1Ast i var v)
  AstReshape sh v -> AstReshape sh (substitute1Ast i var v)
  AstBuild1 k (var2, v) -> AstBuild1 k (var2, substitute1Ast i var v)
  AstGatherZ sh v (vars, ix) ->
    AstGatherZ sh (substitute1Ast i var v)
                  (vars, fmap (substitute1AstInt i var) ix)
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
  :: (ShowAst r, KnownNat m)
  => Either (AstRanked r m) (AstInt r) -> AstVarId -> AstDynamic r
  -> AstDynamic r
substitute1AstDynamic i var (AstDynamic t) = AstDynamic $ substitute1Ast i var t

substitute1AstDomains
  :: (ShowAst r, KnownNat m)
  => Either (AstRanked r m) (AstInt r) -> AstVarId -> AstDomains r
  -> AstDomains r
substitute1AstDomains i var v1 = case v1 of
  AstDomains l -> AstDomains $ V.map (substitute1AstDynamic i var) l
  AstDomainsLet var2 u v ->
    AstDomainsLet var2 (substitute1Ast i var u)
                       (substitute1AstDomains i var v)

substitute1AstInt :: forall m r. (ShowAst r, KnownNat m)
                  => Either (AstRanked r m) (AstInt r) -> AstVarId -> AstInt r
                  -> AstInt r
substitute1AstInt i var i2 = case i2 of
  AstIntVar var2 -> if var == var2
                    then fromRight (error "substitute1AstInt: Var") i
                    else i2
  AstIntOp opCodeInt args ->
    AstIntOp opCodeInt $ map (substitute1AstInt i var) args
  AstIntConst _a -> i2
  AstIntFloor (AstPrimalPart v) ->
    AstIntFloor $ AstPrimalPart $ substitute1Ast i var v
  AstIntCond b a1 a2 ->
    AstIntCond (substitute1AstBool i var b)
               (substitute1AstInt i var a1) (substitute1AstInt i var a2)
  AstMinIndex1 (AstPrimalPart v) ->
    AstMinIndex1 $ AstPrimalPart $ substitute1Ast i var v
  AstMaxIndex1 (AstPrimalPart v) ->
    AstMaxIndex1 $ AstPrimalPart $ substitute1Ast i var v

substitute1AstBool :: forall m r. (ShowAst r, KnownNat m)
                   => Either (AstRanked r m) (AstInt r) -> AstVarId -> AstBool r
                   -> AstBool r
substitute1AstBool i var b1 = case b1 of
  AstBoolOp opCodeBool args ->
    AstBoolOp opCodeBool $ map (substitute1AstBool i var) args
  AstBoolConst _a -> b1
  AstRel opCodeRel args ->
    AstRel opCodeRel
    $ map (AstPrimalPart . substitute1Ast i var . unAstPrimalPart) args
  AstRelInt opCodeRel args ->
    AstRelInt opCodeRel $ map (substitute1AstInt i var) args


-- * Determining if a term is too small to require sharing

astIsSmall :: forall n r. KnownNat n
           => AstRanked r n -> Bool
astIsSmall = \case
  AstVar{} -> True
  AstIota -> True
  AstIndexZ AstIota _ -> True
  AstConst{} -> valueOf @n == (0 :: Int)
  AstConstant (AstPrimalPart v) -> astIsSmall v
  AstReplicate _ v -> astIsSmall v  -- materialized via tricks, so prob. safe
  AstSlice _ _ v -> astIsSmall v  -- materialized via tensor/vector slice; cheap
  AstTranspose _ v -> astIsSmall v  -- often cheap and often fuses
  _ -> False


-- * Pretty-printing

-- Modeled after https://github.com/VMatthijs/CHAD/blob/755fc47e1f8d1c3d91455f123338f44a353fc265/src/TargetLanguage.hs#L335.

data PrintConfig = PrintConfig
  { prettifyLosingSharing :: Bool
  , varRenames            :: IntMap String
  }

printAstVarId :: String -> PrintConfig -> AstVarId -> ShowS
printAstVarId prefix cfg var =
  let n = fromEnum var - 100000000
  in showString $ case IM.lookup n (varRenames cfg) of
    Just name | name /= "" -> name
    _ -> prefix ++ show n

printAstVar :: forall n r. KnownNat n
            => PrintConfig -> AstVarName (OR.Array n r) -> ShowS
printAstVar cfg (AstVarName var) =
  let rank = valueOf @n
      prefix = case rank :: Int of
        0 -> "x"
        1 -> "v"
        2 -> "m"
        3 -> "t"
        4 -> "u"
        5 -> "v"
        _ -> "w"
  in printAstVarId prefix cfg var

printAstIntVar :: PrintConfig -> AstVarId -> ShowS
printAstIntVar = printAstVarId "i"

defaulPrintConfig :: Bool -> IntMap String -> PrintConfig
defaulPrintConfig prettifyLosingSharing renames =
  let varRenames = renames `IM.union` IM.fromList [(1, "dret")]
  in PrintConfig {..}

-- Precedences used are as in Haskell.
printAst :: forall n r. (ShowAst r, KnownNat n)
         => PrintConfig -> Int -> AstRanked r n -> ShowS
printAst cfg d = \case
  AstVar _sh var -> printAstVar cfg (AstVarName @(OR.Array n r) var)
  t@(AstLet @_ @m0 var0 u0 v0) ->
    if prettifyLosingSharing cfg
    then let collect :: AstRanked r n -> ([(ShowS, ShowS)], ShowS)
             collect (AstLet @_ @m var u v) =
               let name = printAstVar cfg (AstVarName @(OR.Array m r) var)
                   uPP = printAst cfg 0 u
                   (rest, corePP) = collect v
               in ((name, uPP) : rest, corePP)
             collect v = ([], printAst cfg 0 v)
             (pairs, core) = collect t
         in showParen (d > 0)
            $ showString "let "
              . foldr (.) id (intersperse (showString " ; ")
                  [name . showString " = " . uPP | (name, uPP) <- pairs])
              . showString " in "
              . core
    else
      showParen (d > 10)
      $ showString "tlet "
        . printAst cfg 11 u0
        . showString " "
        . (showParen True
           $ showString "\\"
             . printAstVar cfg (AstVarName @(OR.Array m0 r) var0)
             . showString " -> "
             . printAst cfg 0 v0)
  AstLetADShare l v -> printAst cfg d $ bindsToLet v (assocsADShare l)
  AstOp opCode args -> printAstOp cfg d opCode args
  AstSumOfList [] -> error "printAst: empty AstSumOfList"
  AstSumOfList (left : args) ->
    let rs = map (\arg -> showString " + " . printAst cfg 7 arg) args
    in showParen (d > 6)
       $ printAst cfg 7 left
         . foldr (.) id rs
  AstIota -> showString "tiota"  -- TODO: no surface syntax, so no roundtrip
  AstIndexZ AstIota (i :. ZI) ->
    printPrefixOp printAstInt cfg d "tfromIndex0" [i]
  AstIndexZ v ix ->
    showParen (d > 9)
    $ printAst cfg 10 v
      . showString " ! "
      . showListWith (printAstInt cfg 0) (indexToList ix)
  AstSum v -> printPrefixOp printAst cfg d "tsum" [v]
  AstScatter sh v (vars, ix) ->
    showParen (d > 10)
    $ showString ("tscatter " ++ show sh ++ " ")
      . printAst cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (sizedListToList vars)
           . showString " -> "
           . showListWith (printAstInt cfg 0) (indexToList ix))
  AstFromList l ->
    showParen (d > 10)
    $ showString "tfromList "
      . showListWith (printAst cfg 0) l
  AstFromVector l ->
    showParen (d > 10)
    $ showString "tfromVector "
      . (showParen True
         $ showString "fromList "
           . showListWith (printAst cfg 0) (V.toList l))
  AstReplicate k v -> printPrefixOp printAst cfg d ("treplicate " ++ show k) [v]
  AstAppend x y -> printPrefixOp printAst cfg d "tappend" [x, y]
  AstSlice i k v -> printPrefixOp printAst cfg d
                                  ("tslice " ++ show i ++ " " ++ show k) [v]
  AstReverse v -> printPrefixOp printAst cfg d "treverse" [v]
  AstTranspose perm v ->
    printPrefixOp printAst cfg d ("ttranspose " ++ show perm) [v]
  AstReshape sh v ->
    printPrefixOp printAst cfg d ("treshape " ++ show sh) [v]
  AstBuild1 @m k (var, v) ->
    showParen (d > 10)
    $ showString "tbuild1 "
      . shows k
      . showString " "
      . (showParen True
         $ showString "\\"
           . printAstIntVar cfg var
           . showString " -> "
           . printAst cfg 0 v)
  AstGatherZ sh v (vars, ix) ->
    showParen (d > 10)
    $ showString ("tgather " ++ show sh ++ " ")
      . printAst cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (sizedListToList vars)
           . showString " -> "
           . showListWith (printAstInt cfg 0) (indexToList ix))
  AstConst a ->
    showParen (d > 10)
    $ showString "tconst "
      . if null (OR.shapeL a)
        then shows $ head $ OR.toList a
        else showParen True
             $ shows a
  AstConstant (AstPrimalPart (AstConst a)) -> printAst cfg d (AstConst a)
  AstConstant (AstPrimalPart (AstIndexZ AstIota (i :. ZI))) ->
    printAst cfg d (AstIndexZ AstIota (i :. ZI))
  AstConstant (AstPrimalPart a) ->
    printPrefixOp printAst cfg d "tconstant" [a]
  AstD (AstPrimalPart u) (AstDualPart u') ->
    printPrefixOp printAst cfg d "tD" [u, u']
  AstLetDomains vars l v ->
    showParen (d > 10)
    $ showString "rletDomainsOf "
      . printAstDomains cfg 11 l
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstVarFromDomains cfg)
                          (V.toList $ V.zip vars (unwrapAstDomains l))
           . showString " -> "
           . printAst cfg 0 v)
      -- TODO: this does not roundtrip yet

printAstVarFromDomains :: forall r. PrintConfig -> (AstVarId, AstDynamic r)
                       -> ShowS
printAstVarFromDomains cfg (var, AstDynamic @n _) =
  printAstVar cfg (AstVarName @(OR.Array n r) var)

-- Differs from standard only in the space after comma.
showListWith :: (a -> ShowS) -> [a] -> ShowS
showListWith = showCollectionWith "[" "]"

showCollectionWith :: String -> String -> (a -> ShowS) -> [a] -> ShowS
showCollectionWith start end _     []     s = start ++ end ++ s
showCollectionWith start end showx (x:xs) s = start ++ showx x (showl xs)
 where
  showl []     = end ++ s
  showl (y:ys) = ", " ++ showx y (showl ys)

printAstDynamic :: ShowAst r => PrintConfig -> Int -> AstDynamic r -> ShowS
printAstDynamic cfg d (AstDynamic v) =
  printPrefixOp printAst cfg d "dfromR" [v]

printAstUnDynamic :: ShowAst r => PrintConfig -> Int -> AstDynamic r -> ShowS
printAstUnDynamic cfg d (AstDynamic v) = printAst cfg d v

printAstDomains :: forall r. ShowAst r
                => PrintConfig -> Int -> AstDomains r -> ShowS
printAstDomains cfg d = \case
  AstDomains l ->
    if prettifyLosingSharing cfg
    then
      showCollectionWith "(" ")" (printAstUnDynamic cfg 0) (V.toList l)
    else
      showParen (d > 10)
      $ showString "dmkDomains "
        . (showParen True
           $ showString "fromList "
             . showListWith (printAstDynamic cfg 0) (V.toList l))
  t@(AstDomainsLet @m0 var0 u0 v0) ->
    if prettifyLosingSharing cfg
    then let collect :: AstDomains r -> ([(ShowS, ShowS)], ShowS)
             collect (AstDomainsLet @m var u v) =
               let name = printAstVar cfg (AstVarName @(OR.Array m r) var)
                   uPP = printAst cfg 0 u
                   (rest, corePP) = collect v
               in ((name, uPP) : rest, corePP)
             collect v = ([], printAstDomains cfg 0 v)
             (pairs, core) = collect t
         in showParen (d > 0)
            $ showString "let "
              . foldr (.) id (intersperse (showString " ; ")
                  [name . showString " = " . uPP | (name, uPP) <- pairs])
              . showString " in "
              . core
    else
      showParen (d > 10)
      $ showString "rletToDomainsOf "
        . printAst cfg 11 u0
        . showString " "
        . (showParen True
           $ showString "\\"
             . printAstVar cfg (AstVarName @(OR.Array m0 r) var0)
             . showString " -> "
             . printAstDomains cfg 0 v0)

printAstInt :: ShowAst r => PrintConfig -> Int -> AstInt r -> ShowS
printAstInt cfg d = \case
  AstIntVar var -> printAstIntVar cfg var
  AstIntOp opCode args -> printAstIntOp cfg d opCode args
  AstIntConst a -> shows a
  AstIntFloor (AstPrimalPart v) -> printPrefixOp printAst cfg d "floor" [v]
  AstIntCond b a1 a2 ->
    showParen (d > 10)
    $ showString "ifB "
      . printAstBool cfg 11 b
      . showString " "
      . printAstInt cfg 11 a1
      . showString " "
      . printAstInt cfg 11 a2
  AstMinIndex1 (AstPrimalPart v) ->
    printPrefixOp printAst cfg d "tminIndex0" [v]
  AstMaxIndex1 (AstPrimalPart v) ->
    printPrefixOp printAst cfg d "tmaxIndex0" [v]

printAstBool :: ShowAst r => PrintConfig -> Int -> AstBool r -> ShowS
printAstBool cfg d = \case
  AstBoolOp opCode args -> printAstBoolOp cfg d opCode args
  AstBoolConst b -> showString $ if b then "true" else "false"
  AstRel opCode args -> printAstRelOp printAst cfg d opCode
                        $ map unAstPrimalPart args
  AstRelInt opCode args -> printAstRelOp printAstInt cfg d opCode args

printAstOp :: (ShowAst r, KnownNat n)
           => PrintConfig -> Int -> OpCode -> [AstRanked r n] -> ShowS
printAstOp cfg d opCode args = case (opCode, args) of
  (MinusOp, [u, v]) -> printBinaryOp printAst cfg d u (6, " - ") v
  (TimesOp, [u, v]) -> printBinaryOp printAst cfg d u (7, " * ") v
  (NegateOp, [u]) -> printPrefixOp printAst cfg d "negate" [u]
  (AbsOp, [u]) -> printPrefixOp printAst cfg d "abs" [u]
  (SignumOp, [u]) -> printPrefixOp printAst cfg d "signum" [u]
  (DivideOp, [u, v]) -> printBinaryOp printAst cfg d u (7, " / ") v
  (RecipOp, [u]) -> printPrefixOp printAst cfg d "recip" [u]
  (ExpOp, [u]) -> printPrefixOp printAst cfg d "exp" [u]
  (LogOp, [u]) -> printPrefixOp printAst cfg d "log" [u]
  (SqrtOp, [u]) -> printPrefixOp printAst cfg d "sqrt" [u]
  (PowerOp, [u, v]) -> printBinaryOp printAst cfg d u (8, " ** ") v
  (LogBaseOp, [u, v]) -> printPrefixOp printAst cfg d "logBase" [u, v]
  (SinOp, [u]) -> printPrefixOp printAst cfg d "sin" [u]
  (CosOp, [u]) -> printPrefixOp printAst cfg d "cos" [u]
  (TanOp, [u]) -> printPrefixOp printAst cfg d "tan" [u]
  (AsinOp, [u]) -> printPrefixOp printAst cfg d "asin" [u]
  (AcosOp, [u]) -> printPrefixOp printAst cfg d "acos" [u]
  (AtanOp, [u]) -> printPrefixOp printAst cfg d "atan" [u]
  (SinhOp, [u]) -> printPrefixOp printAst cfg d "sinh" [u]
  (CoshOp, [u]) -> printPrefixOp printAst cfg d "cosh" [u]
  (TanhOp, [u]) -> printPrefixOp printAst cfg d "tanh" [u]
  (AsinhOp, [u]) -> printPrefixOp printAst cfg d "asinh" [u]
  (AcoshOp, [u]) -> printPrefixOp printAst cfg d "acosh" [u]
  (AtanhOp, [u]) -> printPrefixOp printAst cfg d "atanh" [u]
  (Atan2Op, [u, v]) -> printPrefixOp printAst cfg d "atan2" [u, v]
  (MaxOp, [u, v]) -> printPrefixOp printAst cfg d "max" [u, v]
  (MinOp, [u, v]) -> printPrefixOp printAst cfg d "min" [u, v]
  _ -> error $ "printAstOp: wrong number of arguments"
               ++ show (opCode, length args)

printPrefixOp :: (PrintConfig -> Int -> a -> ShowS)
              -> PrintConfig -> Int -> String -> [a]
              -> ShowS
{-# INLINE printPrefixOp #-}
printPrefixOp pr cfg d funcname args =
  let rs = map (\arg -> showString " " . pr cfg 11 arg) args
  in showParen (d > 10)
     $ showString funcname
       . foldr (.) id rs

printBinaryOp :: (PrintConfig -> Int -> a -> ShowS)
              -> PrintConfig -> Int -> a -> (Int, String) -> a
              -> ShowS
{-# INLINE printBinaryOp #-}
printBinaryOp pr cfg d left (prec, opstr) right =
  showParen (d > prec)
  $ pr cfg (prec + 1) left
    . showString opstr
    . pr cfg (prec + 1) right

printAstIntOp :: ShowAst r
              => PrintConfig -> Int -> OpCodeInt -> [AstInt r] -> ShowS
printAstIntOp cfg d opCode args = case (opCode, args) of
  (PlusIntOp, [u, v]) -> printBinaryOp printAstInt cfg d u (6, " + ") v
  (MinusIntOp, [u, v]) -> printBinaryOp printAstInt cfg d u (6, " - ") v
  (TimesIntOp, [u, v]) -> printBinaryOp printAstInt cfg d u (7, " * ") v
  (NegateIntOp, [u]) -> printPrefixOp printAstInt cfg d "negate" [u]
  (AbsIntOp, [u]) -> printPrefixOp printAstInt cfg d "abs" [u]
  (SignumIntOp, [u]) -> printPrefixOp printAstInt cfg d "signum" [u]
  (MaxIntOp, [u, v]) -> printPrefixOp printAstInt cfg d "max" [u, v]
  (MinIntOp, [u, v]) -> printPrefixOp printAstInt cfg d "min" [u, v]
  (QuotIntOp, [u, v]) -> printPrefixOp printAstInt cfg d "quot" [u, v]
  (RemIntOp, [u, v]) -> printPrefixOp printAstInt cfg d "rem" [u, v]
  _ -> error $ "printAstIntOp: wrong number of arguments"
               ++ show (opCode, length args)

printAstBoolOp
  :: ShowAst r => PrintConfig -> Int -> OpCodeBool -> [AstBool r] -> ShowS
printAstBoolOp cfg d opCode args = case (opCode, args) of
  (NotOp, [u]) -> printPrefixOp printAstBool cfg d "notB" [u]
  (AndOp, [u, v]) -> printBinaryOp printAstBool cfg d u (3, " &&* ") v
  (OrOp, [u, v]) -> printBinaryOp printAstBool cfg d u (2, " ||* ") v
  _ -> error $ "printAstBoolOp: wrong number of arguments"
               ++ show (opCode, length args)

printAstRelOp :: (PrintConfig -> Int -> a -> ShowS)
              -> PrintConfig -> Int -> OpCodeRel -> [a]
              -> ShowS
{-# INLINE printAstRelOp #-}
printAstRelOp pr cfg d opCode args = case (opCode, args) of
  (EqOp, [u, v]) -> printBinaryOp pr cfg d u (4, " ==* ") v
  (NeqOp, [u, v]) -> printBinaryOp pr cfg d u (4, " /=* ") v
  (LeqOp, [u, v]) -> printBinaryOp pr cfg d u (4, " <=* ") v
  (GeqOp, [u, v]) -> printBinaryOp pr cfg d u (4, " >=* ") v
  (LsOp, [u, v]) -> printBinaryOp pr cfg d u (4, " <* ") v
  (GtOp, [u, v]) -> printBinaryOp pr cfg d u (4, " >* ") v
  _ -> error $ "printAstRelOp: wrong number of arguments"
               ++ show (opCode, length args)

printAstVarName :: KnownNat n
                => IntMap String -> AstVarName (OR.Array n r) -> String
printAstVarName renames var =
  printAstVar (defaulPrintConfig False renames) var ""

printAstDynamicVarName :: IntMap String -> AstDynamicVarName r -> String
printAstDynamicVarName renames (AstDynamicVarName var) =
  printAstVarName renames var

printAstSimple :: (ShowAst r, KnownNat n) => IntMap String -> AstRanked r n -> String
printAstSimple renames t = printAst (defaulPrintConfig False renames) 0 t ""

printAstPretty :: (ShowAst r, KnownNat n) => IntMap String -> AstRanked r n -> String
printAstPretty renames t = printAst (defaulPrintConfig True renames) 0 t ""


printAstDomainsSimple :: ShowAst r => IntMap String -> AstDomains r -> String
printAstDomainsSimple renames t =
  printAstDomains (defaulPrintConfig False renames) 0 t ""

printAstDomainsPretty :: ShowAst r => IntMap String -> AstDomains r -> String
printAstDomainsPretty renames t =
  printAstDomains (defaulPrintConfig True renames) 0 t ""

printGradient6Simple :: (ShowAst r, KnownNat n)
                     => IntMap String -> ADAstArtifact6 n r -> String
printGradient6Simple renames ((varDt, vars1), gradient, _) =
  let varsPP = printAstVarName renames varDt
               : map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstDomainsSimple renames gradient

printGradient6Pretty :: (ShowAst r, KnownNat n)
                     => IntMap String -> ADAstArtifact6 n r -> String
printGradient6Pretty renames ((varDt, vars1), gradient, _) =
  let varsPP = printAstVarName renames varDt
               : map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstDomainsPretty renames gradient

printPrimal6Simple :: (ShowAst r, KnownNat n)
                   => IntMap String -> ADAstArtifact6 n r -> String
printPrimal6Simple renames ((_, vars1), _, primal) =
  let varsPP = map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimple renames primal

printPrimal6Pretty :: (ShowAst r, KnownNat n)
                   => IntMap String -> ADAstArtifact6 n r -> String
printPrimal6Pretty renames ((_, vars1), _, primal) =
  let varsPP = map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPretty renames primal
