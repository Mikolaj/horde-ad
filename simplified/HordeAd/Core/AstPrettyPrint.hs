{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | Pretty-printing of AST of the code to be differentiated or resulting
-- from the differentiation.
module HordeAd.Core.AstPrettyPrint
  ( printAstVarName, printAstVarNameS
  , printAstSimple, printAstPretty, printAstSimpleS, printAstPrettyS
  , printAstDomainsSimple, printAstDomainsPretty
  , printGradient6Simple, printGradient6Pretty
  , printPrimal6Simple, printPrimal6Pretty
  , printGradient6SimpleS, printGradient6PrettyS
  , printPrimal6SimpleS, printPrimal6PrettyS
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Int (Int64)
import           Data.List (intersperse)
import           Data.Proxy (Proxy (Proxy))
import           Data.Strict.IntMap (IntMap)
import qualified Data.Strict.IntMap as IM
import           Data.Type.Equality (testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, sameNat)
import           Type.Reflection (typeRep)

import           HordeAd.Core.Ast
import           HordeAd.Core.AstTools
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.SizedList
import           HordeAd.Core.Types

-- * Pretty-printing

-- Modeled after https://github.com/VMatthijs/CHAD/blob/755fc47e1f8d1c3d91455f123338f44a353fc265/src/TargetLanguage.hs#L335.

data PrintConfig = PrintConfig
  { prettifyLosingSharing :: Bool
  , varRenames            :: IntMap String
  , representsIntIndex    :: Bool
  }

defaulPrintConfig :: Bool -> IntMap String -> PrintConfig
defaulPrintConfig prettifyLosingSharing renames =
  let varRenames = renames `IM.union` IM.fromList [(1, "dret")]
      representsIntIndex = False
  in PrintConfig {..}

printAstVarId :: String -> PrintConfig -> AstVarId s -> ShowS
printAstVarId prefix cfg var =
  let n = fromEnum var - 100000000
  in showString $ case IM.lookup n (varRenames cfg) of
    Just name | name /= "" -> name
    _ -> prefix ++ show n

printAstVarN :: Int -> PrintConfig -> AstVarName s f r y -> ShowS
printAstVarN n cfg (AstVarName var) =
  let prefix = case n of
        0 -> "x"
        1 -> "v"
        2 -> "m"
        3 -> "t"
        4 -> "u"
        _ -> "w"
  in printAstVarId prefix cfg var

printAstVar :: forall n s r. KnownNat n
            => PrintConfig -> AstVarName s (AstRanked s) r n -> ShowS
printAstVar = printAstVarN (valueOf @n)

printAstVarS :: forall sh s r. OS.Shape sh
             => PrintConfig -> AstVarName s (AstShaped s) r sh -> ShowS
printAstVarS = printAstVarN (length (OS.shapeT @sh))

printAstIntVar :: PrintConfig -> AstVarName s f r y {-IntVarName-} -> ShowS
printAstIntVar cfg (AstVarName var) = printAstVarId "i" cfg var

printAstVarFromLet
  :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
  => AstRanked s r n -> PrintConfig -> AstVarName s (AstRanked s) r n -> ShowS
printAstVarFromLet u cfg var =
  if representsIntIndex cfg && areAllArgsInts u
  then case ( sameAstSpan @s @AstPrimal
            , sameNat (Proxy @n) (Proxy @0)
            , testEquality (typeRep @r) (typeRep @Int64) ) of
    (Just Refl, Just Refl, Just Refl) ->  -- the heuristics may have been correct
      printAstIntVar cfg var
    _ ->  -- the heuristics failed
      printAstVar cfg var
  else printAstVar cfg var

areAllArgsInts :: AstRanked s r n -> Bool
areAllArgsInts = \case
  -- A heuristics for whether all the arguments are still Int64 rank 0 tensors
  -- morally representing integer indexes. This mostly just rules out
  -- rank > 0, but also a likely float, as in the argument of AstFloor,
  -- or a likely dual number. There is an anavoidable ambiguity
  -- and so also aribtrary choices in resolving it.
  AstConst{} -> True
  AstVar{} -> True
  AstLet{} -> True  -- too early to tell, but displays the same
  AstLetADShare{} -> True  -- too early to tell
  AstNm{} -> True  -- has to keep rank and scalar, so it's ints
  AstOp{} -> True  -- has to keep rank and scalar
  AstOpIntegral{} -> True  -- has to keep rank and scalar
  AstSumOfList{} -> True  -- has to keep rank and scalar
  AstIota -> False
  AstIndex{} -> False  -- the index arguments are taken care of via printAstInt
  AstSum{} -> False
  AstScatter{} -> False
  AstFromList{} -> False
  AstFromVector{} -> False
  AstReplicate{} -> False
  AstAppend{} -> False
  AstSlice{} -> False
  AstReverse{} -> False
  AstTranspose{} -> False
  AstReshape{} -> False
  AstBuild1{} -> False
  AstGather{} -> False
  AstCast{} -> False
  AstFromIntegral{} -> True
  AstSToR{} -> False
  AstConstant{} -> True  -- the argument is emphatically a primal number; fine
  AstPrimalPart{} -> False
  AstDualPart{} -> False
  AstD{} -> False  -- dual number
  AstLetDomains{} -> True  -- too early to tell
  AstCond{} -> True  -- too early to tell
  AstFloor{} -> False
  AstMinIndex{} -> False
  AstMaxIndex{} -> False

printAstInt :: PrintConfig -> Int -> AstInt -> ShowS
printAstInt cfgOld d t =
  let cfg = cfgOld {representsIntIndex = True}
  in printAst cfg d t

printAst :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
         => PrintConfig -> Int -> AstRanked s r n -> ShowS
printAst cfgOld d t =
  if representsIntIndex cfgOld
  then case ( sameAstSpan @s @AstPrimal
            , sameNat (Proxy @n) (Proxy @0)
            , testEquality (typeRep @r) (typeRep @Int64) ) of
    (Just Refl, Just Refl, Just Refl) ->  -- the heuristics may have been correct
      case t of
        AstVar _ var -> printAstIntVar cfgOld var
        AstConst i -> shows $ OR.unScalar i
        _ -> if areAllArgsInts t
             then printAstAux cfgOld d t
             else let cfg = cfgOld {representsIntIndex = False}
                  in printAstAux cfg d t
    _ ->  -- the heuristics failed
      let cfg = cfgOld {representsIntIndex = False}
      in printAstAux cfg d t
  else printAstAux cfgOld d t

-- Precedences used are as in Haskell.
printAstAux :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
            => PrintConfig -> Int -> AstRanked s r n -> ShowS
printAstAux cfg d = \case
  AstVar _sh var -> printAstVar cfg var
  t@(AstLet @n0 @_ @r20 @s0 var0 u0 v0) ->
    if prettifyLosingSharing cfg
    then let collect :: AstRanked s r n -> ([(ShowS, ShowS)], ShowS)
             collect (AstLet @n2 @_ @r2 @s2 var u v) =
               let name = printAstVarFromLet u cfg var
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
             . printAstVarFromLet u0 cfg var0
             . showString " -> "
             . printAst cfg 0 v0)
  AstLetADShare l v -> printAst cfg d $ bindsToLet v (assocsADShare l)
  AstNm opCode args -> printAstNm printAst cfg d opCode args
  AstOp opCode args -> printAstOp printAst cfg d opCode args
  AstOpIntegral opCode args -> printAstOpIntegral printAst cfg d opCode args
  AstSumOfList [] -> error "printAst: empty AstSumOfList"
  AstSumOfList (left : args) ->
    let rs = map (\arg -> showString " + " . printAst cfg 7 arg) args
    in showParen (d > 6)
       $ printAst cfg 7 left
         . foldr (.) id rs
  AstIota -> showString "tiota"
  AstIndex v ix ->
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
  AstSlice i n v -> printPrefixOp printAst cfg d
                                  ("tslice " ++ show i ++ " " ++ show n) [v]
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
  AstGather sh v (vars, ix) ->
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
  AstCast v -> printPrefixOp printAst cfg d "tcast" [v]
  AstFromIntegral a ->
    printPrefixOp printAst cfg d "tfromIntegral" [a]
  AstSToR v -> printAstS cfg d v
  AstConst a ->
    showParen (d > 10)
    $ showString "tconst "
      . if null (OR.shapeL a)
        then shows $ head $ OR.toList a
        else showParen True
             $ shows a
  AstConstant a@AstConst{} -> printAst cfg d a
  AstConstant a -> printPrefixOp printAst cfg d "tconstant" [a]
  AstPrimalPart a -> printPrefixOp printAst cfg d "tprimalPart" [a]
  AstDualPart a -> printPrefixOp printAst cfg d "tdualPart" [a]
  AstD u u' -> printPrefixBinaryOp printAst printAst cfg d "tD" u u'
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
  AstCond b a1 a2 ->
    showParen (d > 10)
    $ showString "ifF "
      . printAstBool cfg 11 b
      . showString " "
      . printAst cfg 11 a1
      . showString " "
      . printAst cfg 11 a2
  AstFloor a ->
    printPrefixOp printAst cfg d "tfloor" [a]
  AstMinIndex a ->
    printPrefixOp printAst cfg d "tminIndex" [a]
  AstMaxIndex a ->
    printPrefixOp printAst cfg d "tmaxIndex" [a]

printAstVarFromDomains
  :: forall s. PrintConfig -> (AstVarId s, DynamicExists (AstDynamic s)) -> ShowS
printAstVarFromDomains cfg (var, d) = case d of
  DynamicExists @r (AstRToD @n _) ->
    printAstVar cfg (AstVarName @Nat @s @(AstRanked s) @r @n var)
  DynamicExists @r (AstSToD @sh _) ->
    printAstVarS cfg (AstVarName @[Nat] @s @(AstShaped s) @r @sh var)

-- Differs from standard only in the space after comma.
showListWith :: (a -> ShowS) -> [a] -> ShowS
showListWith = showCollectionWith "[" "]"

showCollectionWith :: String -> String -> (a -> ShowS) -> [a] -> ShowS
showCollectionWith start end _     []     s = start ++ end ++ s
showCollectionWith start end showx (x:xs) s = start ++ showx x (showl xs)
 where
  showl []     = end ++ s
  showl (y:ys) = ", " ++ showx y (showl ys)

printAstDynamic :: (GoodScalar r, AstSpan s)
                => PrintConfig -> Int -> AstDynamic s r -> ShowS
printAstDynamic cfg d = \case
  AstRToD v -> printPrefixOp printAst cfg d "dfromR" [v]
  AstSToD v -> printPrefixOp printAstS cfg d "dfromS" [v]

printAstUnDynamic :: (GoodScalar r, AstSpan s)
                  => PrintConfig -> Int -> AstDynamic s r -> ShowS
printAstUnDynamic cfg d = \case
  AstRToD v -> printAst cfg d v
  AstSToD v -> printAstS cfg d v

printAstDomains :: forall s. AstSpan s
                => PrintConfig -> Int -> AstDomains s -> ShowS
printAstDomains cfg d = \case
  AstDomains l ->
    if prettifyLosingSharing cfg
    then
      showCollectionWith "(" ")" (\(DynamicExists e) ->
                                    printAstUnDynamic cfg 0 e) (V.toList l)
    else
      showParen (d > 10)
      $ showString "dmkDomains "
        . (showParen True
           $ showString "fromList "
             . showListWith (\(DynamicExists e) ->
                               printAstDynamic cfg 0 e) (V.toList l))
  t@(AstDomainsLet @m0 @r0 var0 u0 v0) ->
    if prettifyLosingSharing cfg
    then let collect :: AstDomains s -> ([(ShowS, ShowS)], ShowS)
             collect (AstDomainsLet @m @r var u v) =
               let name = printAstVarFromLet u cfg var
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
             . printAstVarFromLet u0 cfg var0
             . showString " -> "
             . printAstDomains cfg 0 v0)
  t@(AstDomainsLetS @sh0 @r0 var0 u0 v0) ->
    if prettifyLosingSharing cfg
    then let collect :: AstDomains s -> ([(ShowS, ShowS)], ShowS)
             collect (AstDomainsLetS @sh @r var u v) =
               let name = printAstVarS cfg var
                   uPP = printAstS cfg 0 u
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
      $ showString "sletToDomainsOf "
        . printAstS cfg 11 u0
        . showString " "
        . (showParen True
           $ showString "\\"
             . printAstVarS cfg var0
             . showString " -> "
             . printAstDomains cfg 0 v0)

printAstBool :: PrintConfig -> Int -> AstBool -> ShowS
printAstBool cfg d = \case
  AstBoolOp opCode args -> printAstBoolOp cfg d opCode args
  AstBoolConst b -> showString $ if b then "true" else "false"
  AstRel opCode args -> printAstRelOp printAst cfg d opCode args
  AstRelS opCode args -> printAstRelOp printAstS cfg d opCode args

printAstNm :: (PrintConfig -> Int -> a -> ShowS)
              -> PrintConfig -> Int -> OpCodeNum -> [a] -> ShowS
printAstNm pr cfg d opCode args = case (opCode, args) of
  (MinusOp, [u, v]) -> printBinaryOp pr cfg d u (6, " - ") v
  (TimesOp, [u, v]) -> printBinaryOp pr cfg d u (7, " * ") v
  (NegateOp, [u]) -> printPrefixOp pr cfg d "negate" [u]
  (AbsOp, [u]) -> printPrefixOp pr cfg d "abs" [u]
  (SignumOp, [u]) -> printPrefixOp pr cfg d "signum" [u]
  _ -> error $ "printAstNm: wrong number of arguments"
               ++ show (opCode, length args)

printAstOp :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCode -> [a] -> ShowS
printAstOp pr cfg d opCode args = case (opCode, args) of
  (DivideOp, [u, v]) -> printBinaryOp pr cfg d u (7, " / ") v
  (RecipOp, [u]) -> printPrefixOp pr cfg d "recip" [u]
  (ExpOp, [u]) -> printPrefixOp pr cfg d "exp" [u]
  (LogOp, [u]) -> printPrefixOp pr cfg d "log" [u]
  (SqrtOp, [u]) -> printPrefixOp pr cfg d "sqrt" [u]
  (PowerOp, [u, v]) -> printBinaryOp pr cfg d u (8, " ** ") v
  (LogBaseOp, [u, v]) -> printPrefixOp pr cfg d "logBase" [u, v]
  (SinOp, [u]) -> printPrefixOp pr cfg d "sin" [u]
  (CosOp, [u]) -> printPrefixOp pr cfg d "cos" [u]
  (TanOp, [u]) -> printPrefixOp pr cfg d "tan" [u]
  (AsinOp, [u]) -> printPrefixOp pr cfg d "asin" [u]
  (AcosOp, [u]) -> printPrefixOp pr cfg d "acos" [u]
  (AtanOp, [u]) -> printPrefixOp pr cfg d "atan" [u]
  (SinhOp, [u]) -> printPrefixOp pr cfg d "sinh" [u]
  (CoshOp, [u]) -> printPrefixOp pr cfg d "cosh" [u]
  (TanhOp, [u]) -> printPrefixOp pr cfg d "tanh" [u]
  (AsinhOp, [u]) -> printPrefixOp pr cfg d "asinh" [u]
  (AcoshOp, [u]) -> printPrefixOp pr cfg d "acosh" [u]
  (AtanhOp, [u]) -> printPrefixOp pr cfg d "atanh" [u]
  (Atan2Op, [u, v]) -> printPrefixOp pr cfg d "atan2" [u, v]
  _ -> error $ "printAstOp: wrong number of arguments"
               ++ show (opCode, length args)

printAstOpIntegral :: (PrintConfig -> Int -> a -> ShowS)
                   -> PrintConfig -> Int -> OpCodeIntegral -> [a] -> ShowS
printAstOpIntegral pr cfg d opCode args = case (opCode, args) of
  (QuotOp, [u, v]) -> printPrefixOp pr cfg d "quot" [u, v]
  (RemOp, [u, v]) -> printPrefixOp pr cfg d "rem" [u, v]
  _ -> error $ "printAstOpIntegral: wrong number of arguments"
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

printPrefixBinaryOp :: (PrintConfig -> Int -> a -> ShowS)
                    -> (PrintConfig -> Int -> b -> ShowS)
                    -> PrintConfig -> Int -> String -> a -> b
                    -> ShowS
{-# INLINE printPrefixBinaryOp #-}
printPrefixBinaryOp pra prb cfg d funcname a b =
  let rs = [showString " " . pra cfg 11 a, showString " " . prb cfg 11 b]
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

printAstBoolOp
  :: PrintConfig -> Int -> OpCodeBool -> [AstBool] -> ShowS
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
  (EqOp, [u, v]) -> printBinaryOp pr cfg d u (4, " ==. ") v
  (NeqOp, [u, v]) -> printBinaryOp pr cfg d u (4, " /=. ") v
  (LeqOp, [u, v]) -> printBinaryOp pr cfg d u (4, " <=. ") v
  (GeqOp, [u, v]) -> printBinaryOp pr cfg d u (4, " >=. ") v
  (LsOp, [u, v]) -> printBinaryOp pr cfg d u (4, " <. ") v
  (GtOp, [u, v]) -> printBinaryOp pr cfg d u (4, " >. ") v
  _ -> error $ "printAstRelOp: wrong number of arguments"
               ++ show (opCode, length args)

printAstVarName :: KnownNat n
                => IntMap String -> AstVarName s (AstRanked s) r n
                -> String
printAstVarName renames var =
  printAstVar (defaulPrintConfig False renames) var ""

printAstVarNameS :: OS.Shape sh
                 => IntMap String -> AstVarName s (AstShaped s) r sh
                 -> String
printAstVarNameS renames var =
  printAstVarS (defaulPrintConfig False renames) var ""

printAstDynamicVarName :: IntMap String -> AstDynamicVarName -> String
printAstDynamicVarName renames (AstDynamicVarName @sh @r @s var) =
  printAstVarNameS renames (AstVarName @[Nat] @s @(AstShaped s) @r @sh var)

printAstS :: forall sh s r. (GoodScalar r, OS.Shape sh, AstSpan s)
          => PrintConfig -> Int -> AstShaped s r sh -> ShowS
printAstS cfg d = \case
  AstVarS var -> printAstVarS cfg var
  t@(AstLetS @sh0 @_ @r20 @s0 var0 u0 v0) ->
    if prettifyLosingSharing cfg
    then let collect :: AstShaped s r sh -> ([(ShowS, ShowS)], ShowS)
             collect (AstLetS @sh2 @_ @r2 @s2 var u v) =
               let name = printAstVarS cfg var
                   uPP = printAstS cfg 0 u
                   (rest, corePP) = collect v
               in ((name, uPP) : rest, corePP)
             collect v = ([], printAstS cfg 0 v)
             (pairs, core) = collect t
         in showParen (d > 0)
            $ showString "let "
              . foldr (.) id (intersperse (showString " ; ")
                  [name . showString " = " . uPP | (name, uPP) <- pairs])
              . showString " in "
              . core
    else
      showParen (d > 10)
      $ showString "slet "
        . printAstS cfg 11 u0
        . showString " "
        . (showParen True
           $ showString "\\"
             . printAstVarS cfg var0
             . showString " -> "
             . printAstS cfg 0 v0)
  AstLetADShareS l v -> printAstS cfg d $ bindsToLetS v (assocsADShare l)
  AstNmS opCode args -> printAstNm printAstS cfg d opCode args
  AstOpS opCode args -> printAstOp printAstS cfg d opCode args
  AstOpIntegralS opCode args -> printAstOpIntegral printAstS cfg d opCode args
  AstSumOfListS [] -> error "printAst: empty AstSumOfList"
  AstSumOfListS (left : args) ->
    let rs = map (\arg -> showString " + " . printAstS cfg 7 arg) args
    in showParen (d > 6)
       $ printAstS cfg 7 left
         . foldr (.) id rs
  AstIotaS -> showString "siota"
  AstIndexS v ix ->
    showParen (d > 9)
    $ printAstS cfg 10 v
      . showString " !$ "
      . showListWith (printAstInt cfg 0) (ShapedList.sizedListToList ix)
  AstSumS v -> printPrefixOp printAstS cfg d "ssum" [v]
  AstScatterS v (vars, ix) ->
    showParen (d > 10)
    $ showString ("sscatter ")
      . printAstS cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (ShapedList.sizedListToList vars)
           . showString " -> "
           . showListWith (printAstInt cfg 0) (ShapedList.sizedListToList ix))
  AstFromListS l ->
    showParen (d > 10)
    $ showString "sfromList "
      . showListWith (printAstS cfg 0) l
  AstFromVectorS l ->
    showParen (d > 10)
    $ showString "sfromVector "
      . (showParen True
         $ showString "fromList "
           . showListWith (printAstS cfg 0) (V.toList l))
  AstReplicateS v -> printPrefixOp printAstS cfg d "sreplicate" [v]
  AstAppendS x y ->
    -- x and y have different types, unlike in AstAppend, so we
    -- have to inline printPrefixOp:
    let rs = [ showString " " . printAstS cfg 11 x
             , showString " " . printAstS cfg 11 y ]
    in showParen (d > 10)
       $ showString "sappend"
         . foldr (.) id rs
  AstSliceS v -> printPrefixOp printAstS cfg d "sslice" [v]
  AstReverseS v -> printPrefixOp printAstS cfg d "sreverse" [v]
  AstTransposeS v ->
    printPrefixOp printAstS cfg d "stranspose" [v]
  AstReshapeS v ->
    printPrefixOp printAstS cfg d "sreshape" [v]
  AstBuild1S (var, v) ->
    showParen (d > 10)
    $ showString "sbuild1 "
      . (showParen True
         $ showString "\\"
           . printAstIntVar cfg var
           . showString " -> "
           . printAstS cfg 0 v)
  AstGatherS v (vars, ix) ->
    showParen (d > 10)
    $ showString ("sgather ")
      . printAstS cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (ShapedList.sizedListToList vars)
           . showString " -> "
           . showListWith (printAstInt cfg 0) (ShapedList.sizedListToList ix))
  AstCastS v -> printPrefixOp printAstS cfg d "scast" [v]
  AstFromIntegralS a ->
    printPrefixOp printAstS cfg d "sfromIntegral" [a]
  AstRToS v -> printAst cfg d v
  AstConstS a ->
    showParen (d > 10)
    $ showString "sconst "
      . if null (OS.shapeT @sh)
        then shows $ head $ OS.toList a
        else showParen True
             $ shows a
  AstConstantS a@AstConstS{} -> printAstS cfg d a
  AstConstantS a ->
    printPrefixOp printAstS cfg d "sconstant" [a]
  AstPrimalPartS a -> printPrefixOp printAstS cfg d "sprimalPart" [a]
  AstDualPartS a -> printPrefixOp printAstS cfg d "sdualPart" [a]
  AstDS u u' -> printPrefixBinaryOp printAstS printAstS cfg d "tDS" u u'
  AstLetDomainsS vars l v ->
    showParen (d > 10)
    $ showString "sletDomainsOf "
      . printAstDomains cfg 11 l
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstVarFromDomains cfg)
                          (V.toList $ V.zip vars (unwrapAstDomains l))
           . showString " -> "
           . printAstS cfg 0 v)
      -- TODO: this does not roundtrip yet
  AstCondS b a1 a2 ->
    showParen (d > 10)
    $ showString "ifF "
      . printAstBool cfg 11 b
      . showString " "
      . printAstS cfg 11 a1
      . showString " "
      . printAstS cfg 11 a2
  AstFloorS a ->  printPrefixOp printAstS cfg d "sfloor" [a]
  AstMinIndexS a -> printPrefixOp printAstS cfg d "sminIndex" [a]
  AstMaxIndexS a -> printPrefixOp printAstS cfg d "smaxIndex" [a]

printAstSimple :: (GoodScalar r, KnownNat n, AstSpan s)
               => IntMap String -> AstRanked s r n -> String
printAstSimple renames t = printAst (defaulPrintConfig False renames) 0 t ""

printAstPretty :: (GoodScalar r, KnownNat n, AstSpan s)
               => IntMap String -> AstRanked s r n -> String
printAstPretty renames t = printAst (defaulPrintConfig True renames) 0 t ""

printAstSimpleS :: (GoodScalar r, OS.Shape sh, AstSpan s)
                => IntMap String -> AstShaped s r sh -> String
printAstSimpleS renames t = printAstS (defaulPrintConfig False renames) 0 t ""

printAstPrettyS :: (GoodScalar r, OS.Shape sh, AstSpan s)
                => IntMap String -> AstShaped s r sh -> String
printAstPrettyS renames t = printAstS (defaulPrintConfig True renames) 0 t ""

printAstDomainsSimple :: AstSpan s => IntMap String -> AstDomains s -> String
printAstDomainsSimple renames t =
  printAstDomains (defaulPrintConfig False renames) 0 t ""

printAstDomainsPretty :: AstSpan s => IntMap String -> AstDomains s -> String
printAstDomainsPretty renames t =
  printAstDomains (defaulPrintConfig True renames) 0 t ""

printGradient6Simple :: KnownNat n
                     => IntMap String -> ADAstArtifact6 (AstRanked AstPrimal) r n
                     -> String
printGradient6Simple renames ((varDt, vars1), gradient, _) =
  let varsPP = printAstVarName renames varDt
               : map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstDomainsSimple renames gradient

printGradient6Pretty :: KnownNat n
                     => IntMap String -> ADAstArtifact6 (AstRanked AstPrimal) r n
                     -> String
printGradient6Pretty renames ((varDt, vars1), gradient, _) =
  let varsPP = printAstVarName renames varDt
               : map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstDomainsPretty renames gradient

printPrimal6Simple :: (GoodScalar r, KnownNat n)
                   => IntMap String -> ADAstArtifact6 (AstRanked AstPrimal) r n
                   -> String
printPrimal6Simple renames ((_, vars1), _, primal) =
  let varsPP = map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimple renames primal

printPrimal6Pretty :: (GoodScalar r, KnownNat n)
                   => IntMap String -> ADAstArtifact6 (AstRanked AstPrimal) r n
                   -> String
printPrimal6Pretty renames ((_, vars1), _, primal) =
  let varsPP = map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPretty renames primal

printGradient6SimpleS :: OS.Shape sh
                      => IntMap String -> ADAstArtifact6 (AstShaped AstPrimal) r sh
                      -> String
printGradient6SimpleS renames ((varDt, vars1), gradient, _) =
  let varsPP = printAstVarNameS renames varDt
               : map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstDomainsSimple renames gradient

printGradient6PrettyS :: OS.Shape sh
                      => IntMap String -> ADAstArtifact6 (AstShaped AstPrimal) r sh
                      -> String
printGradient6PrettyS renames ((varDt, vars1), gradient, _) =
  let varsPP = printAstVarNameS renames varDt
               : map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstDomainsPretty renames gradient

printPrimal6SimpleS :: (GoodScalar r, OS.Shape sh)
                    => IntMap String -> ADAstArtifact6 (AstShaped AstPrimal) r sh
                    -> String
printPrimal6SimpleS renames ((_, vars1), _, primal) =
  let varsPP = map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimpleS renames primal

printPrimal6PrettyS :: (GoodScalar r, OS.Shape sh)
                    => IntMap String -> ADAstArtifact6 (AstShaped AstPrimal) r sh
                    -> String
printPrimal6PrettyS renames ((_, vars1), _, primal) =
  let varsPP = map (printAstDynamicVarName renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPrettyS renames primal
