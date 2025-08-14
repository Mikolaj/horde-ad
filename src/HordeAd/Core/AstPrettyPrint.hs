-- | Pretty-printing of the AST. Some of the variants of pretty-printing
-- almost roundtrip, while others are more readable but less faithful.
module HordeAd.Core.AstPrettyPrint
  ( PrintConfig(..), defaulPrintConfig
  , printAstVar, printAst
  ) where

import Prelude

import Data.Foldable qualified as Foldable
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.List (intersperse)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Permutation (Perm (..), permToList)
import Data.Array.Nested.Shaped.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstTools
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Pretty-printing config

-- Modeled after https://github.com/VMatthijs/CHAD/blob/755fc47e1f8d1c3d91455f123338f44a353fc265/src/TargetLanguage.hs#L335.

-- TODO: ensure that terms roundtrip if neither loseRoudtrip
-- nor ignoreNestedLambdas is set and that explicit sharing is then preserved
-- as opposed to displaying sharing as Haskell lets.
-- Note that disabling ignoreNestedLambdas causes derivatives to be computed,
-- so pretty-printing in this way can be very expensive.
data PrintConfig = PrintConfig
  { loseRoudtrip        :: Bool
  , ignoreNestedLambdas :: Bool
  , varRenames          :: IntMap String
  }

defaulPrintConfig :: PrintConfig
defaulPrintConfig = PrintConfig
  { loseRoudtrip        = True
  , ignoreNestedLambdas = True
  , varRenames          = IM.empty
  }


-- * Pretty-printing of variables

printAstVarId :: String -> PrintConfig -> AstVarId -> ShowS
printAstVarId prefix cfg var =
  let n = fromEnum var - 100000000
  in showString $ case IM.lookup n (varRenames cfg) of
    Just name | name /= "" -> name
    _ -> prefix ++ show n

printAstVar :: forall s y. AstSpan s
            => PrintConfig -> AstVarName s y -> ShowS
printAstVar cfg var = case isTensorInt (Proxy @s) (varNameToFTK var) of
  Just Refl -> printAstIntVar cfg var
  _ -> let prefix = case lengthSTK (ftkToSTK $ varNameToFTK var) of
             0 -> "x"
             1 -> "v"
             2 -> "m"
             3 -> "t"
             4 -> "u"
             _ -> "w"
       in printAstVarId prefix cfg (varNameToAstVarId var)

printAstIntVar :: PrintConfig -> IntVarName -> ShowS
printAstIntVar cfg var = printAstVarId "i" cfg (varNameToAstVarId var)


-- * Pretty-printing of AST terms

-- Precedences used are as in Haskell.
printAst :: forall s y ms. AstSpan s
         => PrintConfig -> Int -> AstTensor ms s y -> ShowS
printAst cfg d = \case
  AstPair t1 t2 ->
    showParen (d > 10)
    $ showString "tpair "
      . printAst cfg 11 t1
      . showString " "
      . printAst cfg 11 t2
  AstProject1 t -> printPrefixOp printAst cfg d "tproject1" [t]
  AstProject2 t -> printPrefixOp printAst cfg d "tproject2" [t]
  AstFromVector snat stk l ->
   if loseRoudtrip cfg
   then case stk of
    STKR{} ->
      showParen (d > 10)
      $ showString "rfromVector "
        . (showParen True
           $ showString "fromList "
             . showListWith (printAst cfg 0) (V.toList l))
    STKS{} ->
      showParen (d > 10)
      $ showString "sfromVector "
        . (showParen True
           $ showString "fromList "
             . showListWith (printAst cfg 0) (V.toList l))
    STKX{} ->
      showParen (d > 10)
      $ showString "xfromVector "
        . (showParen True
           $ showString "fromList "
             . showListWith (printAst cfg 0) (V.toList l))
    _ ->  -- scalar and product
      showParen (d > 10)
      $ showString "tfromVector "
        . (showParen True
           $ showString "fromList "
             . showListWith (printAst cfg 0) (V.toList l))
   else showParen (d > 10)
        $ showString ("tfromVector (" ++ show snat ++ ") (" ++ show stk ++ ") ")
          . (showParen True
             $ showString "fromList "
               . showListWith (printAst cfg 0) (V.toList l))
  -- This is too common to be verbose even in no loseRoudtrip mode.
  AstSum snat stk v -> case stk of
    STKR{} -> printPrefixOp printAst cfg d "rsum" [v]
    STKS{} -> printPrefixOp printAst cfg d
                            ("ssum @" ++ show (sNatValue snat)) [v]
    STKX{} -> printPrefixOp printAst cfg d
                            ("xsum @" ++ show (sNatValue snat)) [v]
    _ ->  -- scalar and product
      printPrefixOp printAst cfg d
                    ("tsum (" ++ show snat ++ ") (" ++ show stk ++ ")") [v]
  -- This is too common to be verbose even in no loseRoudtrip mode.
  AstReplicate snat stk v -> case stk of
    STKR{} -> printPrefixOp printAst cfg d
                            ("rreplicate " ++ show (sNatValue snat)) [v]
    STKS{} -> printPrefixOp printAst cfg d
                            ("sreplicate @" ++ show (sNatValue snat)) [v]
    STKX{} -> printPrefixOp printAst cfg d
                            ("xreplicate @" ++ show (sNatValue snat)) [v]
    _ ->  -- scalar and product
      printPrefixOp
        printAst cfg d
        ("treplicate (" ++ show snat ++ ") (" ++ show stk ++ ")") [v]
  AstMapAccumRDer k bftk eftk f df rf acc0 es ->
   if loseRoudtrip cfg
   then
    showParen (d > 10)
    $ showString "tmapAccumRDer "
      . showParen True (shows k)
      . showString " "
      . printAstHFun cfg 10 f
      . showString " "
      . printAstHFun cfg 10 df
      . showString " "
      . printAstHFun cfg 10 rf
      . showString " "
      . printAst cfg 11 acc0
      . showString " "
      . printAst cfg 11 es
   else
    showParen (d > 10)
    $ showString "tmapAccumRDer "
      . showParen True (shows k)
      . showString " "
      . showParen True (shows bftk)
      . showString " "
      . showParen True (shows eftk)
      . showString " "
      . printAstHFun cfg 10 f
      . showString " "
      . printAstHFun cfg 10 df
      . showString " "
      . printAstHFun cfg 10 rf
      . showString " "
      . printAst cfg 11 acc0
      . showString " "
      . printAst cfg 11 es
  AstMapAccumLDer k bftk eftk f df rf acc0 es ->
   if loseRoudtrip cfg
   then
    showParen (d > 10)
    $ showString "tmapAccumLDer "
      . showParen True (shows k)
      . showString " "
      . printAstHFun cfg 10 f
      . showString " "
      . printAstHFun cfg 10 df
      . showString " "
      . printAstHFun cfg 10 rf
      . showString " "
      . printAst cfg 11 acc0
      . showString " "
      . printAst cfg 11 es
   else
    showParen (d > 10)
    $ showString "tmapAccumLDer "
      . showParen True (shows k)
      . showString " "
      . showParen True (shows bftk)
      . showString " "
      . showParen True (shows eftk)
      . showString " "
      . printAstHFun cfg 10 f
      . showString " "
      . printAstHFun cfg 10 df
      . showString " "
      . printAstHFun cfg 10 rf
      . showString " "
      . printAst cfg 11 acc0
      . showString " "
      . printAst cfg 11 es
  AstApply t ll -> showParen (d > 10)
                   $ showString "tApply "
                     . printAstHFunOneUnignore cfg 10 t
                         -- this is a lambda, but not nested, so always printed
                     . showString " "
                     . printAst cfg 11 ll
  AstVar var -> printAstVar cfg var
  AstCond b a1 a2 ->
    showParen (d > 10)
    $ showString "ifH "
      . printAstBool cfg 11 b
      . showString " "
      . printAst cfg 11 a1
      . showString " "
      . printAst cfg 11 a2
  AstBuild1 k stk (var, v) ->
   if loseRoudtrip cfg
   then
    showParen (d > 10)
    $ showString "tbuild1 ("
      . shows k
      . showString ") "
      . (showParen True
         $ showString "\\"
           . printAstIntVar cfg var
           . showString " -> "
           . printAst cfg 0 v)
   else
    showParen (d > 10)
    $ showString "tbuild1 ("
      . shows k
      . showString ") "
      . showParen True (shows stk)
      . showString " "
      . (showParen True
         $ showString "\\"
           . printAstIntVar cfg var
           . showString " -> "
           . printAst cfg 0 v)

  t@(AstLet @_ @_ @s1 var0 u0 v0) ->
    if loseRoudtrip cfg
    then let collect :: AstTensor AstMethodLet s y -> ([(ShowS, ShowS)], ShowS)
             collect (AstLet var u v) =
               let name = printAstVar cfg var
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
    else let keyword = case ( sameAstSpan @s1 @PrimalSpan
                            , sameAstSpan @s @FullSpan ) of
               (Just Refl, Just Refl) -> "ttletPrimal "
               _ -> "tlet "
         in showParen (d > 10)
            $ showString keyword
              . printAst cfg 11 u0
              . showString " "
              . (showParen True
                 $ showString "\\"
                   . printAstVar cfg var0
                   . showString " -> "
                   . printAst cfg 0 v0)
  AstShare _var v -> printPrefixOp printAst cfg d "tshare" [v]
  AstToShare v -> printPrefixOp printAst cfg d "toShare" [v]

  AstPrimalPart a ->
    if loseRoudtrip cfg
    then case ftkAst a of
      FTKR{} -> printPrefixOp printAst cfg d "rprimalPart" [a]
      FTKS{} -> printPrefixOp printAst cfg d "sprimalPart" [a]
      FTKX{} -> printPrefixOp printAst cfg d "xprimalPart" [a]
      _      -> printPrefixOp printAst cfg d "tprimalPart" [a]
    else printPrefixOp printAst cfg d "tprimalPart" [a]
  AstDualPart a ->
    if loseRoudtrip cfg
    then case ftkAst a of
      FTKR{} -> printPrefixOp printAst cfg d "rdualPart" [a]
      FTKS{} -> printPrefixOp printAst cfg d "sdualPart" [a]
      FTKX{} -> printPrefixOp printAst cfg d "xdualPart" [a]
      _      -> printPrefixOp printAst cfg d "tdualPart" [a]
    else printPrefixOp printAst cfg d
                       ("tdualPart (" ++ show (ftkToSTK (ftkAst a)) ++ ")") [a]
  AstFromPrimal a ->
    if loseRoudtrip cfg
    then printAst cfg d a
    else printPrefixOp
           printAst cfg d
           ("tfromPrimal (" ++ show (ftkToSTK (ftkAst a)) ++ ")") [a]
  AstFromDual a ->
    if loseRoudtrip cfg
    then printAst cfg d a
    else printPrefixOp printAst cfg d "tfromDual" [a]

  AstPlusK u v -> printBinaryOp printAst cfg d u (6, "+") v
  AstTimesK u v -> printBinaryOp printAst cfg d u (7, "*") v
  AstN1K opCode u -> printAstN1R printAst cfg d opCode u
  AstR1K opCode u -> printAstR1R printAst cfg d opCode u
  AstR2K opCode u v -> printAstR2R printAst cfg d opCode u v
  AstI2K opCode u v -> printAstI2R printAst cfg d opCode u v
  AstConcreteK k -> showNumber k
  AstFloorK v ->
    printPrefixOp printAst cfg d "kfloor" [v]
  AstFromIntegralK v ->
    printPrefixOp printAst cfg d "kfromIntegral" [v]
  AstCastK v ->
    printPrefixOp printAst cfg d "kcast" [v]

  AstPlusS u v -> printBinaryOp printAst cfg d u (6, "+") v
  AstTimesS u v -> printBinaryOp printAst cfg d u (7, "*") v
  AstN1S opCode u -> printAstN1R printAst cfg d opCode u
  AstR1S opCode u -> printAstR1R printAst cfg d opCode u
  AstR2S opCode u v -> printAstR2R printAst cfg d opCode u v
  AstI2S opCode u v -> printAstI2R printAst cfg d opCode u v
  AstConcreteS a -> case Nested.sshape a of
    ZSS -> showParen (d > 10)
           $ showString "sscalar "
             . showNumber (Nested.sunScalar a)
    _ -> showParen (d > 10)
         $ showString "sconcrete "
           . (showParen True
              $ shows a)
  AstFloorS a ->
    printPrefixOp printAst cfg d "sfloor" [a]
  AstFromIntegralS a ->
    printPrefixOp printAst cfg d "sfromIntegral" [a]
  AstCastS a ->
    printPrefixOp printAst cfg d "scast" [a]

  AstIndexS _ v ix ->
    showParen (d > 9)
    $ printAst cfg 10 v
      . showString " !$ "
      . showListWith (printAst cfg 0) (Foldable.toList ix)
  AstScatterS _ v (ZS, ix) ->
    showParen (d > 9)
    $ showString "soneHot "
      . printAst cfg 11 v
      . showString " "
      . showListWith (printAst cfg 0) (Foldable.toList ix)
  AstScatterS sh v (vars, ix) ->
   if loseRoudtrip cfg
   then
    showParen (d > 10)
    $ showString "sscatter "
      . printAst cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (listsToList vars)
           . showString " -> "
           . showListWith (printAst cfg 0) (Foldable.toList ix))
   else
    showParen (d > 10)
    $ showString ("sscatter " ++ show sh ++ " ")
      . printAst cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (listsToList vars)
           . showString " -> "
           . showListWith (printAst cfg 0) (Foldable.toList ix))
  {- Let's re-enable this when/if we remove AstIndexS altogether
     or at least stop rewriting this to AstIndexS but instead optimize
     the instances for this case:
  AstGatherS _ v (ZS, ix) ->
    showParen (d > 9)
    $ printAst cfg 10 v
      . showString " !$ "
      . showListWith (printAst cfg 0) (Foldable.toList ix) -}
  AstGatherS sh v (vars, ix) ->
   if loseRoudtrip cfg
   then
    showParen (d > 10)
    $ showString "sgather "
      . printAst cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (listsToList vars)
           . showString " -> "
           . showListWith (printAst cfg 0) (Foldable.toList ix))
   else
    showParen (d > 10)
    $ showString ("sgather " ++ show sh ++ " ")
      . printAst cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (listsToList vars)
           . showString " -> "
           . showListWith (printAst cfg 0) (Foldable.toList ix))
  AstMinIndexS a -> printPrefixOp printAst cfg d "sminIndex" [a]
  AstMaxIndexS a -> printPrefixOp printAst cfg d "smaxIndex" [a]
  AstIotaS snat ->
    showParen (d > 10)
    $ showString ("siota (" ++ show snat ++ ")")
  AstAppendS t1 t2 ->
    showParen (d > 10)
    $ showString "sappend "
      . printAst cfg 11 t1
      . showString " "
      . printAst cfg 11 t2
  AstSliceS i n _k v ->
    printPrefixOp printAst cfg d
                  ("sslice (" ++ show i ++ ") (" ++ show n ++ ")") [v]
  AstReverseS v -> printPrefixOp printAst cfg d "sreverse" [v]
  AstTransposeS (SNat' @1 `PCons` SNat' @0 `PCons` PNil) v ->
    printPrefixOp printAst cfg d "str" [v]
  AstTransposeS perm v ->
   if loseRoudtrip cfg
   then printPrefixOp printAst cfg d
                      ("stranspose @" ++ show (permToList perm)) [v]
   else printPrefixOp
          printAst cfg d
          ("ttranspose (makePerm @" ++ show (permToList perm) ++ ")") [v]
  AstReshapeS sh2 v ->
    printPrefixOp printAst cfg d ("sreshape @" ++ show (shsToList sh2)) [v]

  -- TODO: pretty-print correctly szip, sunzip, snestS, sunNestS
  -- or at least make sure they get printed as tconvert, not as the others
  AstConvert c t -> case (ftkToSTK (ftkAst t), convertFTK c (ftkAst t)) of
    (STKScalar, FTKS{}) -> printPrefixOp printAst cfg d "sfromK" [t]
    (STKR{}, FTKS{}) -> printPrefixOp printAst cfg d "sfromR" [t]
    (STKX{}, FTKS{}) -> printPrefixOp printAst cfg d "sfromX" [t]
    (STKS{}, FTKScalar) -> printPrefixOp printAst cfg d "kfromS" [t]
    (STKS{}, FTKR{}) -> printPrefixOp printAst cfg d "rfromS" [t]
    (STKS{}, FTKX{}) -> printPrefixOp printAst cfg d "xfromS" [t]
    (ystk, _) -> let s = "tconvert (" ++ show c ++ ") (" ++ show ystk ++ ")"
                 in printPrefixOp printAst cfg d s [t]

  AstSum0S v ->
    printPrefixOp printAst cfg d "ssum0" [v]
  AstDot0S u v ->
    printPrefixOp printAst cfg d "sdot0" [u, v]
  AstDot1InS _ _ u v ->
    printPrefixOp printAst cfg d "sdot1In" [u, v]
  AstMatmul2S SNat SNat SNat u v ->
    showParen (d > 10)
    $ showString "smatmul2 "
      . printAst cfg 11 u
      . showString " "
      . printAst cfg 11 v

showNumber :: Show a => a -> ShowS
{-# INLINE showNumber #-}
showNumber a = case show a of
  s@('-' : _) -> showParen True (showString s)
  s -> showString s

-- Differs from standard only in the space after comma.
showListWith :: (a -> ShowS) -> [a] -> ShowS
{-# INLINE showListWith #-}
showListWith = showCollectionWith "[" ", " "]"

showCollectionWith :: String -> String -> String -> (a -> ShowS) -> [a] -> ShowS
{-# INLINE showCollectionWith #-}
showCollectionWith start _   end _     []     s = start ++ end ++ s
showCollectionWith start sep end showx (x:xs) s = start ++ showx x (showl xs)
 where
  showl []     = end ++ s
  showl (y:ys) = sep ++ showx y (showl ys)

printAstHFun :: (AstSpan s, AstSpan s2)
             => PrintConfig -> Int -> AstHFun s s2 x y -> ShowS
printAstHFun cfg d = \case
  AstLambda var l ->
    if loseRoudtrip cfg
    then if ignoreNestedLambdas cfg
         then showString "<lambda>"
         else showParen (d > 0)
              $ showString "\\"
                . printAstVar cfg var
                . showString " -> "
                . printAst cfg 0 l
    else showParen (d > 0)
         $ showString "tlambda $ \\"
           . printAstVar cfg var
           . showString " -> "
           . printAst cfg 0 l

printAstHFunOneUnignore :: (AstSpan s, AstSpan s2)
                        => PrintConfig -> Int -> AstHFun s s2 x y -> ShowS
printAstHFunOneUnignore cfg d = \case
  AstLambda var l ->
    if loseRoudtrip cfg
    then showParen (d > 0)
         $ showString "\\"
           . printAstVar cfg var
           . showString " -> "
           . printAst cfg 0 l
    else showParen (d > 0)
         $ showString "tlambda $ \\"
           . printAstVar cfg var
           . showString " -> "
           . printAst cfg 0 l

printAstBool :: PrintConfig -> Int -> AstBool ms -> ShowS
printAstBool cfg d = \case
  AstBoolConst b -> showString $ if b then "true" else "false"
  AstBoolNot u -> printPrefixOp printAstBool cfg d "notB" [u]
  AstBoolAnd u v -> printBinaryOp printAstBool cfg d u (3, "&&*") v
  AstLeqK u v -> printBinaryOp printAst cfg d u (4, "<=.") v
  AstLeqS u v -> printBinaryOp printAst cfg d u (4, "<=.") v

printAstN1R :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCodeNum1 -> a -> ShowS
printAstN1R pr cfg d opCode u = case opCode of
  NegateOp -> printPrefixOp pr cfg d "negate" [u]
  AbsOp -> printPrefixOp pr cfg d "abs" [u]
  SignumOp -> printPrefixOp pr cfg d "signum" [u]

printAstR1R :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCode1 -> a -> ShowS
printAstR1R pr cfg d opCode u = case opCode of
  RecipOp -> printPrefixOp pr cfg d "recip" [u]
  ExpOp -> printPrefixOp pr cfg d "exp" [u]
  LogOp -> printPrefixOp pr cfg d "log" [u]
  SqrtOp -> printPrefixOp pr cfg d "sqrt" [u]
  SinOp -> printPrefixOp pr cfg d "sin" [u]
  CosOp -> printPrefixOp pr cfg d "cos" [u]
  TanOp -> printPrefixOp pr cfg d "tan" [u]
  AsinOp -> printPrefixOp pr cfg d "asin" [u]
  AcosOp -> printPrefixOp pr cfg d "acos" [u]
  AtanOp -> printPrefixOp pr cfg d "atan" [u]
  SinhOp -> printPrefixOp pr cfg d "sinh" [u]
  CoshOp -> printPrefixOp pr cfg d "cosh" [u]
  TanhOp -> printPrefixOp pr cfg d "tanh" [u]
  AsinhOp -> printPrefixOp pr cfg d "asinh" [u]
  AcoshOp -> printPrefixOp pr cfg d "acosh" [u]
  AtanhOp -> printPrefixOp pr cfg d "atanh" [u]

printAstR2R :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCode2 -> a -> a -> ShowS
printAstR2R pr cfg d opCode u v = case opCode of
  DivideOp -> printBinaryOp pr cfg d u (7, "/") v
  PowerOp -> printBinaryOp pr cfg d u (8, "**") v
  LogBaseOp -> printPrefixOp pr cfg d "logBase" [u, v]
  Atan2Op -> printPrefixOp pr cfg d "atan2H" [u, v]

printAstI2R :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCodeIntegral2 -> a -> a -> ShowS
printAstI2R pr cfg d opCode u v = case opCode of
  QuotOp -> printPrefixOp pr cfg d "quotH" [u, v]
  RemOp -> printPrefixOp pr cfg d "remH" [u, v]

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
    . showString (" " ++ opstr ++ " ")
    . pr cfg (prec + 1) right
