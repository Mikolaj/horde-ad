{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | Pretty-printing of the AST. Some of the variants of pretty-printing
-- almost roundtrip, while others are more readable but less faithful.
module HordeAd.Core.AstPrettyPrint
  ( -- * Pretty-printing terms in a few useful configurations
    printAstVarName
  , printAstSimple, printAstPretty, printAstPrettyButNested
  , printArtifactSimple, printArtifactPretty
  , printArtifactPrimalSimple, printArtifactPrimalPretty
  ) where

import Prelude

import Data.Foldable qualified as Foldable
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (fromSNat)

import Data.Array.Mixed.Permutation (Perm (..), permToList)
import Data.Array.Nested (ListS (..), ShR (..), ShS (..), ShX (..))
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape (listsToList, shsRank)

import HordeAd.Core.Ast
import HordeAd.Core.AstTools
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Pretty-printing setup and checks

-- Modeled after https://github.com/VMatthijs/CHAD/blob/755fc47e1f8d1c3d91455f123338f44a353fc265/src/TargetLanguage.hs#L335.

-- TODO: ensure that terms roundtrip if neither loseRoudtrip
-- nor ignoreNestedLambdas is set.
-- Ideally, pretty-printing would also preserve the explicit sharing
-- in this case instead of displaying it as Haskell sharing.
-- Note that other options may cause the roundtrip to cost more than
-- a single pass over the term, e.g., ignoreNestedLambdas causes derivatives
-- to be recomputed.
data PrintConfig = PrintConfig
  { loseRoudtrip        :: Bool
  , ignoreNestedLambdas :: Bool
  , varRenames          :: IntMap String
  , representsIntIndex  :: Bool
  }

defaulPrintConfig :: Bool -> IntMap String -> PrintConfig
defaulPrintConfig loseRoudtrip renames =
  let varRenames = renames  -- TODO: `IM.union` IM.fromList [(1, "dret")]
      ignoreNestedLambdas = loseRoudtrip
      representsIntIndex = False
  in PrintConfig {..}

defaulPrintConfig2 :: Bool -> Bool -> IntMap String -> PrintConfig
defaulPrintConfig2 loseRoudtrip ignoreNestedLambdas renames =
  let varRenames = renames  -- TODO: `IM.union` IM.fromList [(1, "dret")]
      representsIntIndex = False
  in PrintConfig {..}


-- * Pretty-printing of variables

printAstVarId :: String -> PrintConfig -> AstVarId -> ShowS
printAstVarId prefix cfg var =
  let n = fromEnum var - 100000000
  in showString $ case IM.lookup n (varRenames cfg) of
    Just name | name /= "" -> name
    _ -> prefix ++ show n

printAstVar :: forall s y.
               PrintConfig -> STensorKind y -> AstVarName s y -> ShowS
printAstVar cfg stk var =
  let rankTensorKind :: STensorKind x -> Int
      rankTensorKind (STKScalar) = 0
      rankTensorKind (STKR snat _) = fromInteger $ fromSNat snat
      rankTensorKind (STKS sh _) = fromInteger $ fromSNat $ shsRank sh
      rankTensorKind (STKX sh _) = fromInteger $ fromSNat $ ssxRank sh
      rankTensorKind (STKProduct sy sz) =
        rankTensorKind sy `max` rankTensorKind sz
      n = rankTensorKind stk
      varId = varNameToAstVarId var
      prefix = case n of
        -1 -> "h"
        0 -> "x"
        1 -> "v"
        2 -> "m"
        3 -> "t"
        4 -> "u"
        _ -> "w"
  in printAstVarId prefix cfg varId

printAstIntVar :: PrintConfig -> IntVarName -> ShowS
printAstIntVar cfg var = printAstVarId "i" cfg (varNameToAstVarId var)

printAstVarFromLet
  :: forall s y ms. AstSpan s
  => AstTensor ms s y -> PrintConfig -> AstVarName s y -> ShowS
printAstVarFromLet u cfg var =
  let stk = ftkToSTK (ftkAst u)
  in if representsIntIndex cfg
     then case isTensorInt u of
       Just Refl -> printAstIntVar cfg var
       _ -> printAstVar cfg stk var
     else printAstVar cfg stk var


-- * General pretty-printing of AST terms

printAstInt :: PrintConfig -> Int -> AstInt ms -> ShowS
printAstInt cfgOld d t =
  let cfg = cfgOld {representsIntIndex = True}
  in printAst cfg d t

printAst :: forall s y ms. AstSpan s
         => PrintConfig -> Int -> AstTensor ms s y -> ShowS
printAst cfgOld d t =
  if representsIntIndex cfgOld
  then case isTensorInt t of
    Just Refl -> case t of
      AstVar _ var -> printAstIntVar cfgOld var
      AstConcrete (RepF _ i) -> shows $ unRepN i
      _ -> printAstAux cfgOld d t
    _ -> let cfg = cfgOld {representsIntIndex = False}
         in printAstAux cfg d t
  else printAstAux cfgOld d t

-- Precedences used are as in Haskell.
printAstAux :: forall s y ms. AstSpan s
            => PrintConfig -> Int -> AstTensor ms s y -> ShowS
printAstAux cfg d = \case
  AstPair t1 t2 ->
    showParen (d > 10)
    $ showString "tpair ("
      . printAst cfg 0 t1
      . showString ", "
      . printAst cfg 0 t2
      . showString ")"
  AstProject1 t -> printPrefixOp printAst cfg d "tproject1" [t]
  AstProject2 t -> printPrefixOp printAst cfg d "tproject2" [t]
  AstFromVector snat stk l ->
   if loseRoudtrip cfg
   then case stk of
    STKScalar ->
      showParen (d > 10)
      $ showString "tfromVector "
        . (showParen True
           $ showString "fromList "
             . showListWith (printAst cfg 0) (V.toList l))
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
    STKProduct{} ->
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
    STKScalar ->
      printPrefixOp printAst cfg d
                    ("tsum (" ++ show snat ++ ") (" ++ show stk ++ ")") [v]
    STKR{} -> printPrefixOp printAst cfg d "rsum" [v]
    STKS{} -> printPrefixOp printAst cfg d ("ssum @_ @" ++ show (sNatValue snat)) [v]
    STKX{} -> printPrefixOp printAst cfg d ("xsum @_ @" ++ show (sNatValue snat)) [v]
    STKProduct{} ->
      printPrefixOp printAst cfg d
                    ("tsum (" ++ show snat ++ ") (" ++ show stk ++ ")") [v]
  -- This is too common to be verbose even in no loseRoudtrip mode.
  AstReplicate snat stk v -> case stk of
    STKScalar ->
      printPrefixOp
        printAst cfg d
        ("treplicate (" ++ show snat ++ ") (" ++ show stk ++ ")") [v]
    STKR{} -> printPrefixOp printAst cfg d
                            ("rreplicate " ++ show (sNatValue snat)) [v]
    STKS{} -> printPrefixOp printAst cfg d
                            ("sreplicate @_ @" ++ show (sNatValue snat)) [v]
    STKX{} -> printPrefixOp printAst cfg d
                            ("xreplicate @_ @" ++ show (sNatValue snat)) [v]
    STKProduct{} ->
      printPrefixOp
        printAst cfg d
        ("treplicate (" ++ show snat ++ ") (" ++ show stk ++ ")") [v]
  AstMapAccumRDer k bShs eShs f df rf acc0 es ->
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
      . showParen True (shows bShs)
      . showString " "
      . showParen True (shows eShs)
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
  AstMapAccumLDer k bShs eShs f df rf acc0 es ->
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
      . showParen True (shows bShs)
      . showString " "
      . showParen True (shows eShs)
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
  AstApply stk t ll ->
    if loseRoudtrip cfg
    then showParen (d > 9)
         $ printAstHFunOneUnignore cfg 10 t
           . showString " "
           . printAst cfg 11 ll
    else showParen (d > 10)
         $ showString "tApply "
           . showParen True (shows stk)
           . showString " "
           . printAstHFunOneUnignore cfg 10 t
           . showString " "
           . printAst cfg 11 ll
  AstVar ftk var -> printAstVar cfg (ftkToSTK ftk) var
  AstCond b a1 a2 ->
    showParen (d > 10)
    $ showString "ifF "
      . printAstBool cfg 11 b
      . showString " "
      . printAst cfg 11 a1
      . showString " "
      . printAst cfg 11 a2
  AstBuild1 k stk (var, v) ->
   if loseRoudtrip cfg
   then
    showParen (d > 10)
    $ showString "tbuild1 "
      . shows k
      . showString " "
      . (showParen True
         $ showString "\\"
           . printAstIntVar cfg var
           . showString " -> "
           . printAst cfg 0 v)
   else
    showParen (d > 10)
    $ showString "tbuild1 "
      . shows k
      . showString " "
      . showParen True (shows stk)
      . showString " "
      . (showParen True
         $ showString "\\"
           . printAstIntVar cfg var
           . showString " -> "
           . printAst cfg 0 v)
  AstConcrete repF ->
    if loseRoudtrip cfg
    then case repF of
      RepF FTKScalar _ -> shows repF
      RepF (FTKR ZSR FTKScalar) a ->
        showParen (d > 10)
        $ showString "rscalar "
          . shows (Nested.runScalar $ unRepN a)
      RepF (FTKR _ FTKScalar) _ ->
        showParen (d > 10)
        $ showString "rconcrete "
          . (showParen True
             $ shows repF)
      RepF (FTKS ZSS FTKScalar) a ->
        showParen (d > 10)
        $ showString "sscalar "
          . shows (Nested.sunScalar $ unRepN a)
      RepF (FTKS _ FTKScalar) _ ->
        showParen (d > 10)
        $ showString "sconcrete "
          . (showParen True
             $ shows repF)
      RepF (FTKX ZSX FTKScalar) a ->
        showParen (d > 10)
        $ showString "xscalar "
          . shows (Nested.munScalar $ unRepN a)
      RepF (FTKX _ FTKScalar) _ ->
        showParen (d > 10)
        $ showString "xconcrete "
          . (showParen True
             $ shows repF)
      RepF ftk _ ->
        showParen (d > 10)
        $ showString ("tconcrete (" ++ show ftk ++ ") ")
          . (showParen True
             $ shows repF)
    else case repF of
      RepF FTKScalar _ -> shows repF
      RepF (FTKR ZSR FTKScalar) a ->
        showParen (d > 10)
        $ showString "rscalar "
          . shows (Nested.runScalar $ unRepN a)
      RepF (FTKS ZSS FTKScalar) a ->
        showParen (d > 10)
        $ showString "sscalar "
          . shows (Nested.sunScalar $ unRepN a)
      RepF (FTKX ZSX FTKScalar) a ->
        showParen (d > 10)
        $ showString "xscalar "
          . shows (Nested.munScalar $ unRepN a)
      RepF ftk _ ->
        showParen (d > 10)
        $ showString ("tconcrete (" ++ show ftk ++ ") ")
          . (showParen True
             $ shows repF)
  t@(AstLet var0 u0 v0) ->
    if loseRoudtrip cfg
    then let collect :: AstTensor AstMethodLet s y -> ([(ShowS, ShowS)], ShowS)
             collect (AstLet var u v) =
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
  AstShare var v ->
    showParen (d > 10)
    $ showString "rshare "
      . printAstVar cfg (ftkToSTK (ftkAst v)) var
      . showString " "
      . printAst cfg 11 v
  AstToShare v -> printAstAux cfg d v  -- ignored

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
  AstSumOfList (left :| args) ->
    let rs = map (\arg -> showString " + " . printAst cfg 7 arg) args
    in showParen (d > 6)
       $ printAst cfg 7 left
         . foldr (.) id rs

  AstN1K opCode u -> printAstN1R printAst cfg d opCode u
  AstN2K opCode u v -> printAstN2R printAst cfg d opCode u v
  AstR1K opCode u -> printAstR1R printAst cfg d opCode u
  AstR2K opCode u v -> printAstR2R printAst cfg d opCode u v
  AstI2K opCode u v -> printAstI2R printAst cfg d opCode u v
  AstFloorK v ->
    printPrefixOp printAst cfg d "kfloor" [v]
  AstFromIntegralK v ->
    printPrefixOp printAst cfg d "kfromIntegral" [v]
  AstCastK v ->
    printPrefixOp printAst cfg d "kcast" [v]

  AstN1S opCode u -> printAstN1R printAst cfg d opCode u
  AstN2S opCode u v -> printAstN2R printAst cfg d opCode u v
  AstR1S opCode u -> printAstR1R printAst cfg d opCode u
  AstR2S opCode u v -> printAstR2R printAst cfg d opCode u v
  AstI2S opCode u v -> printAstI2R printAst cfg d opCode u v
  AstFloorS a ->  printPrefixOp printAst cfg d "sfloor" [a]
  AstFromIntegralS a ->
    printPrefixOp printAst cfg d "sfromIntegral" [a]
  AstCastS v -> printPrefixOp printAst cfg d "scast" [v]

  AstIndexS _ v ix ->
    showParen (d > 9)
    $ printAst cfg 10 v
      . showString " !$ "
      . showListWith (printAstInt cfg 0) (Foldable.toList ix)
  AstScatterS _ v (ZS, ix) ->
    showParen (d > 9)
    $ showString "soneHot "
      . printAst cfg 11 v
      . showString " "
      . showListWith (printAstInt cfg 0) (Foldable.toList ix)
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
           . showListWith (printAstInt cfg 0) (Foldable.toList ix))
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
           . showListWith (printAstInt cfg 0) (Foldable.toList ix))
  AstGatherS _ v (ZS, ix) ->
    showParen (d > 9)
    $ printAst cfg 10 v
      . showString " !$ "
      . showListWith (printAstInt cfg 0) (Foldable.toList ix)
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
           . showListWith (printAstInt cfg 0) (Foldable.toList ix))
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
           . showListWith (printAstInt cfg 0) (Foldable.toList ix))
  AstMinIndexS a -> printPrefixOp printAst cfg d "sminIndex" [a]
  AstMaxIndexS a -> printPrefixOp printAst cfg d "smaxIndex" [a]
  AstIotaS snat ->
    showParen (d > 10)
    $ showString ("siota (" ++ show snat ++ ")")
  AstAppendS x y ->
    -- x and y have different types, unlike in AstAppend, so we
    -- have to inline printPrefixOp:
    let rs = [ showString " " . printAst cfg 11 x
             , showString " " . printAst cfg 11 y ]
    in showParen (d > 10)
       $ showString "sappend"
         . foldr (.) id rs
  AstSliceS _ _ _ v -> printPrefixOp printAst cfg d "sslice" [v]
  AstReverseS v -> printPrefixOp printAst cfg d "sreverse" [v]
  AstTransposeS (SNat' @1 `PCons` SNat' @0 `PCons` PNil) v ->
    printPrefixOp printAst cfg d "str" [v]
  AstTransposeS perm v ->
   if loseRoudtrip cfg
   then printPrefixOp printAst cfg d
                      ("stranspose @_ @" ++ show (permToList perm)) [v]
   else printPrefixOp
          printAst cfg d
         ("ttranspose (makePerm @" ++ show (permToList perm) ++ ")") [v]
  AstReshapeS _ v ->
    printPrefixOp printAst cfg d "sreshape" [v]
  AstZipS v -> printPrefixOp printAst cfg d "szip" [v]
  AstUnzipS v -> printPrefixOp printAst cfg d "sunzip" [v]
  AstNestS _ _ v ->
    printPrefixOp printAst cfg d "snestS" [v]
  AstUnNestS v -> printPrefixOp printAst cfg d "sunNestS" [v]

  AstFromS stkz v ->
    case stkz of
      STKScalar -> printPrefixOp printAst cfg d "kfromS" [v]
      STKR{} -> printPrefixOp printAst cfg d "rfromS" [v]
      STKX{} -> printPrefixOp printAst cfg d "xfromS" [v]
      _ -> printPrefixOp printAst cfg d "tfromS" [v]
  AstSFromK t -> printPrefixOp printAst cfg d "sfromK" [t]
  AstSFromR _ v -> printPrefixOp printAst cfg d "sfromR" [v]
  AstSFromX _ v -> printPrefixOp printAst cfg d "sfromX" [v]

  AstReplicate0NS _sh v ->
    printPrefixOp printAst cfg d "sreplicate0N" [v]
  AstSum0S v ->
    printPrefixOp printAst cfg d "ssum0" [v]
  AstDot0S u v ->
    printPrefixOp printAst cfg d "sdot0" [u, v]
  AstDot1InS SNat SNat u v ->
    printPrefixOp printAst cfg d "ssdot1In" [u, v]
  AstMatvecmulS SNat SNat u v ->
    showParen (d > 10)
    $ showString "smatvecmul "
      . printAst cfg 11 u
      . showString " "
      . printAst cfg 11 v
  AstMatmul2S SNat SNat SNat u v ->
    showParen (d > 10)
    $ showString "smatmul2 "
      . printAst cfg 11 u
      . showString " "
      . printAst cfg 11 v

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

printAstHFun :: PrintConfig -> Int -> AstHFun x y -> ShowS
printAstHFun cfg d = \case
  AstLambda (var, ftk, l) ->
    if loseRoudtrip cfg
    then if ignoreNestedLambdas cfg
         then showString "<lambda>"
         else showParen (d > 0)
              $ showString "\\"
                . printAstVar cfg (ftkToSTK ftk) var
                . showString " -> "
                . printAst cfg 0 l
    else showParen (d > 0)
         $ {- showString "tlambda $ "  -- TODO: enable for full roundtrip
           . -}
           showString "\\"
           . printAstVar cfg (ftkToSTK ftk) var
           . showString " -> "
           . printAst cfg 0 l

printAstHFunOneUnignore :: PrintConfig -> Int -> AstHFun x y -> ShowS
printAstHFunOneUnignore cfg d = \case
  AstLambda (var, ftk, l) ->
    if loseRoudtrip cfg
    then showParen (d > 0)
         $ showString "\\"
           . printAstVar cfg (ftkToSTK ftk) var
           . showString " -> "
           . printAst cfg 0 l
    else showParen (d > 0)
         $ {- showString "tlambda $ "  -- TODO: enable for full roundtrip
           . -}
           showString "\\"
           . printAstVar cfg (ftkToSTK ftk) var
           . showString " -> "
           . printAst cfg 0 l

printAstBool :: PrintConfig -> Int -> AstBool ms -> ShowS
printAstBool cfg d = \case
  AstBoolNot u -> printPrefixOp printAstBool cfg d "notB" [u]
  AstB2 opCode arg1 arg2 -> printAstB2 cfg d opCode arg1 arg2
  AstBoolConst b -> showString $ if b then "true" else "false"
  AstRelK opCode arg1 arg2 -> printAstRelOp printAst cfg d opCode arg1 arg2
  AstRelS opCode arg1 arg2 -> printAstRelOp printAst cfg d opCode arg1 arg2

printAstN1R :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCodeNum1 -> a -> ShowS
printAstN1R pr cfg d opCode u = case opCode of
  NegateOp -> printPrefixOp pr cfg d "negate" [u]
  AbsOp -> printPrefixOp pr cfg d "abs" [u]
  SignumOp -> printPrefixOp pr cfg d "signum" [u]

printAstN2R :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCodeNum2 -> a -> a -> ShowS
printAstN2R pr cfg d opCode u v = case opCode of
  MinusOp -> printBinaryOp pr cfg d u (6, " - ") v
  TimesOp -> printBinaryOp pr cfg d u (7, " * ") v

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
  DivideOp -> printBinaryOp pr cfg d u (7, " / ") v
  PowerOp -> printBinaryOp pr cfg d u (8, " ** ") v
  LogBaseOp -> printPrefixOp pr cfg d "logBase" [u, v]
  Atan2Op -> printPrefixOp pr cfg d "atan2F" [u, v]

printAstI2R :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCodeIntegral2 -> a -> a -> ShowS
printAstI2R pr cfg d opCode u v = case opCode of
  QuotOp -> printPrefixOp pr cfg d "quotF" [u, v]
  RemOp -> printPrefixOp pr cfg d "remF" [u, v]

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

printAstB2
  :: PrintConfig -> Int -> OpCodeBool -> AstBool ms -> AstBool ms -> ShowS
printAstB2 cfg d opCode arg1 arg2 = case opCode of
  AndOp -> printBinaryOp printAstBool cfg d arg1 (3, " &&* ") arg2
  OrOp -> printBinaryOp printAstBool cfg d arg1 (2, " ||* ") arg2

printAstRelOp :: (PrintConfig -> Int -> a -> ShowS)
              -> PrintConfig -> Int -> OpCodeRel -> a -> a
              -> ShowS
{-# INLINE printAstRelOp #-}
printAstRelOp pr cfg d opCode u v = case opCode of
  EqOp -> printBinaryOp pr cfg d u (4, " ==. ") v
  NeqOp -> printBinaryOp pr cfg d u (4, " /=. ") v
  LeqOp -> printBinaryOp pr cfg d u (4, " <=. ") v
  GeqOp -> printBinaryOp pr cfg d u (4, " >=. ") v
  LsOp -> printBinaryOp pr cfg d u (4, " <. ") v
  GtOp -> printBinaryOp pr cfg d u (4, " >. ") v


-- * Pretty-printing terms in a few useful configurations

printAstVarName :: KnownSTK y
                => IntMap String -> AstVarName s y -> String
printAstVarName renames var =
  printAstVar (defaulPrintConfig False renames) knownSTK var ""

printAstSimple :: AstSpan s
               => IntMap String -> AstTensor ms s y -> String
printAstSimple renames t = printAst (defaulPrintConfig False renames) 0 t ""

printAstPretty :: AstSpan s
               => IntMap String -> AstTensor ms s y -> String
printAstPretty renames t = printAst (defaulPrintConfig True renames) 0 t ""

printAstPrettyButNested :: AstSpan s
                        => IntMap String -> AstTensor ms s y -> String
printAstPrettyButNested renames t =
  printAst (defaulPrintConfig2 True False renames) 0 t ""

printArtifactSimple
  :: forall x z. KnownSTK x
  => IntMap String -> AstArtifactRev x z -> String
printArtifactSimple renames !AstArtifactRev{..} =
  withKnownSTK (adSTK $ ftkToSTK (ftkAst artPrimalRev)) $
  let !varsPP =
        [ printAstVarName renames artVarDtRev
        , printAstVarName renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimple renames artDerivativeRev

printArtifactPretty
  :: forall x z. KnownSTK x
  => IntMap String -> AstArtifactRev x z -> String
printArtifactPretty renames !AstArtifactRev{..} =
  withKnownSTK (adSTK $ ftkToSTK (ftkAst artPrimalRev)) $
  let varsPP =
        [ printAstVarName renames artVarDtRev
        , printAstVarName renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPretty renames artDerivativeRev

printArtifactPrimalSimple
  :: forall x z. KnownSTK x
  => IntMap String -> AstArtifactRev x z -> String
printArtifactPrimalSimple renames !AstArtifactRev{..} =
  "\\" ++ printAstVarName renames artVarDomainRev
       ++ " -> " ++ printAstSimple renames artPrimalRev

printArtifactPrimalPretty
  :: forall x z. KnownSTK x
  => IntMap String -> AstArtifactRev x z -> String
printArtifactPrimalPretty renames !AstArtifactRev{..} =
  "\\" ++ printAstVarName renames artVarDomainRev
       ++ " -> " ++ printAstPretty renames artPrimalRev
