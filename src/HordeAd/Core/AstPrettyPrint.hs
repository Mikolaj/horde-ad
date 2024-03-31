{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | Pretty-printing of AST of the code to be differentiated or resulting
-- from the differentiation.
module HordeAd.Core.AstPrettyPrint
  ( -- * Pretty-print variables
    printAstVarName, printAstVarNameS, printAstDynamicVarNameBrief
  , printAstDynamicVarName
  , printAstIntVarName
    -- * User-friendly API for pretty-printing AST terms
  , printAstSimple, printAstPretty, printAstPrettyButNested
  , printAstSimpleS, printAstPrettyS, printAstPrettyButNestedS
  , printAstHVectorSimple, printAstHVectorPretty, printAstHVectorPrettyButNested
  , printGradient6Simple, printGradient6Pretty
  , printPrimal6Simple, printPrimal6Pretty
  , printArtifactFwdSimple, printArtifactFwdPretty
  ) where

import Prelude

import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.List (intersperse)
import           Data.Proxy (Proxy (Proxy))
import           Data.Strict.IntMap (IntMap)
import qualified Data.Strict.IntMap as IM
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, sameNat)
import           Type.Reflection (typeRep)

import           HordeAd.Core.Ast
import           HordeAd.Core.HVector
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances (sameShape)
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

-- * Pretty-printing setup and checks

-- Modeled after https://github.com/VMatthijs/CHAD/blob/755fc47e1f8d1c3d91455f123338f44a353fc265/src/TargetLanguage.hs#L335.

-- TODO: ensure that terms roundtrip if neither loseRoudtrip
-- nor ignoreNestedLambdas is set.
-- Ideally, it would also preserve sharing.
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

areAllArgsInts :: AstRanked s r n -> Bool
areAllArgsInts = \case
  -- A heuristics for whether all the arguments are still Int64 rank 0 tensors
  -- morally representing integer indexes. This mostly just rules out
  -- rank > 0, but also a likely float, as in the argument of AstFloor,
  -- or a likely dual number. There is an anavoidable ambiguity
  -- and so also aribtrary choices in resolving it.
  AstVar{} -> True
  AstLet{} -> True  -- too early to tell, but displays the same
  AstShare{} -> True  -- too early to tell
  AstCond{} -> True  -- too early to tell
  AstMinIndex{} -> False
  AstMaxIndex{} -> False
  AstFloor{} -> False
  AstIota -> False
  AstN1{} -> True  -- has to keep rank and scalar, so it's ints
  AstN2{} -> True  -- has to keep rank and scalar
  AstR1{} -> True  -- has to keep rank and scalar
  AstR2{} -> True  -- has to keep rank and scalar
  AstI2{} -> True  -- has to keep rank and scalar
  AstSumOfList{} -> True  -- has to keep rank and scalar
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
  AstConst{} -> True
  AstProject{} -> True  -- too early to tell
  AstLetHVectorIn{} -> True  -- too early to tell
  AstLetHFunIn{} -> True  -- too early to tell
  AstRFromS{} -> False
  AstConstant{} -> True  -- the argument is emphatically a primal number; fine
  AstPrimalPart{} -> False
  AstDualPart{} -> False
  AstD{} -> False  -- dual number


-- * Pretty-print variables

printAstVarId :: String -> PrintConfig -> AstVarId -> ShowS
printAstVarId prefix cfg var =
  let n = fromEnum var - 100000000
  in showString $ case IM.lookup n (varRenames cfg) of
    Just name | name /= "" -> name
    _ -> prefix ++ show n

printAstVarN :: Int -> PrintConfig -> AstVarName f r y -> ShowS
printAstVarN n cfg (AstVarName varId) =
  let prefix = case n of
        0 -> "x"
        1 -> "v"
        2 -> "m"
        3 -> "t"
        4 -> "u"
        _ -> "w"
  in printAstVarId prefix cfg varId

printAstVar :: forall n s r. KnownNat n
            => PrintConfig -> AstVarName (AstRanked s) r n -> ShowS
printAstVar = printAstVarN (valueOf @n)

printAstVarS :: forall sh s r. Sh.Shape sh
             => PrintConfig -> AstVarName (AstShaped s) r sh -> ShowS
printAstVarS = printAstVarN (length (Sh.shapeT @sh))

printAstIntVar :: PrintConfig -> IntVarName -> ShowS
printAstIntVar cfg (AstVarName varId) = printAstVarId "i" cfg varId

printAstFunVar :: PrintConfig -> AstVarId -> ShowS
printAstFunVar = printAstVarId "f"

printAstVarFromLet
  :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
  => AstRanked s r n -> PrintConfig -> AstVarName (AstRanked s) r n -> ShowS
printAstVarFromLet u cfg var =
  if representsIntIndex cfg && areAllArgsInts u
  then case isRankedInt u of
    Just Refl ->  -- the heuristics may have been correct
      printAstIntVar cfg var
    _ ->  -- the heuristics failed
      printAstVar cfg var
  else printAstVar cfg var

printAstIntVarName :: IntMap String -> IntVarName -> String
printAstIntVarName renames var =
  printAstIntVar (defaulPrintConfig False renames) var ""

printAstVarName :: KnownNat n
                => IntMap String -> AstVarName (AstRanked s) r n
                -> String
printAstVarName renames var =
  printAstVar (defaulPrintConfig False renames) var ""

printAstVarNameS :: Sh.Shape sh
                 => IntMap String -> AstVarName (AstShaped s) r sh
                 -> String
printAstVarNameS renames var =
  printAstVarS (defaulPrintConfig False renames) var ""

printAstDynamicVarNameBrief :: IntMap String -> AstDynamicVarName -> String
printAstDynamicVarNameBrief renames (AstDynamicVarName @ty @r @sh varId) =
  printAstVarNameS renames (AstVarName @[Nat] @_ @r @sh varId)

printAstDynamicVarName :: IntMap String -> AstDynamicVarName -> String
printAstDynamicVarName renames var@(AstDynamicVarName @ty @r @sh _varId) =
  printAstDynamicVarNameBrief renames var
  ++ " @" ++ show (typeRep @ty)
  ++ " @" ++ show (typeRep @r)
  ++ " @" ++ show (Sh.shapeT @sh)

printAstDynamicVarNameCfg :: PrintConfig -> AstDynamicVarName -> String
printAstDynamicVarNameCfg cfg =
  if loseRoudtrip cfg
  then printAstDynamicVarNameBrief (varRenames cfg)
  else printAstDynamicVarName (varRenames cfg)


-- * General pretty-printing of AST terms

printAstInt :: PrintConfig -> Int -> AstInt -> ShowS
printAstInt cfgOld d t =
  let cfg = cfgOld {representsIntIndex = True}
  in printAst cfg d t

printAst :: forall n s r. (GoodScalar r, KnownNat n, AstSpan s)
         => PrintConfig -> Int -> AstRanked s r n -> ShowS
printAst cfgOld d t =
  if representsIntIndex cfgOld
  then case isRankedInt t of
    Just Refl ->  -- the heuristics may have been correct
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
  t@(AstLet var0 u0 v0) ->
    if loseRoudtrip cfg
    then let collect :: AstRanked s r n -> ([(ShowS, ShowS)], ShowS)
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
      $ showString "rlet "
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
      . printAstVar cfg var
      . showString " "
      . printAst cfg 11 v
  AstCond b a1 a2 ->
    showParen (d > 10)
    $ showString "ifF "
      . printAstBool cfg 11 b
      . showString " "
      . printAst cfg 11 a1
      . showString " "
      . printAst cfg 11 a2
  AstMinIndex a ->
    printPrefixOp printAst cfg d "rminIndex" [a]
  AstMaxIndex a ->
    printPrefixOp printAst cfg d "rmaxIndex" [a]
  AstFloor a ->
    printPrefixOp printAst cfg d "rfloor" [a]
  AstIota -> showString "riota"
  AstN1 opCode u -> printAstN1 printAst cfg d opCode u
  AstN2 opCode u v -> printAstN2 printAst cfg d opCode u v
  AstR1 opCode u -> printAstR1 printAst cfg d opCode u
  AstR2 opCode u v -> printAstR2 printAst cfg d opCode u v
  AstI2 opCode u v -> printAstI2 printAst cfg d opCode u v
  AstSumOfList [] -> error "printAst: empty AstSumOfList"
  AstSumOfList (left : args) ->
    let rs = map (\arg -> showString " + " . printAst cfg 7 arg) args
    in showParen (d > 6)
       $ printAst cfg 7 left
         . foldr (.) id rs
  AstIndex v ix ->
    showParen (d > 9)
    $ printAst cfg 10 v
      . showString " ! "
      . showListWith (printAstInt cfg 0) (indexToList ix)
  AstSum v -> printPrefixOp printAst cfg d "rsum" [v]
  AstScatter sh v (vars, ix) ->
    showParen (d > 10)
    $ showString ("rscatter " ++ show sh ++ " ")
      . printAst cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (sizedToList vars)
           . showString " -> "
           . showListWith (printAstInt cfg 0) (indexToList ix))
  AstFromList l ->
    showParen (d > 10)
    $ showString "rfromList "
      . showListWith (printAst cfg 0) l
  AstFromVector l ->
    showParen (d > 10)
    $ showString "rfromVector "
      . (showParen True
         $ showString "fromList "
           . showListWith (printAst cfg 0) (V.toList l))
  AstReplicate k v -> printPrefixOp printAst cfg d ("rreplicate " ++ show k) [v]
  AstAppend x y -> printPrefixOp printAst cfg d "rappend" [x, y]
  AstSlice i n v -> printPrefixOp printAst cfg d
                                  ("rslice " ++ show i ++ " " ++ show n) [v]
  AstReverse v -> printPrefixOp printAst cfg d "rreverse" [v]
  AstTranspose perm v ->
    printPrefixOp printAst cfg d ("rtranspose " ++ show perm) [v]
  AstReshape sh v ->
    printPrefixOp printAst cfg d ("rreshape " ++ show sh) [v]
  AstBuild1 k (var, v) ->
    showParen (d > 10)
    $ showString "rbuild1 "
      . shows k
      . showString " "
      . (showParen True
         $ showString "\\"
           . printAstIntVar cfg var
           . showString " -> "
           . printAst cfg 0 v)
  AstGather sh v (vars, ix) ->
    showParen (d > 10)
    $ showString ("rgather " ++ show sh ++ " ")
      . printAst cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (sizedToList vars)
           . showString " -> "
           . showListWith (printAstInt cfg 0) (indexToList ix))
  AstCast v -> printPrefixOp printAst cfg d "rcast" [v]
  AstFromIntegral a ->
    printPrefixOp printAst cfg d "rfromIntegral" [a]
  AstConst a ->
    case sameNat (Proxy @n) (Proxy @0) of
      Just Refl -> shows $ OR.unScalar a
      _ -> showParen (d > 10)
           $ showString "rconst "
             . (showParen True
                $ shows a)
  AstProject l p ->
    showParen (d > 10)
    $ showString "rproject "  -- fake, no such surface syntax
      . printAstHVector cfg 0 l
      . showString " "
      . shows p
  AstLetHVectorIn vars l v ->
    if loseRoudtrip cfg
    then
      showParen (d > 10)
      $ showString "let "
        . showListWith (showString
                        . printAstDynamicVarName (varRenames cfg)) vars
        . showString " = "
        . printAstHVector cfg 0 l
        . showString " in "
        . printAst cfg 0 v
    else
      showParen (d > 10)
      $ showString "rletHVectorIn "
        . printAstHVector cfg 11 l
        . showString " "
        . (showParen True
           $ showString "\\"
             . showListWith (showString
                             . printAstDynamicVarName (varRenames cfg)) vars
             . showString " -> "
             . printAst cfg 0 v)
        -- TODO: this does not roundtrip yet
  AstLetHFunIn var f v ->
    if loseRoudtrip cfg
    then
      showParen (d > 10)
      $ showString "let "
        . printAstFunVar cfg var
        . showString " = "
        . printAstHFun cfg 0 f
        . showString " in "
        . printAst cfg 0 v
    else
      showParen (d > 10)
      $ showString "rletHFunIn "
        . printAstHFun cfg 11 f
        . showString " "
        . (showParen True
           $ showString "\\"
             . printAstFunVar cfg var
             . showString " -> "
             . printAst cfg 0 v)
        -- TODO: this does not roundtrip yet
  AstRFromS v -> printPrefixOp printAstS cfg d "rfromS" [v]
  AstConstant a -> if loseRoudtrip cfg
                   then printAst cfg d a
                   else printPrefixOp printAst cfg d "rconstant" [a]
  AstPrimalPart a -> printPrefixOp printAst cfg d "rprimalPart" [a]
  AstDualPart a -> printPrefixOp printAst cfg d "rdualPart" [a]
  AstD u u' -> printPrefixBinaryOp printAst printAst cfg d "rD" u u'

printAstS :: forall sh s r. (GoodScalar r, Sh.Shape sh, AstSpan s)
          => PrintConfig -> Int -> AstShaped s r sh -> ShowS
printAstS cfg d = \case
  AstVarS var -> printAstVarS cfg var
  t@(AstLetS var0 u0 v0) ->
    if loseRoudtrip cfg
    then let collect :: AstShaped s r sh -> ([(ShowS, ShowS)], ShowS)
             collect (AstLetS var u v) =
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
  AstShareS var v ->
    showParen (d > 10)
    $ showString "sshare "
      . printAstVarS cfg var
      . showString " "
      . printAstS cfg 11 v
  AstCondS b a1 a2 ->
    showParen (d > 10)
    $ showString "ifF "
      . printAstBool cfg 11 b
      . showString " "
      . printAstS cfg 11 a1
      . showString " "
      . printAstS cfg 11 a2
  AstMinIndexS a -> printPrefixOp printAstS cfg d "sminIndex" [a]
  AstMaxIndexS a -> printPrefixOp printAstS cfg d "smaxIndex" [a]
  AstFloorS a ->  printPrefixOp printAstS cfg d "sfloor" [a]
  AstIotaS -> showString "siota"
  AstN1S opCode u -> printAstN1 printAstS cfg d opCode u
  AstN2S opCode u v -> printAstN2 printAstS cfg d opCode u v
  AstR1S opCode u -> printAstR1 printAstS cfg d opCode u
  AstR2S opCode u v -> printAstR2 printAstS cfg d opCode u v
  AstI2S opCode u v -> printAstI2 printAstS cfg d opCode u v
  AstSumOfListS [] -> error "printAst: empty AstSumOfList"
  AstSumOfListS (left : args) ->
    let rs = map (\arg -> showString " + " . printAstS cfg 7 arg) args
    in showParen (d > 6)
       $ printAstS cfg 7 left
         . foldr (.) id rs
  AstIndexS v ix ->
    showParen (d > 9)
    $ printAstS cfg 10 v
      . showString " !$ "
      . showListWith (printAstInt cfg 0) (ShapedList.indexToList ix)
  AstSumS v -> printPrefixOp printAstS cfg d "ssum" [v]
  AstScatterS v (vars, ix) ->
    showParen (d > 10)
    $ showString "sscatter "
      . printAstS cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (ShapedList.sizedToList vars)
           . showString " -> "
           . showListWith (printAstInt cfg 0) (ShapedList.indexToList ix))
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
    $ showString "sgather "
      . printAstS cfg 11 v
      . showString " "
      . (showParen True
         $ showString "\\"
           . showListWith (printAstIntVar cfg)
                          (ShapedList.sizedToList vars)
           . showString " -> "
           . showListWith (printAstInt cfg 0) (ShapedList.indexToList ix))
  AstCastS v -> printPrefixOp printAstS cfg d "scast" [v]
  AstFromIntegralS a ->
    printPrefixOp printAstS cfg d "sfromIntegral" [a]
  AstConstS @sh2 a ->
    case sameShape @sh @'[] of
      Just Refl -> shows $ OS.unScalar a
      _ -> showParen (d > 10)
           $ showString ("sconst @" ++ show (Sh.shapeT @sh2) ++ " ")
             . (showParen True
                $ shows a)
  AstProjectS l p ->
    showParen (d > 10)
    $ showString "sproject "  -- fake, no such surface syntax
      . printAstHVector cfg 0 l
      . showString " "
      . shows p
  AstLetHVectorInS vars l v ->
    if loseRoudtrip cfg
    then
      showParen (d > 10)
      $ showString "let "
        . showListWith (showString
                        . printAstDynamicVarName (varRenames cfg)) vars
        . showString " = "
        . printAstHVector cfg 0 l
        . showString " in "
        . printAstS cfg 0 v
    else
      showParen (d > 10)
      $ showString "sletHVectorIn "
        . printAstHVector cfg 11 l
        . showString " "
        . (showParen True
           $ showString "\\"
             . showListWith (showString
                             . printAstDynamicVarName (varRenames cfg)) vars
             . showString " -> "
             . printAstS cfg 0 v)
        -- TODO: this does not roundtrip yet
  AstLetHFunInS var f v ->
    if loseRoudtrip cfg
    then
      showParen (d > 10)
      $ showString "let "
        . printAstFunVar cfg var
        . showString " = "
        . printAstHFun cfg 0 f
        . showString " in "
        . printAstS cfg 0 v
    else
      showParen (d > 10)
      $ showString "sletHFunIn "
        . printAstHFun cfg 11 f
        . showString " "
        . (showParen True
           $ showString "\\"
             . printAstFunVar cfg var
             . showString " -> "
             . printAstS cfg 0 v)
        -- TODO: this does not roundtrip yet
  AstSFromR v -> printPrefixOp printAst cfg d "sfromR" [v]
  AstConstantS a -> if loseRoudtrip cfg
                    then printAstS cfg d a
                    else printPrefixOp printAstS cfg d "sconstant" [a]
  AstPrimalPartS a -> printPrefixOp printAstS cfg d "sprimalPart" [a]
  AstDualPartS a -> printPrefixOp printAstS cfg d "sdualPart" [a]
  AstDS u u' -> printPrefixBinaryOp printAstS printAstS cfg d "sD" u u'

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

printAstDynamic :: AstSpan s
                => PrintConfig -> Int -> AstDynamic s -> ShowS
printAstDynamic cfg d = \case
  DynamicRanked v -> printPrefixOp printAst cfg d "DynamicRanked" [v]
  DynamicShaped v -> printPrefixOp printAstS cfg d "DynamicShaped" [v]
  DynamicRankedDummy{} -> showString "DynamicRankedDummy"
  DynamicShapedDummy{} -> showString "DynamicShapedDummy"

printAstUnDynamic :: AstSpan s
                  => PrintConfig -> Int -> AstDynamic s -> ShowS
printAstUnDynamic cfg d = \case
  DynamicRanked v -> printAst cfg d v
  DynamicShaped v -> printAstS cfg d v
  DynamicRankedDummy{} -> showString "0"
  DynamicShapedDummy{} -> showString "0"

printHVectorAst :: forall s. AstSpan s
                => PrintConfig -> HVector (AstRanked s) -> ShowS
printHVectorAst cfg l =
  if loseRoudtrip cfg
  then
    showListWith (printAstUnDynamic cfg 0) (V.toList l)
  else
    showParen True
      $ showString "fromList "
        . showListWith (printAstDynamic cfg 0) (V.toList l)

printAstHVector :: forall s. AstSpan s
                => PrintConfig -> Int -> AstHVector s -> ShowS
printAstHVector cfg d = \case
  AstMkHVector l ->
    if loseRoudtrip cfg
    then printHVectorAst cfg l
    else showParen (d > 10)
         $ showString "dmkHVector " . printHVectorAst cfg l
  AstHApply t ll ->
    if loseRoudtrip cfg
    then showParen (d > 9)
         $ printAstHFunOneUnignore cfg 10 t
           . showString " "
           . showListWith (printHVectorAst cfg) ll
    else showParen (d > 10)
         $ showString "dHApply "
           . printAstHFunOneUnignore cfg 10 t
           . showString " "
           . showListWith (printHVectorAst cfg) ll
  AstLetHVectorInHVector vars l v ->
    if loseRoudtrip cfg
    then
      showParen (d > 10)
      $ showString "let "
        . showListWith (showString
                        . printAstDynamicVarName (varRenames cfg)) vars
        . showString " = "
        . printAstHVector cfg 0 l
        . showString " in "
        . printAstHVector cfg 0 v
    else
      showParen (d > 10)
      $ showString "dletHVectorInHVector "
        . printAstHVector cfg 11 l
        . showString " "
        . (showParen True
           $ showString "\\"
             . showListWith (showString
                             . printAstDynamicVarName (varRenames cfg)) vars
             . showString " -> "
             . printAstHVector cfg 0 v)
  AstLetHFunInHVector var f v ->
    if loseRoudtrip cfg
    then
      showParen (d > 10)
      $ showString "let "
        . printAstFunVar cfg var
        . showString " = "
        . printAstHFun cfg 0 f
        . showString " in "
        . printAstHVector cfg 0 v
    else
      showParen (d > 10)
      $ showString "dletHFunInHVector "
        . printAstHFun cfg 11 f
        . showString " "
        . (showParen True
           $ showString "\\"
             . printAstFunVar cfg var
             . showString " -> "
             . printAstHVector cfg 0 v)
        -- TODO: this does not roundtrip yet
  t@(AstLetInHVector var0 u0 v0) ->
    if loseRoudtrip cfg
    then let collect :: AstHVector s -> ([(ShowS, ShowS)], ShowS)
             collect (AstLetInHVector var u v) =
               let name = printAstVarFromLet u cfg var
                   uPP = printAst cfg 0 u
                   (rest, corePP) = collect v
               in ((name, uPP) : rest, corePP)
             collect v = ([], printAstHVector cfg 0 v)
             (pairs, core) = collect t
         in showParen (d > 0)
            $ showString "let "
              . foldr (.) id (intersperse (showString " ; ")
                  [name . showString " = " . uPP | (name, uPP) <- pairs])
              . showString " in "
              . core
    else
      showParen (d > 10)
      $ showString "rletInHVector "
        . printAst cfg 11 u0
        . showString " "
        . (showParen True
           $ showString "\\"
             . printAstVarFromLet u0 cfg var0
             . showString " -> "
             . printAstHVector cfg 0 v0)
  t@(AstLetInHVectorS var0 u0 v0) ->
    if loseRoudtrip cfg
    then let collect :: AstHVector s -> ([(ShowS, ShowS)], ShowS)
             collect (AstLetInHVectorS var u v) =
               let name = printAstVarS cfg var
                   uPP = printAstS cfg 0 u
                   (rest, corePP) = collect v
               in ((name, uPP) : rest, corePP)
             collect v = ([], printAstHVector cfg 0 v)
             (pairs, core) = collect t
         in showParen (d > 0)
            $ showString "let "
              . foldr (.) id (intersperse (showString " ; ")
                  [name . showString " = " . uPP | (name, uPP) <- pairs])
              . showString " in "
              . core
    else
      showParen (d > 10)
      $ showString "sletInHVector "
        . printAstS cfg 11 u0
        . showString " "
        . (showParen True
           $ showString "\\"
             . printAstVarS cfg var0
             . showString " -> "
             . printAstHVector cfg 0 v0)
  AstShareHVector vars l ->
    showParen (d > 10)
    $ showString "dshare "
      . showListWith (showString
                      . printAstDynamicVarName (varRenames cfg)) vars
      . showString " "
      . printAstHVector cfg 11 l
  AstBuildHVector1 k (var, v) ->
    showParen (d > 10)
    $ showString "dbuild1 "
      . showParen True (shows k)
      . showString " "
      . (showParen True
         $ showString "\\"
           . printAstIntVar cfg var
           . showString " -> "
           . printAstHVector cfg 0 v)
  AstMapAccumRDer k _accShs _bShs _eShs f df rf acc0 es ->
    showParen (d > 10)
    $ showString "dmapAccumRDer "
      . showParen True (shows k)
      . showString " "
      . printAstHFun cfg 10 f
      . showString " "
      . printAstHFun cfg 10 df
      . showString " "
      . printAstHFun cfg 01 rf
      . showString " "
      . printAstHVector cfg 0 acc0
      . showString " "
      . printAstHVector cfg 0 es
  AstMapAccumLDer k _accShs _bShs _eShs f df rf acc0 es ->
    showParen (d > 10)
    $ showString "dmapAccumLDer "
      . showParen True (shows k)
      . showString " "
      . printAstHFun cfg 10 f
      . showString " "
      . printAstHFun cfg 10 df
      . showString " "
      . printAstHFun cfg 01 rf
      . showString " "
      . printAstHVector cfg 0 acc0
      . showString " "
      . printAstHVector cfg 0 es

printAstHFun :: PrintConfig -> Int -> AstHFun -> ShowS
printAstHFun cfg d = \case
  AstLambda (vvars, l) ->
    if loseRoudtrip cfg
    then if ignoreNestedLambdas cfg
         then showString "<lambda>"
         else showParen (d > 0)
              $ showString "\\"
                . showCollectionWith "" " " ""
                    (showListWith (showString
                                   . printAstDynamicVarNameCfg cfg)) vvars
                . showString " -> "
                . printAstHVector cfg 0 l
    else showParen (d > 0)
         $ {- showString "dlambda $ "  -- TODO: enable for full roundtrip
           . -}
           showString "\\"
           . showCollectionWith "" " " ""
               (showListWith (showString
                              . printAstDynamicVarNameCfg cfg)) vvars
           . showString " -> "
           . printAstHVector cfg 0 l
  AstVarHFun _shss _shs var -> printAstFunVar cfg var

printAstHFunOneUnignore :: PrintConfig -> Int -> AstHFun -> ShowS
printAstHFunOneUnignore cfg d = \case
  AstLambda (vvars, l) ->
    if loseRoudtrip cfg
    then showParen (d > 0)
         $ showString "\\"
           . showCollectionWith "" " " ""
               (showListWith (showString
                              . printAstDynamicVarNameCfg cfg)) vvars
           . showString " -> "
           . printAstHVector cfg 0 l
    else showParen (d > 0)
         $ {- showString "dlambda $ "  -- TODO: enable for full roundtrip
           . -}
           showString "\\"
           . showCollectionWith "" " " ""
               (showListWith (showString
                              . printAstDynamicVarNameCfg cfg)) vvars
           . showString " -> "
           . printAstHVector cfg 0 l
  AstVarHFun _shss _shs var -> printAstFunVar cfg var

printAstBool :: PrintConfig -> Int -> AstBool -> ShowS
printAstBool cfg d = \case
  AstBoolNot u -> printPrefixOp printAstBool cfg d "notB" [u]
  AstB2 opCode arg1 arg2 -> printAstB2 cfg d opCode arg1 arg2
  AstBoolConst b -> showString $ if b then "true" else "false"
  AstRel opCode arg1 arg2 -> printAstRelOp printAst cfg d opCode arg1 arg2
  AstRelS opCode arg1 arg2 -> printAstRelOp printAstS cfg d opCode arg1 arg2

printAstN1 :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCodeNum1 -> a -> ShowS
printAstN1 pr cfg d opCode u = case opCode of
  NegateOp -> printPrefixOp pr cfg d "negate" [u]
  AbsOp -> printPrefixOp pr cfg d "abs" [u]
  SignumOp -> printPrefixOp pr cfg d "signum" [u]

printAstN2 :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCodeNum2 -> a -> a -> ShowS
printAstN2 pr cfg d opCode u v = case opCode of
  MinusOp -> printBinaryOp pr cfg d u (6, " - ") v
  TimesOp -> printBinaryOp pr cfg d u (7, " * ") v

printAstR1 :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCode1 -> a -> ShowS
printAstR1 pr cfg d opCode u = case opCode of
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

printAstR2 :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCode2 -> a -> a -> ShowS
printAstR2 pr cfg d opCode u v = case opCode of
  DivideOp -> printBinaryOp pr cfg d u (7, " / ") v
  PowerOp -> printBinaryOp pr cfg d u (8, " ** ") v
  LogBaseOp -> printPrefixOp pr cfg d "logBase" [u, v]
  Atan2Op -> printPrefixOp pr cfg d "atan2" [u, v]

printAstI2 :: (PrintConfig -> Int -> a -> ShowS)
           -> PrintConfig -> Int -> OpCodeIntegral2 -> a -> a -> ShowS
printAstI2 pr cfg d opCode u v = case opCode of
  QuotOp -> printPrefixOp pr cfg d "quot" [u, v]
  RemOp -> printPrefixOp pr cfg d "rem" [u, v]

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

printAstB2
  :: PrintConfig -> Int -> OpCodeBool -> AstBool -> AstBool -> ShowS
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


-- * User-friendly API for pretty-printing AST terms

printAstSimple :: (GoodScalar r, KnownNat n, AstSpan s)
               => IntMap String -> AstRanked s r n -> String
printAstSimple renames t = printAst (defaulPrintConfig False renames) 0 t ""

printAstPretty :: (GoodScalar r, KnownNat n, AstSpan s)
               => IntMap String -> AstRanked s r n -> String
printAstPretty renames t = printAst (defaulPrintConfig True renames) 0 t ""

printAstPrettyButNested :: (GoodScalar r, KnownNat n, AstSpan s)
                        => IntMap String -> AstRanked s r n -> String
printAstPrettyButNested renames t =
  printAst (defaulPrintConfig2 True False renames) 0 t ""

printAstSimpleS :: (GoodScalar r, Sh.Shape sh, AstSpan s)
                => IntMap String -> AstShaped s r sh -> String
printAstSimpleS renames t = printAstS (defaulPrintConfig False renames) 0 t ""

printAstPrettyS :: (GoodScalar r, Sh.Shape sh, AstSpan s)
                => IntMap String -> AstShaped s r sh -> String
printAstPrettyS renames t = printAstS (defaulPrintConfig True renames) 0 t ""

printAstPrettyButNestedS :: (GoodScalar r, Sh.Shape sh, AstSpan s)
                         => IntMap String -> AstShaped s r sh -> String
printAstPrettyButNestedS renames t =
  printAstS (defaulPrintConfig2 True False renames) 0 t ""

printAstHVectorSimple :: AstSpan s => IntMap String -> AstHVector s -> String
printAstHVectorSimple renames t =
  printAstHVector (defaulPrintConfig False renames) 0 t ""

printAstHVectorPretty :: AstSpan s => IntMap String -> AstHVector s -> String
printAstHVectorPretty renames t =
  printAstHVector (defaulPrintConfig True renames) 0 t ""

printAstHVectorPrettyButNested
  :: AstSpan s => IntMap String -> AstHVector s -> String
printAstHVectorPrettyButNested renames t =
  printAstHVector (defaulPrintConfig2 True False renames) 0 t ""

printGradient6Simple
  :: IntMap String
  -> AstArtifactRev (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
  -> String
printGradient6Simple renames ((varsDt, vars1), gradient, _) =
  let varsPP = map (printAstDynamicVarNameBrief renames) $ varsDt ++ vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorSimple renames (unAstRawWrap gradient)

printGradient6Pretty
  :: IntMap String
  -> AstArtifactRev (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
  -> String
printGradient6Pretty renames ((varsDt, vars1), gradient, _) =
  let varsPP = map (printAstDynamicVarNameBrief renames) $ varsDt ++ vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorPretty renames (unAstRawWrap gradient)

printPrimal6Simple
  :: IntMap String
  -> AstArtifactRev (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
  -> String
printPrimal6Simple renames ((_, vars1), _, HVectorPseudoTensor primal) =
  let varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorSimple renames (unAstRawWrap primal)

printPrimal6Pretty
  :: IntMap String
  -> AstArtifactRev (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
  -> String
printPrimal6Pretty renames ((_, vars1), _, HVectorPseudoTensor primal) =
  let varsPP = map (printAstDynamicVarNameBrief renames) vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorPretty renames (unAstRawWrap primal)

printArtifactFwdSimple
  :: IntMap String
  -> AstArtifactFwd (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
  -> String
printArtifactFwdSimple renames
                       ((varsDt, vars1),  HVectorPseudoTensor derivative, _) =
  let varsPP = map (printAstDynamicVarNameBrief renames) $ varsDt ++ vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorSimple renames (unAstRawWrap derivative)

printArtifactFwdPretty
  :: IntMap String
  -> AstArtifactFwd (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
  -> String
printArtifactFwdPretty renames
                       ((varsDt, vars1), HVectorPseudoTensor derivative, _) =
  let varsPP = map (printAstDynamicVarNameBrief renames) $ varsDt ++ vars1
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstHVectorPretty renames (unAstRawWrap derivative)
