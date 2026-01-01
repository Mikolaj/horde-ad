{-# LANGUAGE TemplateHaskellQuotes #-}
module Data.Array.Strided.Arith.Internal.Lists.TH where

import Control.Monad
import Control.Monad.IO.Class
import Data.Maybe
import Foreign.C.Types
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Text.Read


data OpKind = Binop | IBinop | FBinop | Unop | FUnop | Redop
  deriving (Show, Eq)

readArithLists :: OpKind
               -> (String -> Int -> String -> Q a)
               -> ([a] -> Q r)
               -> Q r
readArithLists targetkind fop fcombine = do
  addDependentFile "cbits/arith_lists.h"
  lns <- liftIO $ lines <$> readFile "cbits/arith_lists.h"

  mvals <- forM lns $ \line -> do
    if null (dropWhile (== ' ') line)
      then return Nothing
      else do let (kind, name, num, aux) = parseLine line
              if kind == targetkind
                then Just <$> fop name num aux
                else return Nothing

  fcombine (catMaybes mvals)
  where
    parseLine s0
      | ("LIST_", s1) <- splitAt 5 s0
      , (kindstr, '(' : s2) <- break (== '(') s1
      , (f1, ',' : s3) <- parseField s2
      , (f2, ',' : s4) <- parseField s3
      , (f3, ')' : _) <- parseField s4
      , Just kind <- parseKind kindstr
      , let name = f1
      , Just num <- readMaybe f2
      , let aux = f3
      = (kind, name, num, aux)
      | otherwise
      = error $ "readArithLists: unrecognised line in cbits/arith_lists.h: " ++ show s0

    parseField s = break (`elem` ",)") (dropWhile (== ' ') s)

    parseKind "BINOP" = Just Binop
    parseKind "IBINOP" = Just IBinop
    parseKind "FBINOP" = Just FBinop
    parseKind "UNOP" = Just Unop
    parseKind "FUNOP" = Just FUnop
    parseKind "REDOP" = Just Redop
    parseKind _ = Nothing

genArithDataType :: OpKind -> String -> Q [Dec]
genArithDataType kind dtname = do
  cons <- readArithLists kind
            (\name _num _ -> return $ NormalC (mkName name) [])
            return
  return [DataD [] (mkName dtname) [] Nothing cons [DerivClause Nothing [ConT ''Show, ConT ''Enum, ConT ''Bounded]]]

genArithNameFun :: OpKind -> Name -> String -> (String -> String) -> Q [Dec]
genArithNameFun kind dtname funname nametrans = do
  clauses <- readArithLists kind
               (\name _num _ -> return (Clause [ConP (mkName name) [] []]
                                               (NormalB (LitE (StringL (nametrans name))))
                                               []))
               return
  return [SigD (mkName funname) (ArrowT `AppT` ConT dtname `AppT` ConT ''String)
         ,FunD (mkName funname) clauses]

genArithEnumFun :: OpKind -> Name -> String -> Q [Dec]
genArithEnumFun kind dtname funname = do
  clauses <- readArithLists kind
               (\name num _ -> return (Clause [ConP (mkName name) [] []]
                                              (NormalB (LitE (IntegerL (fromIntegral num))))
                                              []))
               return
  return [SigD (mkName funname) (ArrowT `AppT` ConT dtname `AppT` ConT ''CInt)
         ,FunD (mkName funname) clauses]
