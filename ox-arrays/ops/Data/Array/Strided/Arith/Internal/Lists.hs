{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Array.Strided.Arith.Internal.Lists where

import Data.Char
import Data.Int
import Language.Haskell.TH

import Data.Array.Strided.Arith.Internal.Lists.TH


data ArithType = ArithType
  { atType :: Name  -- ''Int32
  , atCName :: String  -- "i32"
  }

intTypesList :: [ArithType]
intTypesList =
  [ArithType ''Int8 "i8"
  ,ArithType ''Int16 "i16"
  ,ArithType ''Int32 "i32"
  ,ArithType ''Int64 "i64"
  ]

floatTypesList :: [ArithType]
floatTypesList =
  [ArithType ''Float "float"
  ,ArithType ''Double "double"
  ]

typesList :: [ArithType]
typesList = intTypesList ++ floatTypesList

-- data ArithBOp = BO_ADD | BO_SUB | BO_MUL deriving (Show, Enum, Bounded)
$(genArithDataType Binop "ArithBOp")

$(genArithNameFun Binop ''ArithBOp "aboName" (map toLower . drop 3))
$(genArithEnumFun Binop ''ArithBOp "aboEnum")

$(do clauses <- readArithLists Binop
                  (\name _num hsop -> return (Clause [ConP (mkName name) [] []]
                                                     (NormalB (VarE 'mkName `AppE` LitE (StringL hsop)))
                                                     []))
                  return
     sequence [SigD (mkName "aboNumOp") <$> [t| ArithBOp -> Name |]
              ,return $ FunD (mkName "aboNumOp") clauses])


-- data ArithIBOp = IB_QUOT deriving (Show, Enum, Bounded)
$(genArithDataType IBinop "ArithIBOp")

$(genArithNameFun IBinop ''ArithIBOp "aiboName" (map toLower . drop 3))
$(genArithEnumFun IBinop ''ArithIBOp "aiboEnum")

$(do clauses <- readArithLists IBinop
                  (\name _num hsop -> return (Clause [ConP (mkName name) [] []]
                                                     (NormalB (VarE 'mkName `AppE` LitE (StringL hsop)))
                                                     []))
                  return
     sequence [SigD (mkName "aiboNumOp") <$> [t| ArithIBOp -> Name |]
              ,return $ FunD (mkName "aiboNumOp") clauses])


-- data ArithFBOp = FB_DIV deriving (Show, Enum, Bounded)
$(genArithDataType FBinop "ArithFBOp")

$(genArithNameFun FBinop ''ArithFBOp "afboName" (map toLower . drop 3))
$(genArithEnumFun FBinop ''ArithFBOp "afboEnum")

$(do clauses <- readArithLists FBinop
                  (\name _num hsop -> return (Clause [ConP (mkName name) [] []]
                                                     (NormalB (VarE 'mkName `AppE` LitE (StringL hsop)))
                                                     []))
                  return
     sequence [SigD (mkName "afboNumOp") <$> [t| ArithFBOp -> Name |]
              ,return $ FunD (mkName "afboNumOp") clauses])


-- data ArithUOp = UO_NEG | UO_ABS | UO_SIGNUM | ... deriving (Show, Enum, Bounded)
$(genArithDataType Unop "ArithUOp")

$(genArithNameFun Unop ''ArithUOp "auoName" (map toLower . drop 3))
$(genArithEnumFun Unop ''ArithUOp "auoEnum")


-- data ArithFUOp = FU_RECIP | ... deriving (Show, Enum, Bounded)
$(genArithDataType FUnop "ArithFUOp")

$(genArithNameFun FUnop ''ArithFUOp "afuoName" (map toLower . drop 3))
$(genArithEnumFun FUnop ''ArithFUOp "afuoEnum")


-- data ArithRedOp = RO_SUM1 | RO_PRODUCT1 deriving (Show, Enum, Bounded)
$(genArithDataType Redop "ArithRedOp")

$(genArithNameFun Redop ''ArithRedOp "aroName" (map toLower . drop 3))
$(genArithEnumFun Redop ''ArithRedOp "aroEnum")
