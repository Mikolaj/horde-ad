{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
module Data.Array.Nested.Trace.TH where

import Control.Monad (zipWithM)
import Data.List (foldl')
import Data.Maybe (isJust)
import Language.Haskell.TH hiding (cxt)
import System.IO (hPutStr, stderr)
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Nested


splitFunTy :: Type -> ([TyVarBndr Specificity], Cxt, [Type], Type)
splitFunTy = \case
  ArrowT `AppT` t1 `AppT` t2 ->
    let (vars, cx, args, ret) = splitFunTy t2
    in (vars, cx, t1 : args, ret)
  ForallT vs cx' t ->
    let (vars, cx, args, ret) = splitFunTy t
    in (vs ++ vars, cx' ++ cx, args, ret)
  t -> ([], [], [], t)

data Arg = RRanked Type Arg
         | RShaped Type Arg
         | RMixed Type Arg
         | RShowable Type
         | ROther Type
  deriving (Show)

recognise :: Type -> Maybe Arg
recognise (ConT name `AppT` sht `AppT` ty)
  | name == ''Ranked = Just (RRanked sht (recogniseElt ty))
  | name == ''Shaped = Just (RShaped sht (recogniseElt ty))
  | name == ''Mixed = Just (RMixed sht (recogniseElt ty))
  | name == ''Conversion = Just (RShowable ty)
recognise ty@(ConT name `AppT` _)
  | name `elem` [''IShR, ''IIxR, ''ShS, ''IIxS, ''SNat, ''Perm] =
      Just (RShowable ty)
recognise ty@(ConT name)
  | name == ''PermR = Just (RShowable ty)
recognise (ListT `AppT` ty) = Just (ROther ty)
recognise _ = Nothing

recogniseElt :: Type -> Arg
recogniseElt (ConT name `AppT` sht `AppT` ty)
  | name == ''Ranked = RRanked sht (recogniseElt ty)
  | name == ''Shaped = RShaped sht (recogniseElt ty)
  | name == ''Mixed = RMixed sht (recogniseElt ty)
recogniseElt ty = ROther ty

realise :: Arg -> Type
realise (RRanked sht ty) = ConT ''Ranked `AppT` sht `AppT` realise ty
realise (RShaped sht ty) = ConT ''Shaped `AppT` sht `AppT` realise ty
realise (RMixed sht ty) = ConT ''Mixed `AppT` sht `AppT` realise ty
realise (RShowable ty) = ty
realise (ROther ty) = ty

mkShow :: Arg -> Cxt
mkShow (RRanked _ ty) = mkShowElt ty
mkShow (RShaped _ ty) = mkShowElt ty
mkShow (RMixed sht ty) = [ConT ''Show `AppT` realise (RMixed sht ty)]
mkShow (RShowable _) = []
mkShow (ROther ty) = [ConT ''Show `AppT` ty]

mkShowElt :: Arg -> Cxt
mkShowElt (RRanked _ ty) = mkShowElt ty
mkShowElt (RShaped _ ty) = mkShowElt ty
mkShowElt (RMixed sht ty) = [ConT ''Show `AppT` realise (RMixed sht ty), ConT ''Elt `AppT` realise (RMixed sht ty)]
mkShowElt (RShowable _ty) = []  -- [ConT ''Elt `AppT` ty]
mkShowElt (ROther ty) = [ConT ''Show `AppT` ty, ConT ''Elt `AppT` ty]

-- If you pass a polymorphic function to seq, GHC wants to monomorphise and
-- doesn't know how to instantiate the type variables. Just don't, I guess.
isSeqable :: Type -> Bool
isSeqable ForallT{} = False
isSeqable (AppT a b) = isSeqable a && isSeqable b
isSeqable _ = True  -- yolo, I guess

convertType :: Type -> Q (Type, [Bool], [Bool], Bool)
convertType typ =
  let (tybndrs, cxt, args, ret) = splitFunTy typ
      argdescrs = map recognise args
      retdescr = recognise ret
  in return
      (ForallT tybndrs
               (cxt ++ [constr
                       | Just rel <- retdescr : argdescrs
                       , constr <- mkShow rel])
               (foldr (\a b -> ArrowT `AppT` a `AppT` b) ret args)
      ,map isJust argdescrs
      ,map isSeqable args
      ,isJust retdescr)

convertFun :: Name -> Q [Dec]
convertFun funname = do
  defname <- newName (nameBase funname)
  -- "ok": whether we understand this type enough to be able to show it
  (convty, argoks, argsseqable, retok) <- reifyType funname >>= convertType
  names <- zipWithM (\_ i -> newName ('x' : show i)) argoks [1::Int ..]
  -- let tracenames = map fst (filter snd (zip (names ++ [resname]) (argarrs ++ [retarr])))
  resname <- newName "res"
  let traceCall str val = VarE 'traceNoNewline `AppE` str `AppE` val
  let msg1 = [LitE (StringL ("oxtrace: (" ++ nameBase funname ++ " "))] ++
             [if ok
                then VarE 'showsPrec `AppE` LitE (IntegerL 11) `AppE` VarE n `AppE` LitE (StringL " ")
                else LitE (StringL "_ ")
             | (n, ok) <- zip names argoks] ++
             [LitE (StringL "...")]
  let msg2 | retok = [LitE (StringL " = "), VarE 'show `AppE` VarE resname, LitE (StringL ")\n")]
           | otherwise = [LitE (StringL " = _)\n")]
  let ex = LetE [ValD (VarP resname)
                      (NormalB (foldl' AppE (VarE funname) (map VarE names)))
                      []] $
             flip (foldr AppE) [VarE 'seq `AppE` VarE n | (n, True) <- zip names argsseqable] $
             traceCall (VarE 'concat `AppE` ListE msg1) $
             VarE 'seq `AppE` VarE resname `AppE`
             traceCall (VarE 'concat `AppE` ListE msg2) (VarE resname)
  return
    [SigD defname convty
    ,FunD defname [Clause (map VarP names) (NormalB ex) []]]

{-# NOINLINE traceNoNewline #-}
traceNoNewline :: String -> a -> a
traceNoNewline str x = unsafePerformIO $ do
  hPutStr stderr str
  return x
