{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ViewPatterns #-}
module HordeAd.Core.CompileFuthark (compileExpr) where

import Prelude

import Control.Monad.Trans.State.Strict
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as BSB
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Lazy qualified as Lazy
import Data.ByteString.Short (ShortByteString)
import Data.ByteString.Short qualified as BSS
import Data.Char (ord, chr)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Foldable (toList)
import Data.List (intersperse)
import Data.Int
import Data.Type.Equality
import Data.Typeable
import Data.Word
import Data.Vector.Strict qualified as V

import Data.Array.Mixed.Types (fromSNat')
import Data.Array.Mixed.Shape
import qualified Data.Array.Nested as N
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstTools (ftkAst)
import HordeAd.Core.TensorKind
import HordeAd.Core.Types


-- Conventions
-- ===========
--
-- We choose the simplest possible type representation:
--   Rep[TKScalar r]         = r
--   Rep[TKR2 k t]           = []...[](Rep[t])
--   Rep[TKS2 [k1,...,kn] t] = [k1]...[kn](Rep[t])
--   Rep[RKX2 [k1,...,kn] t] = [k1]...[kn](Rep[t])
--   Rep[TKProduct t1 t2]    = (Rep[t1], Rep[t2])
-- In particular, this means that e.g. Rep[TKR2 0 t] = Rep[t].
--
-- In comments and function names, we abbreviate @BuildTensorKind@ to BTK.
--
-- The general horde-ad semantics is that all terms model a dual number:
-- - terms with FullSpan model a general dual number;
-- - terms with PrimalSpan model a dual number with a zero dual component;
-- - terms with DualSpan model a dual number with a zero _primal_ component.
-- This backend computes only the primal parts of the dual numbers. To this
-- end, it requires the top-level expression to have PrimalSpan, so that the
-- (zero) dual part of that result does not need to be returned. This decision
-- also means that terms with FullSpan can be compiled as if they were
-- PrimalSpan (we aren't computing the dual half anyway), and that terms with
-- DualSpan can be completely ignored. The result of a DualSpan term can only
-- be used in another DualSpan term, or using one of the following primitives:
-- - AstFromDual: this returns a FullSpan result, the primal component of which
--   is zero; we only compute the primal component, so AstFromDual just returns
--   zero in this backend.
-- - AstApply: this allows a variable of arbitrary span to be used in a
--   subcomputation with the same span as the context (primal or full, in our
--   case). Fortunately, if said variable has DualSpan, by induction its value
--   will not be observable in the subcomputation (which is compiled with this
--   same backend).
-- Hence our policy is consistent. Whenever we skip DualPart terms because
-- their result could not be referenced anyway in a primal computation, we add
-- the note "Note: no duals".

-- :m *HordeAd Prelude HordeAd.Core.CompileFuthark HordeAd.Core.CarriersAst
-- :seti -XOverloadedLists -fprint-explicit-foralls
-- compileExpr $ unAstNoSimplify $ tlet @_ @_ @(AstNoSimplify PrimalSpan) (tpair (kconcrete (7::Double)) (sfromList @10 @'[] (fmap sscalar [1..10 :: Double]))) $ \x -> tproject1 x


type Name = ShortByteString

bss8 :: String -> ShortByteString
bss8 = BSS.pack . map (fromIntegral . ord)

-- | Futhark expression.
data FEx
  = FELit ShortByteString
  | FETuple [FEx]
  | FEList (V.Vector FEx)
  | FEApp Name [FEx]
  | FEBinop FEx Name FEx
  | FELam Name FEx
  | FELet Name FEx FEx
  | FEIf FEx FEx FEx
  deriving (Show)

pattern FELitS :: String -> FEx
pattern FELitS s <- FELit (map (chr . fromIntegral) . BSS.unpack -> s)
  where FELitS s = FELit (bss8 s)

compileExpr :: AstTensor AstMethodLet PrimalSpan t -> Lazy.ByteString
compileExpr = prettyExpr . runIdGen . compE (Env DMap.empty DMap.empty)

prettyExpr :: FEx -> Lazy.ByteString
prettyExpr = BSB.toLazyByteString . go 0
  where
    go :: Int -> FEx -> BSB.Builder
    go d = \case
      FELit l -> BSB.shortByteString l
      FETuple es -> BSB.char8 '(' <> mconcat (intersperse (BSB.char8 ',') (map (go 0) es)) <> BSB.char8 ')'
      FEList v -> BSB.char8 '[' <> mconcat (intersperse (BSB.char8 ',') (map (go 0) (toList v))) <> BSB.char8 ']'
      FEApp n es -> bParen (d > 10) $
        BSB.shortByteString n <> mconcat [BSB.char8 ' ' <> go 11 e | e <- es]
      FEBinop e1 n e2 ->
        -- TODO: less redundant parentheses
        bParen (d > 9) $
          go 10 e1 <> BSB.char8 ' ' <> BSB.shortByteString n <> BSB.char8 ' ' <> go 10 e2
      FELam n e -> bParen (d > 0) $
        BSB.char8 '\\' <> BSB.shortByteString n <> BSB.shortByteString (bss8 " -> ") <> go 0 e
      FELet n e1 e2 -> bParen (d > 0) $
        BSB.shortByteString (bss8 "let ") <> BSB.shortByteString n <>
        BSB.shortByteString (bss8 " = ") <> go 0 e1 <>
        BSB.shortByteString (bss8 " in ") <> go 0 e2
      FEIf e1 e2 e3 -> bParen (d > 0) $
        BSB.shortByteString (bss8 "if ") <> go 0 e1 <>
        BSB.shortByteString (bss8 "then ") <> go 0 e2 <>
        BSB.shortByteString (bss8 "else ") <> go 0 e3

    bParen :: Bool -> BSB.Builder -> BSB.Builder
    bParen False b = b
    bParen True b = BSB.char8 '(' <> b <> BSB.char8 ')'

class PrimalIsh (s :: AstSpanType) where
  whichSpanType :: Either (s :~: PrimalSpan) (s :~: FullSpan)
instance PrimalIsh PrimalSpan where
  whichSpanType = Left Refl
instance PrimalIsh FullSpan where
  whichSpanType = Right Refl

checkPrimalIsh :: forall s sm y. AstSpan s => AstTensor sm s y -> Either (Dict PrimalIsh s) (s :~: DualSpan)
checkPrimalIsh _
  | Just Refl <- sameAstSpan @s @PrimalSpan = Left Dict
  | Just Refl <- sameAstSpan @s @FullSpan = Left Dict
  | Just Refl <- sameAstSpan @s @DualSpan = Right Refl
  | otherwise = error "checkPrimalIsh: span not Primal/Full/Dual"

type role SomeName nominal
newtype SomeName (n :: TK) = SomeName Name
  deriving (Show)

data Env = Env
  { envPr :: DEnumMap (AstVarName PrimalSpan) SomeName
  , envFu :: DEnumMap (AstVarName FullSpan) SomeName }
  deriving (Show)

envInsert :: forall s y. PrimalIsh s => AstVarName s y -> Name -> Env -> Env
envInsert var val env = case whichSpanType @s of
  Left  Refl -> env { envPr = DMap.insert var (SomeName val) (envPr env) }
  Right Refl -> env { envFu = DMap.insert var (SomeName val) (envFu env) }

envLookup :: forall s y. PrimalIsh s => AstVarName s y -> Env -> Maybe Name
envLookup var env = case whichSpanType @s of
  Left  Refl -> (\(SomeName s) -> s) <$> DMap.lookup var (envPr env)
  Right Refl -> (\(SomeName s) -> s) <$> DMap.lookup var (envFu env)

compE :: PrimalIsh s => Env -> AstTensor AstMethodLet s y -> IdGen FEx
compE env topexpr = case topexpr of
  AstPair a b -> FETuple <$:> [compE env a, compE env b]
  AstProject1 a -> FEApp "fst" <$:> [compE env a]
  AstProject2 a -> FEApp "snd" <$:> [compE env a]
  AstFromVector _ t v -> unzipBTK t =<< FEList <$:> fmap (compE env) v
  AstSum _ _ a ->
    mapOverTuple (ftkPT (ftkAst topexpr))  -- topexpr has precisely the tuple type we need, without BTK
      (\t e -> FEApp "reduce_comm" <$:> [toLambda2 (addEltwise t), makeZeros t, pure e])
      =<< compE env a
  AstReplicate _ _ a ->
    mapOverTuple (ftkPT (ftkAst a))
      (\_ e -> pure $ FEApp "replicate" [e])
      =<< compE env a
  AstApply (AstLambda var a) b -> case checkPrimalIsh b of
    Left Dict -> do
      name <- fresh
      FELet name <$> compE env b <*> compE (envInsert var name env) a
    Right _ -> compE env a  -- Note: no duals
  AstVar var -> case envLookup var env of
                  Just name -> pure $ FELit name
                  Nothing -> error $ "CompileFuthark: Variable out of scope: " ++ show var
  AstCond a b c -> FEIf <$> compBE env a <*> compE env b <*> compE env c
  AstBuild1 k t (var, a) -> do
    name <- fresh
    unzipBTK t =<< FEApp "tabulate" <$:>
                     [pure (FELitS (show (fromSNat' k)))
                     ,compE (envInsert var name env) a]

  AstLet var a b -> case checkPrimalIsh a of
    Left Dict -> do
      name <- fresh
      FELet name <$> compE env a <*> compE (envInsert var name env) b
    Right _ -> compE env b  -- Note: no duals

  AstPrimalPart a -> compE env a
  AstDualPart{} -> error "CompileFuthark: unexpected compilation of DualPart term"  -- Note: no duals
  AstFromPrimal a -> compE env a
  AstFromDual _ -> makeZeros (ftkAst topexpr)  -- Note: no duals

  AstPlusK a b -> FEBinop <$> compE env a <*> pure "+" <*> compE env b
  AstTimesK a b -> FEBinop <$> compE env a <*> pure "*" <*> compE env b
  AstN1K op a -> compOpCodeNum1 (ftkAst a) op <$> compE env a
  AstR1K op a -> compOpCode1 (ftkAst a) op <$> compE env a
  AstR2K op a b -> compOpCode2 (ftkAst a) op <$> compE env a <*> compE env b
  AstI2K op a b -> compOpCodeIntegral2 (ftkAst a) op <$> compE env a <*> compE env b
  AstConcreteK x -> pure $ FELitS (show x)
  AstFloorK a -> FEApp "floor" <$:> [compE env a]
  AstFromIntegralK a -> FEApp (convertFun (toScalTy (ftkAst a)) (toScalTy (ftkAst topexpr))) <$:> [compE env a]
  AstCastK a -> FEApp (convertFun (toScalTy (ftkAst a)) (toScalTy (ftkAst topexpr))) <$:> [compE env a]

  AstPlusS a b -> repMap2' (ftkAst a) (\_ x y -> pure (FEBinop x "+" y)) (compE env a) (compE env b)
  AstTimesS a b -> repMap2' (ftkAst a) (\_ x y -> pure (FEBinop x "*" y)) (compE env a) (compE env b)
  AstN1S op a -> repMap1' (ftkAst a) (\t x -> pure (compOpCodeNum1 t op x)) (compE env a)
  AstR1S op a -> repMap1' (ftkAst a) (\t x -> pure (compOpCode1 t op x)) (compE env a)
  AstR2S op a b -> repMap2' (ftkAst a) (\t x y -> pure (compOpCode2 t op x y)) (compE env a) (compE env b)
  AstI2S op a b -> repMap2' (ftkAst a) (\t x y -> pure (compOpCodeIntegral2 t op x y)) (compE env a) (compE env b)
  AstConcreteS arr -> pure $ compConcrete arr

  AstMapAccumRDer{} -> error "CompileFuthark: unimplemented AstMapAccumRDer"
  AstMapAccumLDer{} -> error "CompileFuthark: unimplemented AstMapAccumLDer"
  _ -> error "CompileFuthark: unimplemented"

compBE :: Env -> AstBool AstMethodLet -> IdGen FEx
compBE env = \case
  AstBoolConst x -> pure $ FELitS (show x)
  AstBoolNot a -> FEApp "not" <$:> [compBE env a]
  AstBoolAnd a b -> FEBinop <$> compBE env a <*> pure "&&" <*> compBE env b
  AstLeqK a b -> FEBinop <$> compE env a <*> pure "<=" <*> compE env b
  AstLeqS a b -> FEBinop <$> compE env a <*> pure "<=" <*> compE env b

compOpCodeNum1 :: FullShapeTK (TKScalar r) -> OpCodeNum1 -> FEx -> FEx
compOpCodeNum1 ty@FTKScalar op e = case op of
  NegateOp -> FEApp (md "negate") [e]
  AbsOp    -> FEApp (md "abs") [e]
  SignumOp -> FEApp (md "signum") [e]
  where
    md n = bss8 $ scalTyToMod (toScalTy ty) ++ "." ++ n

compOpCode1 :: FullShapeTK (TKScalar r) -> OpCode1 -> FEx -> FEx
compOpCode1 ty@FTKScalar op e = case op of
  RecipOp -> FEApp (md "recip") [e]
  ExpOp   -> FEApp (md "exp") [e]
  LogOp   -> FEApp (md "log") [e]
  SqrtOp  -> FEApp (md "sqrt") [e]
  SinOp   -> FEApp (md "sin") [e]
  CosOp   -> FEApp (md "cos") [e]
  TanOp   -> FEApp (md "tan") [e]
  AsinOp  -> FEApp (md "asin") [e]
  AcosOp  -> FEApp (md "acos") [e]
  AtanOp  -> FEApp (md "atan") [e]
  SinhOp  -> FEApp (md "sinh") [e]
  CoshOp  -> FEApp (md "cosh") [e]
  TanhOp  -> FEApp (md "tanh") [e]
  AsinhOp -> FEApp (md "asinh") [e]
  AcoshOp -> FEApp (md "acosh") [e]
  AtanhOp -> FEApp (md "atanh") [e]
  where
    md n = bss8 $ scalTyToMod (toScalTy ty) ++ "." ++ n

compOpCode2 :: FullShapeTK (TKScalar r) -> OpCode2 -> FEx -> FEx -> FEx
compOpCode2 ty@FTKScalar op a b = case op of
  DivideOp  -> FEBinop a "/" b
  PowerOp   -> FEBinop a "**" b
  LogBaseOp -> FEBinop (FEApp (md "log") [a]) "/" (FEApp (md "log") [b])
  Atan2Op   -> FEApp (md "atan2") [a,b]
  where
    md n = bss8 $ scalTyToMod (toScalTy ty) ++ "." ++ n

compOpCodeIntegral2 :: FullShapeTK (TKScalar r) -> OpCodeIntegral2 -> FEx -> FEx -> FEx
compOpCodeIntegral2 FTKScalar op a b = case op of
  QuotOp -> FEBinop a "/" b
  RemOp  -> FEBinop a "%" b

convertFun :: ScalTy r1 -> ScalTy r2 -> Name
convertFun _ SBool =
  -- This is only possible to trigger from user code if one adds Num and
  -- possibly RealFrac instances for Bool.
  error "CompileFuthark: Cannot use t{s,k}fromIntegral or t{s,k}cast to convert to Bool"
convertFun from to = bss8 $ scalTyToMod to ++ "." ++ scalTyToMod from

-- TODO: if the constant is huge, this creates a huge intermediate term that is
-- even larger than its textual representation afterwards. The user is kind of
-- asking for it, but it's still not great.
compConcrete :: forall sh r. GoodScalar r => N.Shaped sh r -> FEx
compConcrete = \arr -> go (N.sshape arr) (N.sindex arr)
  where
    go :: ShS sh' -> (IIxS sh' -> r) -> FEx
    go ZSS f = FELitS (show (f ZIS) ++ scalTyToMod (toScalTy (Proxy @(TKScalar r))))
    go (n :$$ sh) f =
      FEList (V.fromListN (fromSNat' n)
                  [go sh (f . (\idx -> i :.$ idx)) | i <- [0 .. fromSNat' n - 1]])

makeZeros :: FullShapeTK y -> IdGen FEx
makeZeros FTKScalar = pure (FELit "0")
makeZeros (FTKR sh t) = do
  zeros <- makeZeros t
  pure $ foldr (\n e -> FEApp "replicate" [FELitS (show n), e]) zeros (toList sh)
makeZeros (FTKS sh t) = do
  zeros <- makeZeros t
  pure $ foldr (\n e -> FEApp "replicate" [FELitS (show n), e]) zeros (shsToList sh)
makeZeros (FTKX sh t) = do
  zeros <- makeZeros t
  pure $ foldr (\n e -> FEApp "replicate" [FELitS (show n), e]) zeros (shxToList sh)
makeZeros (FTKProduct t1 t2) = FETuple <$:> [makeZeros t1, makeZeros t2]

addEltwise :: FullShapeTK y -> FEx -> FEx -> IdGen FEx
addEltwise topty e1 e2 = case topty of
  FTKScalar -> pure $ FEBinop e1 "+" e2
  FTKR{} -> repMap2 topty addEltwise e1 e2
  FTKS{} -> repMap2 topty addEltwise e1 e2
  FTKX{} -> repMap2 topty addEltwise e1 e2
  FTKProduct t1 t2 ->
    FEApp "bimap2" <$:> [toLambda2 (addEltwise t1), toLambda2 (addEltwise t2)
                        ,pure e1, pure e2]

class IsArrayType t where
  type ArrayTypeElt t :: TK
  arrayShapeRank :: FullShapeTK t -> Int
  arrayTypeElt :: FullShapeTK t -> FullShapeTK (ArrayTypeElt t)
instance IsArrayType (TKS2 sh y) where
  type ArrayTypeElt (TKS2 sh y) = y
  arrayShapeRank (FTKS sh _) = fromSNat' (shsRank sh)
  arrayTypeElt (FTKS _ t) = t
instance IsArrayType (TKR2 n y) where
  type ArrayTypeElt (TKR2 n y) = y
  arrayShapeRank (FTKR n _) = fromSNat' (shrRank n)
  arrayTypeElt (FTKR _ t) = t
instance IsArrayType (TKX2 sh y) where
  type ArrayTypeElt (TKX2 sh y) = y
  arrayShapeRank (FTKX sh _) = fromSNat' (shxRank sh)
  arrayTypeElt (FTKX _ t) = t

-- | The argument to the callback is NOT necessarily duplicable.
repMap1 :: IsArrayType t => FullShapeTK t -> (FullShapeTK (ArrayTypeElt t) -> FEx -> IdGen FEx) -> FEx -> IdGen FEx
repMap1 ty f e = case arrayShapeRank ty of
  0 -> f (arrayTypeElt ty) e
  rank ->
    FEApp "map" <$:>
      [iterateN (rank - 1) (\e' -> FEApp "map" [e']) <$> toLambda1 (f (arrayTypeElt ty))
      ,pure e]

-- | The argument to the callback is NOT necessarily duplicable.
repMap2 :: IsArrayType t => FullShapeTK t -> (FullShapeTK (ArrayTypeElt t) -> FEx -> FEx -> IdGen FEx) -> FEx -> FEx -> IdGen FEx
repMap2 ty f e1 e2 = case arrayShapeRank ty of
  0 -> f (arrayTypeElt ty) e1 e2
  rank ->
    FEApp "map2" <$:>
      [iterateN (rank - 1) (\e' -> FEApp "map" [e']) <$> toLambda2 (f (arrayTypeElt ty))
      ,pure e1, pure e2]

repMap1' :: IsArrayType t => FullShapeTK t -> (FullShapeTK (ArrayTypeElt t) -> FEx -> IdGen FEx) -> IdGen FEx -> IdGen FEx
repMap1' ty f e = e >>= repMap1 ty f

repMap2' :: IsArrayType t => FullShapeTK t -> (FullShapeTK (ArrayTypeElt t) -> FEx -> FEx -> IdGen FEx) -> IdGen FEx -> IdGen FEx -> IdGen FEx
repMap2' ty f e1 e2 = do
  x <- e1
  y <- e2
  repMap2 ty f x y

-- | Map a function over each tuple component, given an expression of that
-- tuple type. One can consider this function to have multiple distinct types,
-- that happen to be the same in Futhark land:
-- * Type (y1, ..., yn)
--     -> (Type yi -> Expr yi -> Expr zi)
--     -> Expr (y1, ..., yn)
--     -> Expr (zi, ..., zn)
-- * Type (y1, ..., yn)
--     -> (Type yi -> Expr ([k]yi) -> Expr zi)
--     -> Expr (BuildTensorKind k (y1, ..., yn))
--     -> Expr (zi, ..., zn)
-- * Type (y1, ..., yn)
--     -> (Type yi -> Expr yi -> Expr ([k]zi))
--     -> Expr (y1, ..., yn)
--     -> Expr (BuildTensorKind k (zi, ..., zn))
-- * Type (y1, ..., yn)
--     -> (Type yi -> Expr ([k]yi) -> Expr ([k']zi))
--     -> Expr (BuildTensorKind k (y1, ..., yn))
--     -> Expr (BuildTensorKind k' (zi, ..., zn))
mapOverTuple :: ProductTree f y -> (forall y'. f y' -> FEx -> IdGen FEx) -> FEx -> IdGen FEx
mapOverTuple (PTPair t1 t2) f e = do
  (name1, name2) <- fresh
  FEApp "bimap" <$:> [FELam name1 <$> mapOverTuple t1 f (FELit name1)
                     ,FELam name2 <$> mapOverTuple t2 f (FELit name2)
                     ,pure e]
mapOverTuple (PTLeaf t) f e = f t e

toLambda1 :: (FEx -> IdGen FEx) -> IdGen FEx
toLambda1 f = do
  name <- fresh
  FELam name <$> f (FELit name)

toLambda2 :: (FEx -> FEx -> IdGen FEx) -> IdGen FEx
toLambda2 f = do
  (name1, name2) <- fresh
  FELam name1 . FELam name2 <$> f (FELit name1) (FELit name2)

-- -- | etaExpand 3 f [u, v] == (\x y z -> f u v x y z)
-- etaExpand :: Int -> String -> [FEx] -> IdGen FEx
-- etaExpand n f args = do
--   names <- replicateM n fresh
--   pure $ foldr FELam (FEApp f (args ++ map FELit names)) names

iterateN :: Int -> (a -> a) -> a -> a
iterateN 0 _ x = x
iterateN n f x = iterateN (n - 1) f (f x)

-- | Given a TensorKind for @y@ and an expression of type @[]y@, returns an
-- expression of type @BuildTensorKind k y@.
unzipBTK :: SingletonTK y -> FEx -> IdGen FEx
unzipBTK = go . stkPT
  where
    go :: ProductTree SingletonTK y -> FEx -> IdGen FEx
    go PTLeaf{} e = pure e
    go (PTPair PTLeaf{} PTLeaf{}) e = pure $ FEApp "unzip" [e]
    go (PTPair pt1 PTLeaf{}) e = do
      name <- fresh
      FEApp "first" <$:> [FELam name <$> go pt1 (FELit name), pure (FEApp "unzip" [e])]
    go (PTPair PTLeaf{} pt2) e = do
      name <- fresh
      FEApp "second" <$:> [FELam name <$> go pt2 (FELit name), pure (FEApp "unzip" [e])]
    go (PTPair pt1 pt2) e = do
      (name1, name2) <- fresh
      FEApp "bimap" <$:> [FELam name1 <$> go pt1 (FELit name1)
                         ,FELam name2 <$> go pt2 (FELit name2)
                         ,pure (FEApp "unzip" [e])]

type role ProductTree representational nominal
data ProductTree f y where
  PTPair :: ProductTree f y1 -> ProductTree f y2 -> ProductTree f (TKProduct t1 t2)
  PTLeaf :: f y -> ProductTree f y

stkPT :: SingletonTK y -> ProductTree SingletonTK y
stkPT (STKProduct t1 t2) = PTPair (stkPT t1) (stkPT t2)
stkPT t@STKScalar = PTLeaf t  -- enumerate the cases explicitly so we get warnings on new cases
stkPT t@STKR{} = PTLeaf t
stkPT t@STKS{} = PTLeaf t
stkPT t@STKX{} = PTLeaf t

ftkPT :: FullShapeTK y -> ProductTree FullShapeTK y
ftkPT (FTKProduct t1 t2) = PTPair (ftkPT t1) (ftkPT t2)
ftkPT t@FTKScalar = PTLeaf t  -- enumerate the cases explicitly so we get warnings on new cases
ftkPT t@FTKR{} = PTLeaf t
ftkPT t@FTKS{} = PTLeaf t
ftkPT t@FTKX{} = PTLeaf t

type role ScalTy nominal
data ScalTy t where
  SI8 :: ScalTy Int8
  SI16 :: ScalTy Int16
  SI32 :: ScalTy Int32
  SI64 :: ScalTy Int64
  SU8 :: ScalTy Word8
  SU16 :: ScalTy Word16
  SU32 :: ScalTy Word32
  SU64 :: ScalTy Word64
  -- SF16 :: ScalTy Half
  SF32 :: ScalTy Float
  SF64 :: ScalTy Double
  SBool :: ScalTy Bool

toScalTy :: forall t f. Typeable t => f (TKScalar t) -> ScalTy t
toScalTy p
  | Just Refl <- eqT @t @Int8 = SI8
  | Just Refl <- eqT @t @Int16 = SI16
  | Just Refl <- eqT @t @Int32 = SI32
  | Just Refl <- eqT @t @Int64 = SI64
  | Just Refl <- eqT @t @Word8 = SU8
  | Just Refl <- eqT @t @Word16 = SU16
  | Just Refl <- eqT @t @Word32 = SU32
  | Just Refl <- eqT @t @Word64 = SU64
  -- | Just Refl <- eqT @t @Half = SF16
  | Just Refl <- eqT @t @Float = SF32
  | Just Refl <- eqT @t @Double = SF64
  | Just Refl <- eqT @t @Bool = SBool
  | otherwise = error $ "CompileFuthark: encountered type " ++ show (typeRep p) ++
                        " not supported by Futhark"

scalTyToMod :: ScalTy t -> String
scalTyToMod = \case
  SI8 -> "i8"
  SI16 -> "i16"
  SI32 -> "i32"
  SI64 -> "i64"
  SU8 -> "u8"
  SU16 -> "u16"
  SU32 -> "u32"
  SU64 -> "u64"
  -- SF16 -> "f16"
  SF32 -> "f32"
  SF64 -> "f64"
  SBool -> "bool"

(<$:>) :: (Applicative f, Traversable t) => (t a -> b) -> t (f a) -> f b
f <$:> l = f <$> sequenceA l

type role IdGen nominal
newtype IdGen a = IdGen (State Int a)
  deriving newtype (Functor, Applicative, Monad)

class Fresh a where
  fresh :: IdGen a
instance Fresh ShortByteString where
  fresh = IdGen $ state (\i -> (bss8 ('x' : show i), i + 1))
instance (Fresh a, Fresh b) => Fresh (a, b) where
  fresh = (,) <$> fresh <*> fresh

runIdGen :: IdGen a -> a
runIdGen (IdGen m) = evalState m 1
