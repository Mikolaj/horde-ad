{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
module HordeAd.Core.CompileFuthark (compileExpr, HList(..)) where

import Prelude

import Control.Monad (forM_, forM)
import Control.Monad.Trans.State.Strict
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString.Builder qualified as BSB
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Lazy qualified as Lazy
import Data.ByteString.Short (ShortByteString)
import Data.ByteString.Short qualified as BSS
import Data.Char (ord, chr)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.Sum
import Data.Foldable (toList)
import Data.Functor.Product as Fun
import Data.Kind (Type)
import Data.List (intersperse)
import Data.Int
import Data.Maybe (catMaybes)
import Data.Some
import Data.Type.Equality
import Data.Typeable
import Data.Word
import Data.Vector.Storable qualified as VS
import Data.Vector.Strict qualified as V
import Foreign.ForeignPtr (touchForeignPtr)
import Foreign.Marshal.Alloc
import Foreign.Storable

import Data.Array.Mixed.Lemmas (lemRankReplicate)
import Data.Array.Mixed.Shape
import Data.Array.Mixed.Types (fromSNat', type (++), Replicate)
import qualified Data.Array.Nested as N
import Data.Array.Nested.Internal.Shape

import HordeAd.Core.Ast
import HordeAd.Core.AstTools (ftkAst)
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.CompileFuthark.Exec
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

-- C FFI API
-- =========
--
-- Binding various functions with runtime-dependent signatures via the FFI is
-- complicated, so instead of binding the Futhark-generated C API directly, we
-- generate some glue C code with an exceedingly simple function signature:
-- void f(void*). All data exchange happens through a single memory buffer
-- allocated and freed on the Haskell side.
--
-- Contents of that buffer is first all input arguments (written from the
-- Haskell side and read by C), followed by space for the output (written from
-- C and read by Haskell). Because Futhark does not define a binary format for
-- tuples, we must unzip everything to individual scalar arrays. We don't want
-- to do said unzipping in C, so we do it in Haskell.
--
-- The input type
--   TKProduct (TKS [2, 3] (TKProduct (TKScalar @Double)
--                                    (TKS [5] (TKScalar @Int))))
--             (TKS [4] (TKScalar @Float))
-- turns into 3 Futhark-land inputs:
-- - [2][3]f64
-- - [2][3][5]i64
-- - [4]f32
-- and similarly for the output. Hence, an actual input/output in the C
-- interface is either a scalar or a multi-dimensional array of scalars; a
-- scalar is represented as-is, and an array of scalars is represented as a
-- pointer to a memory buffer (pre-)allocated by Haskell.
--
-- In the memory buffer, all values are properly aligned by the usual C rules.
-- Use `computeStructOffsets` for this.

{-
:m *HordeAd Prelude HordeAd.Core.CompileFuthark HordeAd.Core.CarriersAst Data.Some Data.Array.Nested.Internal.Shape Data.Int
:seti -XOverloadedLists -fprint-explicit-foralls

-- let x = (7, [1..10]) in fst x
compileExpr [] $ unAstNoSimplify $ tlet @_ @_ @(AstNoSimplify PrimalSpan) (tpair (kconcrete (7::Double)) (sfromList @10 @'[] (fmap sscalar [1..10 :: Double]))) $ \x -> tproject1 x

-- var : ([5]f64, f32) |- let x = (7, [1..10]) in (fst x + kfromS (ssum (fst var)), 42)
let var = mkAstVarName (FTKProduct (FTKS (SNat @5 :$$ ZSS) (FTKScalar @Double)) (FTKScalar @Float)) Nothing (toEnum (-1)) in compileExpr (var `HCons` HNil) $ unAstNoSimplify $ tlet @_ @_ @(AstNoSimplify PrimalSpan) (tpair (kconcrete (7::Double)) (sfromList @10 @'[] (fmap sscalar [1..10 :: Double]))) $ \x -> tpair (tproject1 x + kfromS (ssum (tproject1 (AstNoSimplify (AstVar var))))) (kconcrete (42 :: Int64))
-}


type Name = ShortByteString

-- | Futhark expression.
data FEx
  = FELit ShortByteString
  | FETuple [FEx]
  | FEList (V.Vector FEx)
  | FEProj FEx ShortByteString  -- field name projection
  | FEApp Name [FEx]
  | FEBinop FEx Name FEx
  | FELam Name FEx
  | FELet Name FEx FEx
  | FEIf FEx FEx FEx
  deriving (Show)

-- | A context: a bunch of let bindings.
newtype FCtx = FCtx [(Name, FEx)]
  deriving (Show)

instance Semigroup FCtx where FCtx a <> FCtx b = FCtx (a ++ b)
instance Monoid FCtx where mempty = FCtx []

letCtx :: FCtx -> FEx -> FEx
letCtx (FCtx l) e = foldr (uncurry FELet) e l

pattern FELitS :: String -> FEx
pattern FELitS s <- FELit (map (chr . fromIntegral) . BSS.unpack -> s)
  where FELitS s = FELit (bss8 s)

type role HList representational nominal
type HList :: forall {k}. (k -> Type) -> [k] -> Type
data HList f list where
  HNil :: HList f '[]
  HCons :: f a -> HList f list -> HList f (a : list)
infixr `HCons`

hlistToList :: (forall a. f a -> t) -> HList f list -> [t]
hlistToList _ HNil = []
hlistToList f (x `HCons` xs) = f x : hlistToList f xs

hlistMap :: (forall a. f a -> g a) -> HList f list -> HList g list
hlistMap _ HNil = HNil
hlistMap f (x `HCons` xs) = f x `HCons` hlistMap f xs

hlistZipWith :: (forall a. f1 a -> f2 a -> f3 a) -> HList f1 list -> HList f2 list -> HList f3 list
hlistZipWith _ HNil HNil = HNil
hlistZipWith f (x `HCons` xs) (y `HCons` ys) = f x y `HCons` hlistZipWith f xs ys

compileExpr :: HList (AstVarName PrimalSpan) args -> AstTensor AstMethodLet PrimalSpan t
            -> IO (HList Concrete args -> IO (RepConcrete t))
compileExpr inputVars ast = do
  let arguments' = hlistMap (\var -> Pair var (splitType (varNameToFTK var))) inputVars
      arguments = hlistToList (\(Pair v str) -> v :=> str) arguments'
      outSplit = splitType (ftkAst ast)
      futintys = [ty | _ :=> SplitTypeRes parts _ _ _ _ <- arguments, ty <- parts]
      futouttys = let SplitTypeRes parts _ _ _ _ = outSplit in parts

  let (alloffsets, databufsize) = computeStructOffsets [metrics t | Some t <- futintys ++ futouttys]
      (argoffsets, outoffsets) = splitAt (length arguments) alloffsets
      fullargoffsets = coalesce [Some str | _ :=> str <- arguments] argoffsets

  kernel <- buildKernel (compileExprToFuthark arguments outSplit ast)
                        (generateCWrapper futintys argoffsets futouttys outoffsets)
                        "horde_ad_kernel_top"
  return $ \argvals ->
    allocaBytes databufsize $ \ptr -> do
      -- collect input vectors for keep-alive later
      let inputs = hlistToList (\(Pair (Pair _ str) val) -> Some (Pair str val)) (hlistZipWith Pair arguments' argvals)
      inputvecs <- forM (zip inputs fullargoffsets) $ \(Some (Pair (SplitTypeRes _ split _ _ _) (Concrete fullval)), offs) ->
        forM @_ @_ @_ @(Maybe (Some VS.Vector)) (zip (split fullval) offs) $ \(Some (TypedCon (ATArray sh eltty) val), off) -> do
          Dict <- return $ scalTyDict eltty
          case sh of
            _ :$% _ -> do
              VS.unsafeWith (N.mtoVector val) $ \valptr ->
                pokeByteOff ptr off valptr
              return (Just (Some (N.mtoVector val)))
            ZSX -> do
              pokeByteOff ptr off (N.munScalar val)
              return Nothing

      -- TODO: allocate space for outputs
      -- TODO: call kernel

      -- make sure the input vectors stay alive until here
      forM_ (catMaybes (concat inputvecs)) $ \(Some vec) -> do
        touchForeignPtr (let (p, _, _) = VS.unsafeToForeignPtr vec in p)

      -- TODO: read outputs
      _

coalesce :: [Some SplitTypeRes] -> [a] -> [[a]]
coalesce (Some (SplitTypeRes parts _ _ _ _) : strs) l =
  let (pre, post) = splitAt (length parts) l
  in pre : coalesce strs post
coalesce [] _ = []

compileExprToFuthark
  :: [DSum (AstVarName PrimalSpan) SplitTypeRes]
  -> SplitTypeRes t
  -> AstTensor AstMethodLet PrimalSpan t
  -> Lazy.ByteString
compileExprToFuthark arguments (SplitTypeRes outParts _ _ outFutSplit _) term =
  let outerArgs = [(futTypeName partTy, bss8 ("arg" ++ show i ++ "_" ++ show j))
                  | (_ :=> SplitTypeRes parts _ _ _ _, i) <- zip arguments [1::Int ..]
                  , (Some partTy, j) <- zip parts [1::Int ..]]
      innerEnv = DMap.fromList
                   [var :=> SomeName (bss8 ("arg" ++ show i))
                   | (var :=> _, i) <- zip arguments [1::Int ..]]
      outFutTy = case outParts of
                   [Some t] -> futTypeName t
                   _ -> BSB.char8 '(' <>
                        mconcat (intersperse (BSB.char8 ',') [futTypeName t | Some t <- outParts]) <>
                        BSB.char8 ')'
  in BSB.toLazyByteString $
       BSB.byteString futLibrary <>
       bsb8 "entry main" <>
       mconcat [bsb8 " (" <> BSB.shortByteString name <> bsb8 ": " <> ty <> bsb8 ")"
               | (ty, name) <- outerArgs] <>
       bsb8 " : " <> outFutTy <> " =\n  " <>
       (prettyExpr $ runIdGen $ do
          argRecons <- sequence
              [do e <- futrecon [FELit (bss8 ("arg" ++ show i ++ "_" ++ show j))
                                | (_, j) <- zip parts [1::Int ..]]
                  pure (bss8 ("arg" ++ show i), e)
              | (_var :=> SplitTypeRes parts _ _ _ futrecon, i) <- zip arguments [1::Int ..]]
          body <- compE (Env innerEnv DMap.empty) term
          (outCtx, out) <- outFutSplit body
          pure (letCtx (FCtx argRecons) $
                letCtx outCtx $
                  case out of [e] -> e
                              _ -> FETuple out))

generateCWrapper :: [Some ArgType] -> [Int] -> [Some ArgType] -> [Int] -> Lazy.ByteString
generateCWrapper arguments argoffsets outputs outoffsets =
  let futArrName :: ArgType t -> BSB.Builder
      futArrName (ATArray sh@(_ :$% _) t) =
        bsb8 (scalTyToMod t) <> "_" <> bsb8 (show (fromSNat' (shxRank sh))) <> "d"
      futArrName (ATArray ZSX _) = error "futArrName called with scalar type"

      cTypeName :: ScalTy t -> BSB.Builder
      cTypeName = \case
        SI8 -> "int8_t" ; SI16 -> "int16_t" ; SI32 -> "int32_t" ; SI64 -> "int64_t"
        SU8 -> "uint8_t" ; SU16 -> "uint16_t" ; SU32 -> "uint32_t" ; SU64 -> "uint64_t"
        SF32 -> "float" ; SF64 -> "double" ; SBool -> "bool"

      haveinarrs  = any (\case Some (ATArray (_ :$% _) _) -> True ; _ -> False) arguments
      haveoutarrs = any (\case Some (ATArray (_ :$% _) _) -> True ; _ -> False) outputs

      sync True = "  futhark_context_sync(ctx);\n"
      sync False = mempty

  in BSB.toLazyByteString $
  -- TODO: allocate and supply a futhark cache file? Keyed by hash of futhark source, maybe?
  "#include \"prog.h\"\n\n\
  \void horde_ad_kernel_top(char *data) {\n\
  \  struct futhark_context_config *cfg = futhark_context_config_new();\n\
  \  struct futhark_context *ctx = futhark_context_new(cfg);\n"
  -- copy input arrays
  <> mconcat ["  struct futhark_" <> futArrName ty <> " *inarr" <> bsb8 (show i) <>
                " = futhark_new_" <> futArrName ty <>
                "(ctx, (const " <> cTypeName t <> "*)(data + " <> bsb8 (show off) <> ")" <>
                mconcat [", " <> bsb8 (show n) | n <- shxToList sh] <> ");\n"
             | (Some ty@(ATArray sh@(_ :$% _) t), off, i) <- zip3 arguments argoffsets [1::Int ..]]
  -- declare output arrays
  <> mconcat ["  struct futhark_" <> futArrName ty <> " *outarr" <> bsb8 (show i) <> ";"
             | (Some ty@(ATArray (_ :$% _) _), i) <- zip outputs [1::Int ..]]
  <> sync (haveinarrs || haveoutarrs)
  <>
  -- kernel call:
  "  futhark_entry_main(ctx\n"
  -- * output destinations
  <> mconcat [case ty of
                ATArray ZSX t -> "    , (" <> cTypeName t <> "*)(data + " <> bsb8 (show off) <> ")  // out " <> bsb8 (show i) <> ": " <> futTypeName ty <> "\n"
                ATArray _ _ -> "    , &outarr" <> bsb8 (show i) <> "  // out " <> bsb8 (show i) <> ": " <> futTypeName ty <> "\n"
             | (Some ty, off, i) <- zip3 outputs outoffsets [1::Int ..]]
  -- * inputs
  <> mconcat [case ty of
                ATArray ZSX t -> "    , *(const " <> cTypeName t <> "*)(data + " <> bsb8 (show off) <> ")  // in " <> bsb8 (show i) <> ": " <> futTypeName ty <> "\n"
                ATArray _ _ -> "    , inarr" <> bsb8 (show i) <> "  // in " <> bsb8 (show i) <> ": " <> futTypeName ty <> "\n"
             | (Some ty, off, i) <- zip3 arguments argoffsets [1::Int ..]]
  <>
  "  );\n"
  <> sync True
  -- release input arrays
  <> mconcat ["  futhark_free_" <> futArrName ty <> "(ctx, inarr" <> bsb8 (show i) <> ");\n"
             | (Some ty@(ATArray (_ :$% _) _), i) <- zip arguments [1::Int ..]]
  -- copy output arrays
  <> mconcat ["  futhark_values_" <> futArrName ty <> "(ctx, outarr" <> bsb8 (show i) <>
                ", (" <> cTypeName t <> "*)(data + " <> bsb8 (show off) <> ");\n"
             | (Some ty@(ATArray (_ :$% _) t), off, i) <- zip3 outputs outoffsets [1::Int ..]]
  <> sync (haveinarrs || haveoutarrs)
  -- release output arrays
  <> mconcat ["  futhark_free_" <> futArrName ty <> "(ctx, outarr" <> bsb8 (show i) <> ");\n"
             | (Some ty@(ATArray (_ :$% _) _), i) <- zip outputs [1::Int ..]]
  <> sync haveoutarrs
  <>
  "  futhark_context_free(ctx);\n\
  \  futhark_context_config_free(cfg);\n\
  \}\n"

-- | Returns (sizeof, alignment)
metrics :: ArgType t -> (Int, Int)
metrics (ATArray ZSX ty) = case ty of
  SI8 -> (1, 1)
  SI16 -> (2, 2)
  SI32 -> (4, 4)
  SI64 -> (8, 8)
  SU8 -> (1, 1)
  SU16 -> (2, 2)
  SU32 -> (4, 4)
  SU64 -> (8, 8)
  SF32 -> (4, 4)
  SF64 -> (8, 8)
  SBool -> (4, 4)  -- some C compilers like luxurious bathing space for their bools
metrics ATArray{} = (8, 8)  -- assuming 64-bit pointers

-- | Takes list of (sizeof, alignment)
computeStructOffsets :: [(Int, Int)] -> ([Int], Int)
computeStructOffsets = go 0
  where
    go off [] = ([], off)
    go off ((sz, al) : pairs) = let off' = roundUpToMultiple off al
                                in first (off' :) (go (off' + sz) pairs)
    roundUpToMultiple x n = (x + n - 1) `quot` n * n

type role ArgType nominal
data ArgType t where
  ATArray :: IShX sh -> ScalTy t -> ArgType (TKX sh t)
deriving instance Show (ArgType t)

-- | Typed concrete value
type role TypedCon nominal
data TypedCon t = TypedCon (ArgType t) (RepConcrete t)

-- | The types and shapes (!) in the argument to the reconstruction function
-- must be equal to those obtained from the decomposition.
-- Types are lost here, sorry.
type role SplitTypeRes nominal
data SplitTypeRes t = SplitTypeRes
  [Some ArgType]  -- ^ The types of the generated components
  (RepConcrete t -> [Some TypedCon])  -- ^ Split up an input value into components
  ([Some TypedCon] -> RepConcrete t)  -- ^ Reconstruct an output from components
  (FEx -> IdGen (FCtx, [FEx]))  -- ^ Split up an output into components in Futhark
  ([FEx] -> IdGen FEx)  -- ^ Compute a reconstructed input from components in Futhark

splitType :: FullShapeTK t -> SplitTypeRes t
splitType = \typ ->
  case go typ ZSX of
    (SplitTypeRes parts f1 f2 f3 f4, Dict) ->
      -- We don't need to post-process the Futhark-side expressions, because
      -- the Futhark representation of a zero-dimensional array is identical to
      -- its contained value.
      SplitTypeRes parts (f1 . N.mscalar) (N.munScalar . f2) f3 f4
  where
    go :: FullShapeTK t
       -> IShX upsh
       -> (SplitTypeRes (TKX2 upsh t), Dict N.Elt (RepConcrete t))
    go ty@FTKScalar upsh =
      let sty = toScalTy ty
          argty = ATArray upsh sty
      in
      (SplitTypeRes
        [Some argty]
        (\x -> [Some (TypedCon argty x)])
        (\l -> case l of [Some (TypedCon (ATArray sh2 ty2) x)]
                           | Just Refl <- shxEqual upsh sh2
                           , Just Refl <- testEquality sty ty2 -> x
                         _ -> error "invalid splitType response")
        -- array of scalars decomposes into... an array of scalars
        (\e -> pure (FCtx [], [e]))
        (\l -> case l of [e] -> pure e
                         _ -> error "invalid splitType Futhark response")
      ,Dict)
    go (FTKX sh ty) upsh
      | let upsh' = shxConcat upsh sh
      , (SplitTypeRes parts split recon futsplit futrecon, Dict) <- go ty upsh' =
          (SplitTypeRes
            parts
            (\arr -> split (N.munNest arr))
            (\l -> N.mnest (ssxFromShape upsh) (recon l))
            -- nesting/unnesting is the identity on Futhark arrays, so nothing to be adapted here
            futsplit
            futrecon
          ,Dict)
    go (FTKR @n sh ty) upsh
      | Refl <- lemRankReplicate (shrRank sh)
      , let upsh' = shxConcat upsh (shCvtRX sh)
      , (SplitTypeRes parts split recon futsplit futrecon, Dict) <- go ty upsh' =
          (SplitTypeRes
            parts
            (\arr -> split (N.munNest (N.castCastable (N.CastXX (N.CastRX N.CastId)) arr)))
            (\l -> N.castCastable (N.CastXX (N.CastXR N.CastId))
                       (N.mnest @_ @(Replicate n Nothing) (ssxFromShape upsh) (recon l)))
            futsplit
            futrecon
          ,Dict)
    go (FTKS sh ty) upsh
      | let upsh' = shxConcat upsh (shCvtSX sh)
      , (SplitTypeRes parts split recon futsplit futrecon, Dict) <- go ty upsh' =
          (SplitTypeRes
            parts
            (\arr -> split (N.munNest (N.castCastable (N.CastXX (N.CastSX N.CastId)) arr)))
            (\l -> N.castCastable (N.CastXX (N.CastXS N.CastId))
                       (N.mnest (ssxFromShape upsh) (recon l)))
            futsplit
            futrecon
          ,Dict)
    go (FTKProduct ty1 ty2) upsh
      | (SplitTypeRes parts1 split1 recon1 futsplit1 futrecon1, Dict) <- go ty1 upsh
      , (SplitTypeRes parts2 split2 recon2 futsplit2 futrecon2, Dict) <- go ty2 upsh =
          (SplitTypeRes
            (parts1 ++ parts2)
            (\arr ->
              let (arr1, arr2) = N.munzip arr
              in split1 arr1 ++ split2 arr2)
            (\l -> let (l1, l2) = splitAt (length parts1) l
                   in N.mzip (recon1 l1) (recon2 l2))
            (\e -> do
                (name1, nameL, nameR) <- fresh
                eL <- repMap1 (fromSNat' (shxRank upsh)) (\e' -> pure (FEProj e' "0")) (FELit name1)
                eR <- repMap1 (fromSNat' (shxRank upsh)) (\e' -> pure (FEProj e' "1")) (FELit name1)
                (ctx1, es1) <- futsplit1 (FELit nameL)
                (ctx2, es2) <- futsplit2 (FELit nameR)
                pure (FCtx [(name1, e)
                           ,(nameL, eL)
                           ,(nameR, eR)]
                      <> ctx1 <> ctx2
                     ,es1 ++ es2))
            (\es -> do
                let (es1, es2) = splitAt (length parts1) es
                eL <- futrecon1 es1
                eR <- futrecon2 es2
                repMap2 (fromSNat' (shxRank upsh)) (\e1 e2 -> pure (FETuple [e1, e2])) eL eR)
          ,Dict)

    shxConcat :: IShX sh1 -> IShX sh2 -> IShX (sh1 ++ sh2)
    shxConcat ZSX sh2 = sh2
    shxConcat (n :$% sh1) sh2 = n :$% shxConcat sh1 sh2

prettyExpr :: FEx -> BSB.Builder
prettyExpr = go 0
  where
    go :: Int -> FEx -> BSB.Builder
    go d = \case
      FELit l -> BSB.shortByteString l
      FETuple es -> BSB.char8 '(' <> mconcat (intersperse (BSB.char8 ',') (map (go 0) es)) <> BSB.char8 ')'
      FEList v -> BSB.char8 '[' <> mconcat (intersperse (BSB.char8 ',') (map (go 0) (toList v))) <> BSB.char8 ']'
      FEProj e n -> go 11 e <> BSB.char8 '.' <> BSB.shortByteString n
      FEApp n es -> bParen (d > 10) $
        BSB.shortByteString n <> mconcat [BSB.char8 ' ' <> go 11 e | e <- es]
      FEBinop e1 n e2 ->
        -- TODO: less redundant parentheses
        bParen (d > 9) $
          go 10 e1 <> BSB.char8 ' ' <> BSB.shortByteString n <> BSB.char8 ' ' <> go 10 e2
      FELam n e -> bParen (d > 0) $
        BSB.char8 '\\' <> BSB.shortByteString n <> bsb8 " -> " <> go 0 e
      FELet n e1 e2 -> bParen (d > 0) $
        bsb8 "let " <> BSB.shortByteString n <>
        bsb8 " = " <> go 0 e1 <>
        bsb8 " in " <> go 0 e2
      FEIf e1 e2 e3 -> bParen (d > 0) $
        bsb8 "if " <> go 0 e1 <>
        bsb8 "then " <> go 0 e2 <>
        bsb8 "else " <> go 0 e3

    bParen :: Bool -> BSB.Builder -> BSB.Builder
    bParen False b = b
    bParen True b = BSB.char8 '(' <> b <> BSB.char8 ')'

futTypeName :: ArgType t -> BSB.Builder
futTypeName (ATArray sh t) =
  bsb8 (concat ['[' : show n ++ "]" | n <- shxToList sh]) <> bsb8 (scalTyToMod t)

bsb8 :: String -> BSB.Builder
bsb8 = BSB.shortByteString . bss8

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
newtype SomeName (t :: TK) = SomeName Name
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
  AstProject1 a -> FEProj <$> compE env a <*> pure "0"
  AstProject2 a -> FEProj <$> compE env a <*> pure "1"
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
  AstConcreteK x -> pure $ FELitS (show x ++ scalTyToMod (toScalTy (ftkAst topexpr)))
  AstFloorK a -> FEApp "floor" <$:> [compE env a]
  AstFromIntegralK a -> FEApp (convertFun (toScalTy (ftkAst a)) (toScalTy (ftkAst topexpr))) <$:> [compE env a]
  AstCastK a -> FEApp (convertFun (toScalTy (ftkAst a)) (toScalTy (ftkAst topexpr))) <$:> [compE env a]

  AstPlusS a b -> repMap2T' (ftkAst a) (\_ x y -> pure (FEBinop x "+" y)) (compE env a) (compE env b)
  AstTimesS a b -> repMap2T' (ftkAst a) (\_ x y -> pure (FEBinop x "*" y)) (compE env a) (compE env b)
  AstN1S op a -> repMap1T' (ftkAst a) (\t x -> pure (compOpCodeNum1 t op x)) (compE env a)
  AstR1S op a -> repMap1T' (ftkAst a) (\t x -> pure (compOpCode1 t op x)) (compE env a)
  AstR2S op a b -> repMap2T' (ftkAst a) (\t x y -> pure (compOpCode2 t op x y)) (compE env a) (compE env b)
  AstI2S op a b -> repMap2T' (ftkAst a) (\t x y -> pure (compOpCodeIntegral2 t op x y)) (compE env a) (compE env b)
  AstConcreteS arr -> pure $ compConcrete arr

  -- TODO: AstIndexS etc.

  AstFromS targetty a -> case (ftkAst a, targetty) of
    (FTKS ZSS FTKScalar, STKScalar) -> compE env a
    (FTKS sh t, STKR n t')
      | Just Refl <- sameSTK (ftkToSTK t) t'
      , Just Refl <- testEquality (shsRank sh) n -> compE env a
    (FTKS sh t, STKX sh' t')
      | Just Refl <- sameSTK (ftkToSTK t) t'
      , Just Refl <- testEquality (ssxFromShape (shCvtSX sh)) sh' -> compE env a
    (FTKProduct _ _, STKProduct _ _) -> error "CompileFuthark: TODO FromS product"
    _ -> error "CompileFuthark: nonsensical AstFromS"

  AstMapAccumRDer{} -> error "CompileFuthark: unimplemented AstMapAccumRDer"
  AstMapAccumLDer{} -> error "CompileFuthark: unimplemented AstMapAccumLDer"
  _ -> error $ "CompileFuthark: unimplemented: " ++ concat (take 1 (words (show topexpr)))

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
  FTKR{} -> repMap2T topty addEltwise e1 e2
  FTKS{} -> repMap2T topty addEltwise e1 e2
  FTKX{} -> repMap2T topty addEltwise e1 e2
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
repMap1 :: Int -> (FEx -> IdGen FEx) -> FEx -> IdGen FEx
repMap1 0 f e = f e
repMap1 rank f e =
  FEApp "map" <$:>
    [iterateN (rank - 1) (\e' -> FEApp "map" [e']) <$> toLambda1 f
    ,pure e]

-- | The argument to the callback is NOT necessarily duplicable.
repMap2 :: Int -> (FEx -> FEx -> IdGen FEx) -> FEx -> FEx -> IdGen FEx
repMap2 0 f e1 e2 = f e1 e2
repMap2 rank f e1 e2 =
  FEApp "map2" <$:>
    [iterateN (rank - 1) (\e' -> FEApp "map" [e']) <$> toLambda2 f
    ,pure e1, pure e2]

repMap1T :: IsArrayType t => FullShapeTK t -> (FullShapeTK (ArrayTypeElt t) -> FEx -> IdGen FEx) -> FEx -> IdGen FEx
repMap1T ty f = repMap1 (arrayShapeRank ty) (f (arrayTypeElt ty))

repMap2T :: IsArrayType t => FullShapeTK t -> (FullShapeTK (ArrayTypeElt t) -> FEx -> FEx -> IdGen FEx) -> FEx -> FEx -> IdGen FEx
repMap2T ty f = repMap2 (arrayShapeRank ty) (f (arrayTypeElt ty))

repMap1T' :: IsArrayType t => FullShapeTK t -> (FullShapeTK (ArrayTypeElt t) -> FEx -> IdGen FEx) -> IdGen FEx -> IdGen FEx
repMap1T' ty f e = e >>= repMap1T ty f

repMap2T' :: IsArrayType t => FullShapeTK t -> (FullShapeTK (ArrayTypeElt t) -> FEx -> FEx -> IdGen FEx) -> IdGen FEx -> IdGen FEx -> IdGen FEx
repMap2T' ty f e1 e2 = do
  x <- e1
  y <- e2
  repMap2T ty f x y

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
deriving instance Show (ScalTy t)

instance TestEquality ScalTy where
  testEquality SI8   SI8   = Just Refl ; testEquality SI8   _ = Nothing
  testEquality SI16  SI16  = Just Refl ; testEquality SI16  _ = Nothing
  testEquality SI32  SI32  = Just Refl ; testEquality SI32  _ = Nothing
  testEquality SI64  SI64  = Just Refl ; testEquality SI64  _ = Nothing
  testEquality SU8   SU8   = Just Refl ; testEquality SU8   _ = Nothing
  testEquality SU16  SU16  = Just Refl ; testEquality SU16  _ = Nothing
  testEquality SU32  SU32  = Just Refl ; testEquality SU32  _ = Nothing
  testEquality SU64  SU64  = Just Refl ; testEquality SU64  _ = Nothing
  testEquality SF32  SF32  = Just Refl ; testEquality SF32  _ = Nothing
  testEquality SF64  SF64  = Just Refl ; testEquality SF64  _ = Nothing
  testEquality SBool SBool = Just Refl ; testEquality SBool _ = Nothing

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

class (Storable t, N.PrimElt t) => ScalTyDict t
instance (Storable t, N.PrimElt t) => ScalTyDict t

scalTyDict :: ScalTy t -> Dict ScalTyDict t
scalTyDict = \case
  -- SI8 -> Dict
  -- SI16 -> Dict
  SI32 -> Dict
  SI64 -> Dict
  -- SU8 -> Dict
  -- SU16 -> Dict
  -- SU32 -> Dict
  -- SU64 -> Dict
  -- SF16 -> Dict
  SF32 -> Dict
  SF64 -> Dict
  SBool -> Dict
  ty -> error $ "CompileToFuthark: type unsupported in ox-arrays: " ++ show ty

futLibrary :: ByteString
futLibrary = BS8.pack $
  "def first 'a 'b 'c (f: a -> b) (x: (a, c)): (b, c) = (f x.0, x.1)\n\
  \def second 'a 'b 'c (f: b -> c) (x: (a, b)): (a, c) = (x.0, f x.1)\n\
  \def bimap 'a 'b 'c 'd (f: a -> c) (g: b -> d) (x: (a, b)): (c, d) = (f x.0, g x.1)\n"

-- | Checks that the FTKs are actually equal, including shapes.
sameFTK :: FullShapeTK a -> FullShapeTK b -> Maybe (a :~: b)
sameFTK (FTKScalar @r1) (FTKScalar @r2)
  | Just Refl <- eqT @r1 @r2
  = Just Refl
sameFTK FTKScalar _ = Nothing
sameFTK (FTKS sh1 t1) (FTKS sh2 t2)
  | Just Refl <- shsEqual sh1 sh2
  , Just Refl <- sameFTK t1 t2
  = Just Refl
sameFTK FTKS{} _ = Nothing
sameFTK (FTKR sh1 t1) (FTKR sh2 t2)
  | Just Refl <- shrEqual sh1 sh2
  , Just Refl <- sameFTK t1 t2
  = Just Refl
sameFTK FTKR{} _ = Nothing
sameFTK (FTKX sh1 t1) (FTKX sh2 t2)
  | Just Refl <- shxEqual sh1 sh2
  , Just Refl <- sameFTK t1 t2
  = Just Refl
sameFTK FTKX{} _ = Nothing
sameFTK (FTKProduct a1 b1) (FTKProduct a2 b2)
  | Just Refl <- sameFTK a1 a2
  , Just Refl <- sameFTK b1 b2
  = Just Refl
sameFTK FTKProduct{} _ = Nothing

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
instance (Fresh a, Fresh b, Fresh c) => Fresh (a, b, c) where
  fresh = (,,) <$> fresh <*> fresh <*> fresh

runIdGen :: IdGen a -> a
runIdGen (IdGen m) = evalState m 1

bss8 :: String -> ShortByteString
bss8 = BSS.pack . map (fromIntegral . ord)
