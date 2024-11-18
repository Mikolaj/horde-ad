-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of the impurity escapes.
module HordeAd.Core.AstFreshId
  ( unRawHVector, rawHVector
  , funToAstIO, funToAst, fun1ToAst, fun1DToAst
  , funToAstRevIO, funToAstRev
  , funToAstFwdIO, funToAstFwd
  , funToAstIOI, funToAstI, funToAstIntVarIO, funToAstIntVar
  , funToVarsIx, funToAstIndex, funToVarsIxS, funToAstIxS
  , resetVarCounter
  ) where

import Prelude

import Control.Monad (replicateM)
import Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter, writeIORefU)
import Data.List.Index (imapM)
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat)
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Nested (KnownShS (..), Rank)

import HordeAd.Core.Ast
import HordeAd.Core.CarriersAst
import HordeAd.Core.HVector
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

unRawHVector :: HVector (AstRaw s) -> HVector (AstTensor AstMethodShare s)
unRawHVector =
  let f (DynamicRanked (AstRaw t)) = DynamicRanked t
      f (DynamicShaped (AstRaw t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

rawHVector :: HVector (AstTensor AstMethodShare s) -> HVector (AstRaw s)
rawHVector =
  let f (DynamicRanked t) = DynamicRanked $ AstRaw t
      f (DynamicShaped t) = DynamicShaped $ AstRaw t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 100000001)

-- | Only for tests, e.g., to ensure show applied to terms has stable length.
-- Tests using this need to be run with -ftest_seq to avoid variable confusion.
resetVarCounter :: IO ()
resetVarCounter = writeIORefU unsafeAstVarCounter 100000001

unsafeGetFreshAstVarId :: IO AstVarId
{-# INLINE unsafeGetFreshAstVarId #-}
unsafeGetFreshAstVarId =
  intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

unsafeGetFreshAstVarName :: TensorKind y => IO (AstVarName s y)
{-# INLINE unsafeGetFreshAstVarName #-}
unsafeGetFreshAstVarName =
  mkAstVarName . intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

funToAstIO :: forall y z s s2 ms. TensorKind y
           => FullTensorKind y
           -> (AstTensor ms s y -> AstTensor ms s2 z)
           -> IO ( AstVarName s y
                 , AstDynamicVarName
                 , AstTensor ms s2 z )
{-# INLINE funToAstIO #-}
funToAstIO sh f = do
  freshId <- unsafeGetFreshAstVarId
  case sh of
    FTKScalar @r ->
      return $!
        let varName = mkAstVarName freshId
            !x = f (AstVar FTKScalar varName)
            dynVar = AstDynamicVarName @Nat @r @'[] freshId
        in (varName, dynVar, x)
    FTKR shr (FTKScalar @r) ->
      return $! withShapeP (shapeToList shr) $ \(Proxy @p_sh) ->
        let varName = mkAstVarName freshId
            !x = f (AstVar sh varName)
            dynVar = AstDynamicVarName @Nat @r @p_sh freshId
        in (varName, dynVar, x)
    FTKS @sh shs (FTKScalar @r) -> do
      let varName = mkAstVarName freshId
          !x = f (AstVar sh varName)
          dynVar = withKnownShS shs $ AstDynamicVarName @[Nat] @r @sh freshId
      return (varName, dynVar, x)
    FTKX{} -> error "TODO"
    FTKProduct{} -> do
      let varName = mkAstVarName freshId
          !x = f (AstVar sh varName)
      return (varName, undefined, x)
    FTKUntyped{} -> do
      let varName = mkAstVarName freshId
          !x = f (AstVar sh varName)
      return (varName, undefined, x)
    _ -> error "TODO"

funToAst :: TensorKind y
         => FullTensorKind y
         -> (AstTensor ms s y -> AstTensor ms s2 z)
         -> (AstVarName s y, AstTensor ms s2 z)
{-# NOINLINE funToAst #-}
funToAst sh f = unsafePerformIO $ do
  (!var, _, !ast) <- funToAstIO sh f
  return (var, ast)

fun1ToAstIO :: TensorKind y
            => (AstVarName s y -> AstTensor ms s y)
            -> IO (AstTensor ms s y)
{-# INLINE fun1ToAstIO #-}
fun1ToAstIO f = do
  !freshId <- unsafeGetFreshAstVarName
  return $! f freshId

fun1ToAst :: TensorKind y
          => (AstVarName s y -> AstTensor ms s y)
          -> AstTensor ms s y
{-# NOINLINE fun1ToAst #-}
fun1ToAst f = unsafePerformIO $ fun1ToAstIO f

fun1DToAstIO :: VoidHVector
             -> ([AstDynamicVarName] -> HVector (AstTensor ms s) -> a)
             -> IO a
{-# INLINE fun1DToAstIO #-}
fun1DToAstIO od f = do
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  return $! f (V.toList vars) asts

fun1DToAst :: VoidHVector
           -> ([AstDynamicVarName] -> HVector (AstTensor ms s) -> a)
           -> a
{-# NOINLINE fun1DToAst #-}
fun1DToAst od f = unsafePerformIO $ fun1DToAstIO od f

dynamicToVar :: DynamicTensor VoidTensor
             -> IO (AstDynamicVarName, DynamicTensor (AstTensor ms s))
dynamicToVar (DynamicRankedDummy @r2 @sh2 _ _) = do
  freshId <- unsafeGetFreshAstVarId
  return $! withListSh (Proxy @sh2) $ \sh4 ->
    let !varE = AstDynamicVarName @Nat @r2 @sh2 freshId
        dynE :: AstDynamic ms s
        !dynE = DynamicRanked @r2 (AstVar (FTKR sh4 FTKScalar) (mkAstVarName freshId))
    in (varE, dynE)
dynamicToVar (DynamicShapedDummy @r2 @sh2 _ _) = do
  freshId <- unsafeGetFreshAstVarId
  return $!
    let !varE = AstDynamicVarName @[Nat] @r2 @sh2 freshId
        dynE :: AstDynamic ms s
        !dynE = DynamicShaped @r2 @sh2 (AstVar (FTKS knownShS FTKScalar) (mkAstVarName freshId))
    in (varE, dynE)

funToAstRevIO :: forall x. FullTensorKind x
              -> IO ( AstVarName PrimalSpan x
                    , AstTensor AstMethodShare PrimalSpan x
                    , AstVarName FullSpan x
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstRevIO #-}
funToAstRevIO ftk | Dict <- lemTensorKindOfF ftk = do
  freshId <- unsafeGetFreshAstVarId
  let varPrimal :: AstVarName PrimalSpan x
      varPrimal = mkAstVarName freshId
      var :: AstVarName FullSpan x
      var = mkAstVarName freshId
      astVarPrimal :: AstTensor AstMethodShare PrimalSpan x
      !astVarPrimal = AstVar ftk varPrimal
      astVar :: AstTensor AstMethodLet FullSpan x
      !astVar = AstVar ftk var
  case ftk of
    FTKScalar{} ->
      return (varPrimal, astVarPrimal, var, astVar)
    FTKR{} ->
      return (varPrimal, astVarPrimal, var, astVar)
    FTKS{} ->
      return (varPrimal, astVarPrimal, var, astVar)
    FTKX{} ->
      return (varPrimal, astVarPrimal, var, astVar)
    FTKProduct{} ->
      return (varPrimal, astVarPrimal, var, astVar)
    FTKUntyped parameters0 -> do
      let f :: Int -> DynamicTensor VoidTensor
            -> IO ( AstDynamic AstMethodShare PrimalSpan
                  , AstDynamic AstMethodLet FullSpan )
          f i (DynamicRankedDummy @r @sh _ _)
            | Dict <- lemKnownNatRank (knownShS @sh) = do
              return
                ( DynamicRanked @r @(Rank sh)
                                (AstProjectR astVarPrimal i)
                , DynamicRanked @r @(Rank sh)
                                (AstProjectR astVar i) )
          f i (DynamicShapedDummy @r @sh _ _) = do
            return
              ( DynamicShaped @r @sh (AstProjectS astVarPrimal i)
              , DynamicShaped @r @sh (AstProjectS astVar i) )
      (!astsPrimal, !asts) <- unzip <$> imapM f (V.toList parameters0)
      let !vp = AstMkHVector $ V.fromList astsPrimal
          !va = AstMkHVector $ V.fromList asts
      return (varPrimal, vp, var, va)

funToAstRev :: FullTensorKind x
            -> ( AstVarName PrimalSpan x
               , AstTensor AstMethodShare PrimalSpan x
               , AstVarName FullSpan x
               , AstTensor AstMethodLet FullSpan x )
{-# NOINLINE funToAstRev #-}
funToAstRev = unsafePerformIO . funToAstRevIO

funToAstFwdIO :: forall x. FullTensorKind x
              -> IO ( AstVarName PrimalSpan (ADTensorKind x)
                    , AstTensor AstMethodShare PrimalSpan (ADTensorKind x)
                    , AstVarName PrimalSpan x
                    , AstTensor AstMethodShare PrimalSpan x
                    , AstVarName FullSpan x
                    , AstTensor AstMethodLet FullSpan x )
{-# INLINE funToAstFwdIO #-}
funToAstFwdIO ftk | Dict <- lemTensorKindOfF ftk
                  , Dict <- lemTensorKindOfAD (stensorKind @x) = do
  freshIdDs <- unsafeGetFreshAstVarId
  freshId <- unsafeGetFreshAstVarId
  let varPrimalD :: AstVarName PrimalSpan (ADTensorKind x)
      varPrimalD = mkAstVarName freshIdDs
      varPrimal :: AstVarName PrimalSpan x
      varPrimal = mkAstVarName freshId
      var :: AstVarName FullSpan x
      var = mkAstVarName freshId
      astVarPrimalD :: AstTensor AstMethodShare PrimalSpan (ADTensorKind x)
      !astVarPrimalD = AstVar (aDTensorKind ftk) varPrimalD
      astVarPrimal :: AstTensor AstMethodShare PrimalSpan x
      !astVarPrimal = AstVar ftk varPrimal
      astVar :: AstTensor AstMethodLet FullSpan x
      !astVar = AstVar ftk var
  case ftk of
    FTKScalar{} ->
      return (varPrimalD, astVarPrimalD, varPrimal, astVarPrimal, var, astVar)
    FTKR{} ->
      return (varPrimalD, astVarPrimalD, varPrimal, astVarPrimal, var, astVar)
    FTKS{} ->
      return (varPrimalD, astVarPrimalD, varPrimal, astVarPrimal, var, astVar)
    FTKX{} ->
      return (varPrimalD, astVarPrimalD, varPrimal, astVarPrimal, var, astVar)
    FTKProduct{} ->
      return (varPrimalD, astVarPrimalD, varPrimal, astVarPrimal, var, astVar)
    FTKUntyped parameters0 -> do
      let f :: Int -> DynamicTensor VoidTensor
            -> IO ( AstDynamic AstMethodShare PrimalSpan
                  , AstDynamic AstMethodShare PrimalSpan
                  , AstDynamic AstMethodLet FullSpan )
          f i (DynamicRankedDummy @r @sh _ _)
            | Dict <- lemKnownNatRank (knownShS @sh) = do
              return
                ( DynamicRanked @r @(Rank sh)
                                (AstProjectR astVarPrimalD i)
                , DynamicRanked @r @(Rank sh)
                                (AstProjectR astVarPrimal i)
                , DynamicRanked @r @(Rank sh)
                                (AstProjectR astVar i) )
          f i (DynamicShapedDummy @r @sh _ _) = do
            return
              ( DynamicShaped @r @sh (AstProjectS astVarPrimalD i)
              , DynamicShaped @r @sh (AstProjectS astVarPrimal i)
              , DynamicShaped @r @sh (AstProjectS astVar i) )
      (!astsPrimalD, !astsPrimal, !asts)
        <- unzip3 <$> imapM f (V.toList parameters0)
      let !vD = AstMkHVector $ V.fromList astsPrimalD
          !vp = AstMkHVector $ V.fromList astsPrimal
          !va = AstMkHVector $ V.fromList asts
      return (varPrimalD, vD, varPrimal, vp, var, va)

funToAstFwd :: FullTensorKind x
            -> ( AstVarName PrimalSpan (ADTensorKind x)
               , AstTensor AstMethodShare PrimalSpan (ADTensorKind x)
               , AstVarName PrimalSpan x
               , AstTensor AstMethodShare PrimalSpan x
               , AstVarName FullSpan x
               , AstTensor AstMethodLet FullSpan x )
{-# NOINLINE funToAstFwd #-}
funToAstFwd = unsafePerformIO . funToAstFwdIO

funToAstIOI :: (AstInt ms -> t) -> IO (IntVarName, t)
{-# INLINE funToAstIOI #-}
funToAstIOI f = do
  !varName <- unsafeGetFreshAstVarName
  let !x = f (AstIntVar varName)
  return (varName, x)

funToAstI :: (AstInt ms -> t) -> (IntVarName, t)
{-# NOINLINE funToAstI #-}
funToAstI = unsafePerformIO . funToAstIOI

funToAstIntVarIO :: ((IntVarName, AstInt ms) -> a) -> IO a
{-# INLINE funToAstIntVarIO #-}
funToAstIntVarIO f = do
  !varName <- unsafeGetFreshAstVarName
  let !ast = AstIntVar varName
  return $! f (varName, ast)

funToAstIntVar :: ((IntVarName, AstInt ms) -> a) -> a
{-# NOINLINE funToAstIntVar #-}
funToAstIntVar = unsafePerformIO . funToAstIntVarIO

funToVarsIxIO
  :: KnownNat m
  => Int -> ((AstVarList m, AstIndex ms m) -> a) -> IO a
{-# INLINE funToVarsIxIO #-}
funToVarsIxIO m f = do
  varList <- replicateM m unsafeGetFreshAstVarName
  let !vars = listToSized varList
      !ix = listToIndex $ map AstIntVar varList
  return $! f (vars, ix)

funToVarsIx
  :: KnownNat m
  => Int -> ((AstVarList m, AstIndex ms m) -> a) -> a
{-# NOINLINE funToVarsIx #-}
funToVarsIx m = unsafePerformIO . funToVarsIxIO m

funToAstIndex
  :: forall m p ms. KnownNat m
  => (AstIndex ms m -> AstIndex ms p) -> (AstVarList m, AstIndex ms p)
{-# NOINLINE funToAstIndex #-}
funToAstIndex f = unsafePerformIO . funToVarsIxIO (valueOf @m)
                  $ \ (!vars, !ix) -> let !x = f ix in (vars, x)

funToVarsIxIOS
  :: forall sh a ms. KnownShS sh
  => ((AstVarListS sh, AstIxS ms sh) -> a) -> IO a
{-# INLINE funToVarsIxIOS #-}
funToVarsIxIOS f = do
  let p = length $ shapeT @sh
  varList <- replicateM p unsafeGetFreshAstVarName
  let !vars = ShapedList.listToSized varList
      !ix = ShapedList.listToIndex $ map AstIntVar varList
  return $! f (vars, ix)

funToVarsIxS
  :: KnownShS sh
  => ((AstVarListS sh, AstIxS ms sh) -> a) -> a
{-# NOINLINE funToVarsIxS #-}
funToVarsIxS = unsafePerformIO . funToVarsIxIOS

funToAstIxS
  :: KnownShS sh
  => (AstIxS ms sh -> AstIxS ms sh2) -> (AstVarListS sh, AstIxS ms sh2)
{-# NOINLINE funToAstIxS #-}
funToAstIxS f = unsafePerformIO $ funToVarsIxIOS
                   $ \ (!vars, !ix) -> let !x = f ix in (vars, x)
