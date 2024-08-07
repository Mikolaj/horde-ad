-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of the impurity escapes.
module HordeAd.Core.AstFreshId
  ( unRawHVector, rawHVector
  , funToAstIO, funToAst, fun2ToAst
  , fun1RToAst, fun1SToAst, fun1XToAst
  , fun1DToAst, fun1HToAst, fun1LToAst
  , funToAstRevIO, funToAstRev, funToAstFwdIO, funToAstFwd
  , funToAstIOI, funToAstI, funToAstIntVarIO, funToAstIntVar
  , funToVarsIx, funToAstIndex, funToVarsIxS, funToAstIndexS
  , resetVarCounter
  ) where

import Prelude

import Control.Monad (mapAndUnzipM, replicateM)
import Data.Array.Internal (valueOf)
import Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter, writeIORefU)
import Data.List (unzip4, unzip6)
import Data.Proxy (Proxy (Proxy))
import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat, Nat)
import System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.HVector
import HordeAd.Core.Types
import HordeAd.Util.ShapedList qualified as ShapedList
import HordeAd.Util.SizedList

unRawHVector :: HVector (AstRaw s) -> HVector (AstRanked s)
unRawHVector =
  let f (DynamicRanked (AstRaw t)) = DynamicRanked (AstRanked t)
      f (DynamicShaped (AstRawS t)) = DynamicShaped (AstShaped t)
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

rawHVector :: HVector (AstRanked s) -> HVector (AstRaw s)
rawHVector =
  let f (DynamicRanked (AstRanked t)) = DynamicRanked $ AstRaw t
      f (DynamicShaped (AstShaped t)) = DynamicShaped $ AstRawS t
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

funToAstIO :: forall y z s. TensorKind y
           => TensorKindFull y
           -> (AstTensor s y -> AstTensor s z)
           -> IO ( AstVarName s y
                 , AstDynamicVarName
                 , AstTensor s z )
{-# INLINE funToAstIO #-}
funToAstIO sh f = do
  freshId <- unsafeGetFreshAstVarId
  case sh of
    FTKR @r shr ->
      return $! withShapeP (shapeToList shr) $ \(Proxy @p_sh) ->
        let varName = mkAstVarName freshId
            !x = f (AstVar sh varName)
            dynVar = AstDynamicVarName @Nat @r @p_sh freshId
        in (varName, dynVar, x)
    FTKS @r @sh -> do
      let varName = mkAstVarName freshId
          !x = f (AstVar sh varName)
          dynVar = AstDynamicVarName @[Nat] @r @sh freshId
      return (varName, dynVar, x)
    FTKProduct{} -> do
      let varName = mkAstVarName freshId
          !x = f (AstVar sh varName)
      return (varName, undefined, x)
    FTKUntyped{} -> do
      let varName = mkAstVarName freshId
          !x = f (AstVar sh varName)
      return (varName, undefined, x)

funToAst :: TensorKind y
         => TensorKindFull y
         -> (AstTensor s y -> AstTensor s z)
         -> (AstVarName s y, AstTensor s z)
{-# NOINLINE funToAst #-}
funToAst sh f = unsafePerformIO $ do
  (!var, _, !ast) <- funToAstIO sh f
  return (var, ast)

fun2ToAstIO :: (TensorKind x, TensorKind y)
            => TensorKindFull x -> TensorKindFull y
            -> (AstVarName s x -> AstVarName s y
                -> AstTensor s x -> AstTensor s y
                -> AstTensor s z)
            -> IO (AstTensor s z )
{-# INLINE fun2ToAstIO #-}
fun2ToAstIO shX shY f = do
  freshIdX <- unsafeGetFreshAstVarId
  freshIdY <- unsafeGetFreshAstVarId
  let varNameX = mkAstVarName freshIdX
      varNameY = mkAstVarName freshIdY
  return $! f varNameX varNameY (AstVar shX varNameX) (AstVar shY varNameY)

fun2ToAst :: (TensorKind x, TensorKind y)
          => TensorKindFull x -> TensorKindFull y
          -> (AstVarName s x -> AstVarName s y
              -> AstTensor s x -> AstTensor s y
              -> AstTensor s z)
          -> AstTensor s z
{-# NOINLINE fun2ToAst #-}
fun2ToAst shX shY f = unsafePerformIO $ fun2ToAstIO shX shY f

fun1RToAstIO :: forall s r n. (KnownNat n, GoodScalar r)
             => (AstVarName s (TKR r n) -> AstTensor s (TKR r n))
             -> IO (AstTensor s (TKR r n))
{-# INLINE fun1RToAstIO #-}
fun1RToAstIO f = do
  !freshId <- unsafeGetFreshAstVarName
  return $! f freshId

fun1RToAst :: (KnownNat n, GoodScalar r)
           => (AstVarName s (TKR r n) -> AstTensor s (TKR r n))
           -> AstTensor s (TKR r n)
{-# NOINLINE fun1RToAst #-}
fun1RToAst f = unsafePerformIO $ fun1RToAstIO f

fun1SToAstIO :: forall s r sh. (KnownShS sh, GoodScalar r)
             => (AstVarName s (TKS r sh) -> AstTensor s (TKS r sh))
             -> IO (AstTensor s (TKS r sh))
{-# INLINE fun1SToAstIO #-}
fun1SToAstIO f = do
  !freshId <- unsafeGetFreshAstVarName
  return $! f freshId

fun1SToAst :: (KnownShS sh, GoodScalar r)
           => (AstVarName s (TKS r sh) -> AstTensor s (TKS r sh))
           -> AstTensor s (TKS r sh)
{-# NOINLINE fun1SToAst #-}
fun1SToAst f = unsafePerformIO $ fun1SToAstIO f

fun1XToAstIO :: VoidHVector -> ([AstDynamicVarName] -> AstTensor s TKUntyped)
             -> IO (AstTensor s TKUntyped)
{-# INLINE fun1XToAstIO #-}
fun1XToAstIO shs g = do
  let f :: DynamicTensor VoidTensor
        -> IO AstDynamicVarName
      f (DynamicRankedDummy @r @sh _ _) = do
        freshId <- unsafeGetFreshAstVarId
        return $! AstDynamicVarName @Nat @r @sh freshId
      f (DynamicShapedDummy @r @sh _ _) = do
        freshId <- unsafeGetFreshAstVarId
        return $! AstDynamicVarName @[Nat] @r @sh freshId
  !vars <- mapM f (V.toList shs)
  return $! g vars

fun1XToAst :: VoidHVector -> ([AstDynamicVarName] -> AstTensor s TKUntyped)
           -> AstTensor s TKUntyped
{-# NOINLINE fun1XToAst #-}
fun1XToAst shs f = unsafePerformIO $ fun1XToAstIO shs f

fun1LToAstIO :: [VoidHVector]
             -> ([[AstDynamicVarName]] -> [HVector (AstRanked s)] -> a)
             -> IO a
{-# INLINE fun1LToAstIO #-}
fun1LToAstIO shss f = do
  (!vars, !asts) <- mapAndUnzipM (fmap V.unzip . V.mapM dynamicToVar) shss
  return $! f (map V.toList vars) asts

fun1LToAst :: [VoidHVector]
           -> ([[AstDynamicVarName]] -> [HVector (AstRanked s)] -> a)
           -> a
{-# NOINLINE fun1LToAst #-}
fun1LToAst shss f = unsafePerformIO $ fun1LToAstIO shss f

fun1DToAstIO :: VoidHVector
             -> ([AstDynamicVarName] -> HVector (AstRanked s) -> a)
             -> IO a
{-# INLINE fun1DToAstIO #-}
fun1DToAstIO od f = do
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  return $! f (V.toList vars) asts

fun1DToAst :: VoidHVector
           -> ([AstDynamicVarName] -> HVector (AstRanked s) -> a)
           -> a
{-# NOINLINE fun1DToAst #-}
fun1DToAst od f = unsafePerformIO $ fun1DToAstIO od f

fun1HToAstIO :: [VoidHVector] -> VoidHVector
             -> (AstVarId -> AstHFun -> a)
             -> IO a
{-# INLINE fun1HToAstIO #-}
fun1HToAstIO shss shs f = do
  !freshId <- unsafeGetFreshAstVarId
  return $! f freshId (AstVarHFun shss shs freshId)

fun1HToAst :: [VoidHVector] -> VoidHVector
           -> (AstVarId -> AstHFun -> a)
           -> a
{-# NOINLINE fun1HToAst #-}
fun1HToAst shss shs f = unsafePerformIO $ fun1HToAstIO shss shs f

dynamicToVar :: DynamicTensor VoidTensor
             -> IO (AstDynamicVarName, DynamicTensor (AstRanked s))
dynamicToVar (DynamicRankedDummy @r2 @sh2 _ _) = do
  freshId <- unsafeGetFreshAstVarId
  return $! withListSh (Proxy @sh2) $ \sh4 ->
    let !varE = AstDynamicVarName @Nat @r2 @sh2 freshId
        dynE :: AstDynamic s
        !dynE = DynamicRanked @r2 (AstRanked $ AstVar (FTKR sh4) (mkAstVarName freshId))
    in (varE, dynE)
dynamicToVar (DynamicShapedDummy @r2 @sh2 _ _) = do
  freshId <- unsafeGetFreshAstVarId
  return $!
    let !varE = AstDynamicVarName @[Nat] @r2 @sh2 freshId
        dynE :: AstDynamic s
        !dynE = DynamicShaped @r2 @sh2 (AstShaped $ AstVar FTKS (mkAstVarName freshId))
    in (varE, dynE)

funToAstRevIO :: VoidHVector
              -> IO ( [AstDynamicVarName]
                    , HVector (AstRaw PrimalSpan)
                    , [AstDynamicVarName]
                    , HVector (AstRanked FullSpan) )
{-# INLINE funToAstRevIO #-}
funToAstRevIO parameters0 = do
  let f :: DynamicTensor VoidTensor
        -> IO ( AstDynamicVarName, AstDynamic PrimalSpan
              , AstDynamicVarName, AstDynamic FullSpan )
      f (DynamicRankedDummy @r @sh _ _) = do
        freshId <- unsafeGetFreshAstVarId
        return $! withListSh (Proxy @sh) $ \sh ->
          let !varE = AstDynamicVarName @Nat @r @sh freshId
              dynE :: AstDynamic s
              !dynE = DynamicRanked @r (AstRanked $ AstVar (FTKR sh) (mkAstVarName freshId))
          in (varE, dynE, varE, dynE)
      f (DynamicShapedDummy @r @sh _ _) = do
        freshId <- unsafeGetFreshAstVarId
        return $!
          let !varE = AstDynamicVarName @[Nat] @r @sh freshId
              dynE :: AstDynamic s
              !dynE = DynamicShaped @r @sh (AstShaped $ AstVar FTKS (mkAstVarName freshId))
          in (varE, dynE, varE, dynE)
  (!varsPrimal, !astsPrimal, !vars, !asts)
    <- unzip4 <$> mapM f (V.toList parameters0)
  let !vp = V.fromList astsPrimal
      !va = V.fromList asts
  return (varsPrimal, rawHVector vp, vars, va)

funToAstRev :: VoidHVector
            -> ( [AstDynamicVarName]
               , HVector (AstRaw PrimalSpan)
               , [AstDynamicVarName]
               , HVector (AstRanked FullSpan) )
{-# NOINLINE funToAstRev #-}
funToAstRev parameters0 = unsafePerformIO $ funToAstRevIO parameters0

funToAstFwdIO :: VoidHVector
              -> IO ( [AstDynamicVarName]
                    , HVector (AstRaw PrimalSpan)
                    , [AstDynamicVarName]
                    , HVector (AstRaw PrimalSpan)
                    , [AstDynamicVarName]
                    , HVector (AstRanked FullSpan) )
{-# INLINE funToAstFwdIO #-}
funToAstFwdIO parameters0 = do
  let f :: DynamicTensor VoidTensor
        -> IO ( AstDynamicVarName, AstDynamic PrimalSpan
              , AstDynamicVarName, AstDynamic PrimalSpan
              , AstDynamicVarName, AstDynamic FullSpan )
      f (DynamicRankedDummy @r @sh _ _) = do
        freshIdDs <- unsafeGetFreshAstVarId
        freshId <- unsafeGetFreshAstVarId
        return $! withListSh (Proxy @sh) $ \sh ->
          let varE :: AstVarId -> AstDynamicVarName
              varE = AstDynamicVarName @Nat @r @sh
              dynE :: AstVarId -> AstDynamic s
              dynE varId = DynamicRanked @r (AstRanked $ AstVar (FTKR sh) (mkAstVarName varId))
              !vd = varE freshIdDs
              !dd = dynE freshIdDs
              !vi = varE freshId
              di :: AstDynamic s
              !di = dynE freshId
          in (vd, dd, vi, di, vi, di)
      f (DynamicShapedDummy @r @sh _ _) = do
        freshIdDs <- unsafeGetFreshAstVarId
        freshId <- unsafeGetFreshAstVarId
        return $!
          let varE :: AstVarId -> AstDynamicVarName
              varE = AstDynamicVarName @[Nat] @r @sh
              dynE :: AstVarId -> AstDynamic s
              dynE varId = DynamicShaped @r @sh (AstShaped $ AstVar FTKS (mkAstVarName varId))
              !vd = varE freshIdDs
              !dd = dynE freshIdDs
              !vi = varE freshId
              di :: AstDynamic s
              !di = dynE freshId
          in (vd, dd, vi, di, vi, di)
  (!varsPrimalDs, !astsPrimalDs, !varsPrimal, !astsPrimal, !vars, !asts)
    <- unzip6 <$> mapM f (V.toList parameters0)
  let !vd = V.fromList astsPrimalDs
      !vp = V.fromList astsPrimal
      !va = V.fromList asts
  return (varsPrimalDs, rawHVector vd, varsPrimal, rawHVector vp, vars, va)

funToAstFwd :: VoidHVector
            -> ( [AstDynamicVarName]
               , HVector (AstRaw PrimalSpan)
               , [AstDynamicVarName]
               , HVector (AstRaw PrimalSpan)
               , [AstDynamicVarName]
               , HVector (AstRanked FullSpan) )
{-# NOINLINE funToAstFwd #-}
funToAstFwd parameters0 = unsafePerformIO $ funToAstFwdIO parameters0

funToAstIOI :: (AstInt -> t) -> IO (IntVarName, t)
{-# INLINE funToAstIOI #-}
funToAstIOI f = do
  !varName <- unsafeGetFreshAstVarName
  let !x = f (AstIntVar varName)
  return (varName, x)

funToAstI :: (AstInt -> t) -> (IntVarName, t)
{-# NOINLINE funToAstI #-}
funToAstI = unsafePerformIO . funToAstIOI

funToAstIntVarIO :: ((IntVarName, AstInt) -> a) -> IO a
{-# INLINE funToAstIntVarIO #-}
funToAstIntVarIO f = do
  !varName <- unsafeGetFreshAstVarName
  let !ast = AstIntVar varName
  return $! f (varName, ast)

funToAstIntVar :: ((IntVarName, AstInt) -> a) -> a
{-# NOINLINE funToAstIntVar #-}
funToAstIntVar = unsafePerformIO . funToAstIntVarIO

funToVarsIxIO
  :: KnownNat m
  => Int -> ((AstVarList m, AstIndex m) -> a) -> IO a
{-# INLINE funToVarsIxIO #-}
funToVarsIxIO m f = do
  varList <- replicateM m unsafeGetFreshAstVarName
  let !vars = listToSized varList
      !ix = listToIndex $ map AstIntVar varList
  return $! f (vars, ix)

funToVarsIx
  :: KnownNat m
  => Int -> ((AstVarList m, AstIndex m) -> a) -> a
{-# NOINLINE funToVarsIx #-}
funToVarsIx m = unsafePerformIO . funToVarsIxIO m

funToAstIndex
  :: forall m p. KnownNat m
  => (AstIndex m -> AstIndex p) -> (AstVarList m, AstIndex p)
{-# NOINLINE funToAstIndex #-}
funToAstIndex f = unsafePerformIO . funToVarsIxIO (valueOf @m)
                  $ \ (!vars, !ix) -> let !x = f ix in (vars, x)

funToVarsIxIOS
  :: forall sh a. KnownShS sh
  => ((AstVarListS sh, AstIndexS sh) -> a) -> IO a
{-# INLINE funToVarsIxIOS #-}
funToVarsIxIOS f = do
  let p = length $ shapeT @sh
  varList <- replicateM p unsafeGetFreshAstVarName
  let !vars = ShapedList.listToSized varList
      !ix = ShapedList.listToIndex $ map AstIntVar varList
  return $! f (vars, ix)

funToVarsIxS
  :: KnownShS sh
  => ((AstVarListS sh, AstIndexS sh) -> a) -> a
{-# NOINLINE funToVarsIxS #-}
funToVarsIxS = unsafePerformIO . funToVarsIxIOS

funToAstIndexS
  :: KnownShS sh
  => (AstIndexS sh -> AstIndexS sh2) -> (AstVarListS sh, AstIndexS sh2)
{-# NOINLINE funToAstIndexS #-}
funToAstIndexS f = unsafePerformIO $ funToVarsIxIOS
                   $ \ (!vars, !ix) -> let !x = f ix in (vars, x)
