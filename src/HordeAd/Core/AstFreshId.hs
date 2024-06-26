-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of the impurity escapes.
module HordeAd.Core.AstFreshId
  ( unRawHVector, rawHVector
  , funToAstIOR, funToAstR, funToAstIOS, funToAstS
  , fun1RToAst, fun1SToAst, fun1XToAst
  , fun1DToAst, fun1HToAst, fun1LToAst
  , funToAstRevIO, funToAstRev, funToAstFwdIO, funToAstFwd
  , funToAstIOI, funToAstI, funToAstIntVarIO, funToAstIntVar
  , funToVarsIx, funToAstIndex, funToVarsIxS, funToAstIndexS
  , resetVarCounter
  ) where

import Prelude

import           Control.Monad (mapAndUnzipM, replicateM)
import           Data.Array.Internal (valueOf)
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.List (unzip4, unzip6)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat)
import           System.IO.Unsafe (unsafePerformIO)

import           HordeAd.Core.Ast
import           HordeAd.Core.HVector
import           HordeAd.Core.Types
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

unRawHVector :: HVector (AstRaw s) -> HVector (AstRanked s)
unRawHVector =
  let f (DynamicRanked (AstRaw t)) = DynamicRanked t
      f (DynamicShaped (AstRawS t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

rawHVector :: HVector (AstRanked s) -> HVector (AstRaw s)
rawHVector =
  let f (DynamicRanked t) = DynamicRanked $ AstRaw t
      f (DynamicShaped t) = DynamicShaped $ AstRawS t
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

unsafeGetFreshAstVarName :: IO (AstVarName f r y)
{-# INLINE unsafeGetFreshAstVarName #-}
unsafeGetFreshAstVarName =
  AstVarName . intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

funToAstIOR :: forall n m s r r2. GoodScalar r
            => IShR n -> (AstRanked s r n -> AstRanked s r2 m)
            -> IO ( AstVarName (AstRanked s) r n
                  , AstDynamicVarName
                  , AstRanked s r2 m )
{-# INLINE funToAstIOR #-}
funToAstIOR sh f = do
  freshId <- unsafeGetFreshAstVarId
  return $! withShapeP (shapeToList sh) $ \(Proxy @p_sh) ->
    let varName = AstVarName freshId
        !x = f (AstVar sh varName)
    in (varName, AstDynamicVarName @Nat @r @p_sh freshId, x)

funToAstR :: GoodScalar r
          => IShR n -> (AstRanked s r n -> AstRanked s r2 m)
          -> (AstVarName (AstRanked s) r n, AstRanked s r2 m)
{-# NOINLINE funToAstR #-}
funToAstR sh f = unsafePerformIO $ do
  (!var, _, !ast) <- funToAstIOR sh f
  return (var, ast)

funToAstIOS :: forall sh sh2 s r r2. (KnownShS sh, GoodScalar r)
            => (AstShaped s r sh -> AstShaped s r2 sh2)
            -> IO ( AstVarName (AstShaped s) r sh
                  , AstDynamicVarName
                  , AstShaped s r2 sh2 )
{-# INLINE funToAstIOS #-}
funToAstIOS f = do
  freshId <- unsafeGetFreshAstVarId
  let varName = AstVarName freshId
      !x = f (AstVarS varName)
  return (varName, AstDynamicVarName @[Nat] @r @sh freshId, x)

funToAstS :: forall sh sh2 s r r2. (KnownShS sh, GoodScalar r)
          => (AstShaped s r sh -> AstShaped s r2 sh2)
          -> (AstVarName (AstShaped s) r sh, AstShaped s r2 sh2)
{-# NOINLINE funToAstS #-}
funToAstS f = unsafePerformIO $ do
  (!var, _, !ast) <- funToAstIOS f
  return (var, ast)

fun1RToAstIO :: (AstVarName (AstRanked s) r n -> AstRanked s r n)
             -> IO (AstRanked s r n)
{-# INLINE fun1RToAstIO #-}
fun1RToAstIO f = do
  !freshId <- unsafeGetFreshAstVarName
  return $! f freshId

fun1RToAst :: (AstVarName (AstRanked s) r n -> AstRanked s r n)
           -> AstRanked s r n
{-# NOINLINE fun1RToAst #-}
fun1RToAst f = unsafePerformIO $ fun1RToAstIO f

fun1SToAstIO :: (AstVarName (AstShaped s) r sh -> AstShaped s r sh)
             -> IO (AstShaped s r sh)
{-# INLINE fun1SToAstIO #-}
fun1SToAstIO f = do
  !freshId <- unsafeGetFreshAstVarName
  return $! f freshId

fun1SToAst :: (AstVarName (AstShaped s) r sh -> AstShaped s r sh)
           -> AstShaped s r sh
{-# NOINLINE fun1SToAst #-}
fun1SToAst f = unsafePerformIO $ fun1SToAstIO f

fun1XToAstIO :: VoidHVector -> ([AstDynamicVarName] -> AstHVector s)
             -> IO (AstHVector s)
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

fun1XToAst :: VoidHVector -> ([AstDynamicVarName] -> AstHVector s)
           -> AstHVector s
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
        !dynE = DynamicRanked @r2 (AstVar sh4 (AstVarName freshId))
    in (varE, dynE)
dynamicToVar (DynamicShapedDummy @r2 @sh2 _ _) = do
  freshId <- unsafeGetFreshAstVarId
  return $!
    let !varE = AstDynamicVarName @[Nat] @r2 @sh2 freshId
        dynE :: AstDynamic s
        !dynE = DynamicShaped @r2 @sh2 (AstVarS (AstVarName freshId))
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
              !dynE = DynamicRanked @r (AstVar sh (AstVarName freshId))
          in (varE, dynE, varE, dynE)
      f (DynamicShapedDummy @r @sh _ _) = do
        freshId <- unsafeGetFreshAstVarId
        return $!
          let !varE = AstDynamicVarName @[Nat] @r @sh freshId
              dynE :: AstDynamic s
              !dynE = DynamicShaped @r @sh (AstVarS (AstVarName freshId))
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
              dynE varId = DynamicRanked @r (AstVar sh (AstVarName varId))
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
              dynE varId = DynamicShaped @r @sh (AstVarS (AstVarName varId))
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
