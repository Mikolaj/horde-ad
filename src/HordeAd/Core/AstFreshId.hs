-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of it escapes.
module HordeAd.Core.AstFreshId
  ( astRegisterFun, astRegisterFunS, astRegisterADShare, astRegisterADShareS
  , funToAstIOR, funToAstR, fun1DToAst
  , fun2ToAstR, fun2ToAstS, fun2DToAstR, fun2DToAstS
  , fun3ToAstR, fun3ToAstS, fun3DToAstR, fun3DToAstS
  , fun4ToAstR, fun4ToAstS, fun4DToAstR, fun4DToAstS
  , funToAstDomains
  , funToAstRevIO, funToAstRev, funToAstFwdIO, funToAstFwd
  , funToAstIOI, funToAstI, funToAstIndexIO, funToAstIndex
  , funToAstIOS, funToAstS, funToAstIndexIOS, funToAstIndexS
  , resetVarCounter
  ) where

import Prelude

import           Control.Monad (replicateM)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import           Data.Bifunctor.Flip
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.List (unzip4, unzip6)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat)
import           System.IO.Unsafe (unsafePerformIO)

import           HordeAd.Core.Ast
import           HordeAd.Core.AstTools
import           HordeAd.Core.TensorClass (DomainsOD)
import           HordeAd.Core.Types
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedIndex
import           HordeAd.Util.SizedList

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

astRegisterFun
  :: (GoodScalar r, KnownNat n)
  => AstRanked s r n -> AstBindingsD (AstRanked s)
  -> (AstBindingsD (AstRanked s), AstRanked s r n)
{-# NOINLINE astRegisterFun #-}
astRegisterFun !r !l | astIsSmall True r = (l, r)
astRegisterFun r l = unsafePerformIO $ do
  !freshId <- unsafeGetFreshAstVarId
  let !r2 = AstVar (shapeAst r) $ AstVarName freshId
      !d = DynamicRanked r
  return (AstBindingsSimple freshId d : l, r2)

astRegisterFunS
  :: (Sh.Shape sh, GoodScalar r)
  => AstShaped s r sh -> AstBindingsD (AstRanked s)
  -> (AstBindingsD (AstRanked s), AstShaped s r sh)
{-# NOINLINE astRegisterFunS #-}
astRegisterFunS !r !l | astIsSmallS True r = (l, r)
astRegisterFunS r l = unsafePerformIO $ do
  !freshId <- unsafeGetFreshAstVarId
  let !r2 = AstVarS $ AstVarName freshId
      !d = DynamicShaped r
  return (AstBindingsSimple freshId d : l, r2)

astRegisterADShare :: (GoodScalar r, KnownNat n)
                   => AstRanked PrimalSpan r n -> ADShare
                   -> (ADShare, AstRanked PrimalSpan r n)
{-# NOINLINE astRegisterADShare #-}
astRegisterADShare !r !l | astIsSmall True r = (l, r)
astRegisterADShare r l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !l2 = insertADShare freshId (DynamicRanked r) l
      !r2 = AstVar (shapeAst r) $ AstVarName freshId
  return (l2, r2)

astRegisterADShareS :: (GoodScalar r, Sh.Shape sh)
                    => AstShaped PrimalSpan r sh -> ADShare
                    -> (ADShare, AstShaped PrimalSpan r sh)
{-# NOINLINE astRegisterADShareS #-}
astRegisterADShareS !r !l | astIsSmallS True r = (l, r)
astRegisterADShareS r l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !l2 = insertADShare freshId (DynamicShaped r) l
      !r2 = AstVarS $ AstVarName freshId
  return (l2, r2)

funToAstIOR :: forall n m s r r2. GoodScalar r
            => ShapeInt n -> (AstRanked s r n -> AstRanked s r2 m)
            -> IO ( AstVarName (AstRanked s) r n
                  , AstDynamicVarName
                  , AstRanked s r2 m )
{-# INLINE funToAstIOR #-}
funToAstIOR sh f = do
  freshId <- unsafeGetFreshAstVarId
  return $! Sh.withShapeP (shapeToList sh) $ \(Proxy :: Proxy p_sh) ->
    let varName = AstVarName freshId
        !x = f (AstVar sh varName)
    in (varName, AstDynamicVarName @Nat @r @p_sh freshId, x)

funToAstR :: GoodScalar r
          => ShapeInt n -> (AstRanked s r n -> AstRanked s r2 m)
          -> (AstVarName (AstRanked s) r n, AstRanked s r2 m)
{-# NOINLINE funToAstR #-}
funToAstR sh f = unsafePerformIO $ do
  (!var, _, !ast) <- funToAstIOR sh f
  return (var, ast)

funToAstIOS :: forall sh sh2 s r r2. (Sh.Shape sh, GoodScalar r)
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

funToAstS :: forall sh sh2 s r r2. (Sh.Shape sh, GoodScalar r)
          => (AstShaped s r sh -> AstShaped s r2 sh2)
          -> (AstVarName (AstShaped s) r sh, AstShaped s r2 sh2)
{-# NOINLINE funToAstS #-}
funToAstS f = unsafePerformIO $ do
  (!var, _, !ast) <- funToAstIOS f
  return (var, ast)

fun1DToAstIO :: DomainsOD
             -> ([AstDynamicVarName] -> Domains (AstRanked s) -> a)
             -> IO a
{-# INLINE fun1DToAstIO #-}
fun1DToAstIO od f = do
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  return $! f (V.toList vars) asts

fun1DToAst :: DomainsOD
           -> ([AstDynamicVarName] -> Domains (AstRanked s) -> a)
           -> a
{-# NOINLINE fun1DToAst #-}
fun1DToAst od f = unsafePerformIO $ fun1DToAstIO od f

fun2ToAstIOR :: ShapeInt n
             -> ShapeInt m
             -> (AstRanked s rn n -> AstRanked s rm m -> AstRanked s rn n)
             -> IO ( AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rm m
                   , AstRanked s rn n )
{-# INLINE fun2ToAstIOR #-}
fun2ToAstIOR shn shm f = do
  nvarName <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  let !x = f (AstVar shn nvarName) (AstVar shm mvarName)
  return (nvarName, mvarName, x)

fun2ToAstR :: ShapeInt n
           -> ShapeInt m
           -> (AstRanked s rn n -> AstRanked s rm m -> AstRanked s rn n)
           -> ( AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rm m
              , AstRanked s rn n )
{-# NOINLINE fun2ToAstR #-}
fun2ToAstR shn shm f = unsafePerformIO $ fun2ToAstIOR shn shm f

fun2ToAstIOS :: (AstShaped s rn shn -> AstShaped s rm shm -> AstShaped s rn shn)
             -> IO ( AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rm shm
                   , AstShaped s rn shn )
{-# INLINE fun2ToAstIOS #-}
fun2ToAstIOS f = do
  nvarName <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  let !x = f (AstVarS nvarName) (AstVarS mvarName)
  return (nvarName, mvarName, x)

fun2ToAstS :: (AstShaped s rn shn -> AstShaped s rm shm -> AstShaped s rn shn)
           -> ( AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rm shm
              , AstShaped s rn shn )
{-# NOINLINE fun2ToAstS #-}
fun2ToAstS f = unsafePerformIO $ fun2ToAstIOS f

fun2DToAstIOR :: ShapeInt n
              -> (AstRanked s rn n -> Domains (AstRanked s)
                  -> AstRanked s rn n)
              -> DomainsOD
              -> IO ( AstVarName (AstRanked s) rn n
                    , [AstDynamicVarName]
                    , AstRanked s rn n )
{-# INLINE fun2DToAstIOR #-}
fun2DToAstIOR shn f od = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVar shn nvarName) asts
  return (nvarName, V.toList vars, x)

fun2DToAstR :: ShapeInt n
            -> (AstRanked s rn n -> Domains (AstRanked s)
                -> AstRanked s rn n)
            -> DomainsOD
            -> ( AstVarName (AstRanked s) rn n
               , [AstDynamicVarName]
               , AstRanked s rn n )
{-# NOINLINE fun2DToAstR #-}
fun2DToAstR shn f od = unsafePerformIO $ fun2DToAstIOR shn f od

fun2DToAstIOS :: (AstShaped s rn shn -> Domains (AstRanked s)
                  -> AstShaped s rn shn)
              -> DomainsOD
              -> IO ( AstVarName (AstShaped s) rn shn
                    , [AstDynamicVarName]
                    , AstShaped s rn shn )
{-# INLINE fun2DToAstIOS #-}
fun2DToAstIOS f od = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVarS nvarName) asts
  return (nvarName, V.toList vars, x)

fun2DToAstS :: (AstShaped s rn shn -> Domains (AstRanked s)
                -> AstShaped s rn shn)
            -> DomainsOD
            -> ( AstVarName (AstShaped s) rn shn
               , [AstDynamicVarName]
               , AstShaped s rn shn )
{-# NOINLINE fun2DToAstS #-}
fun2DToAstS f od = unsafePerformIO $ fun2DToAstIOS f od

fun3ToAstIOR :: ShapeInt n
             -> ShapeInt m
             -> (AstRanked s rn n -> AstRanked s rn n -> AstRanked s rm m
                 -> AstDomains s)
             -> IO ( AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rm m
                   , AstDomains s )
{-# INLINE fun3ToAstIOR #-}
fun3ToAstIOR shn shm f = do
  nvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  let !x = f (AstVar shn nvarName) (AstVar shn nvarName2) (AstVar shm mvarName)
  return (nvarName, nvarName2, mvarName, x)

fun3ToAstR :: ShapeInt n
           -> ShapeInt m
           -> (AstRanked s rn n -> AstRanked s rn n -> AstRanked s rm m
               -> AstDomains s)
           -> ( AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rm m
              , AstDomains s )
{-# NOINLINE fun3ToAstR #-}
fun3ToAstR shn shm f = unsafePerformIO $ fun3ToAstIOR shn shm f

fun3ToAstIOS :: (AstShaped s rn shn -> AstShaped s rn shn -> AstShaped s rm shm
                 -> AstDomains s)
             -> IO ( AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rm shm
                   , AstDomains s )
{-# INLINE fun3ToAstIOS #-}
fun3ToAstIOS f = do
  nvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  let !x = f (AstVarS nvarName) (AstVarS nvarName2) (AstVarS mvarName)
  return (nvarName, nvarName2, mvarName, x)

fun3ToAstS :: (AstShaped s rn shn -> AstShaped s rn shn -> AstShaped s rm shm
               -> AstDomains s)
           -> ( AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rm shm
              , AstDomains s )
{-# NOINLINE fun3ToAstS #-}
fun3ToAstS f = unsafePerformIO $ fun3ToAstIOS f

fun3DToAstIOR :: ShapeInt n
              -> (AstRanked s rn n -> AstRanked s rn n -> Domains (AstRanked s)
                  -> AstDomains s)
              -> DomainsOD
              -> IO ( AstVarName (AstRanked s) rn n
                    , AstVarName (AstRanked s) rn n
                    , [AstDynamicVarName]
                    , AstDomains s )
{-# INLINE fun3DToAstIOR #-}
fun3DToAstIOR shn f od = do
  nvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVar shn nvarName) (AstVar shn nvarName2) asts
  return (nvarName, nvarName2, V.toList vars, x)

fun3DToAstR :: ShapeInt n
            -> (AstRanked s rn n -> AstRanked s rn n -> Domains (AstRanked s)
                -> AstDomains s)
            -> DomainsOD
            -> ( AstVarName (AstRanked s) rn n
               , AstVarName (AstRanked s) rn n
               , [AstDynamicVarName]
               , AstDomains s )
{-# NOINLINE fun3DToAstR #-}
fun3DToAstR shn f od = unsafePerformIO $ fun3DToAstIOR shn f od

fun3DToAstIOS :: (AstShaped s rn shn -> AstShaped s rn shn
                  -> Domains (AstRanked s)
                  -> AstDomains s)
              -> DomainsOD
              -> IO ( AstVarName (AstShaped s) rn shn
                    , AstVarName (AstShaped s) rn shn
                    , [AstDynamicVarName]
                    , AstDomains s )
{-# INLINE fun3DToAstIOS #-}
fun3DToAstIOS f od = do
  nvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVarS nvarName) (AstVarS nvarName2) asts
  return (nvarName, nvarName2, V.toList vars, x)

fun3DToAstS :: (AstShaped s rn shn -> AstShaped s rn shn
                -> Domains (AstRanked s)
                -> AstDomains s)
            -> DomainsOD
            -> ( AstVarName (AstShaped s) rn shn
               , AstVarName (AstShaped s) rn shn
               , [AstDynamicVarName]
               , AstDomains s )
{-# NOINLINE fun3DToAstS #-}
fun3DToAstS f od = unsafePerformIO $ fun3DToAstIOS f od

fun4ToAstIOR :: ShapeInt n
             -> ShapeInt m
             -> (AstRanked s rn n -> AstRanked s rm m
                 -> AstRanked s rn n -> AstRanked s rm m
                 -> AstRanked s rn n)
             -> IO ( AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rm m
                   , AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rm m
                   , AstRanked s rn n )
{-# INLINE fun4ToAstIOR #-}
fun4ToAstIOR shn shm f = do
  nvarName <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  mvarName2 <- unsafeGetFreshAstVarName
  let !x = f (AstVar shn nvarName) (AstVar shm mvarName)
             (AstVar shn nvarName2) (AstVar shm mvarName2)
  return (nvarName, mvarName, nvarName2, mvarName2, x)

fun4ToAstR :: ShapeInt n
           -> ShapeInt m
           -> (AstRanked s rn n -> AstRanked s rm m
               -> AstRanked s rn n -> AstRanked s rm m
               -> AstRanked s rn n)
           -> ( AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rm m
              , AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rm m
              , AstRanked s rn n )
{-# NOINLINE fun4ToAstR #-}
fun4ToAstR shn shm f = unsafePerformIO $ fun4ToAstIOR shn shm f

fun4ToAstIOS :: (AstShaped s rn shn -> AstShaped s rm shm
                 -> AstShaped s rn shn -> AstShaped s rm shm
                 -> AstShaped s rn shn)
             -> IO ( AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rm shm
                   , AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rm shm
                   , AstShaped s rn shn )
{-# INLINE fun4ToAstIOS #-}
fun4ToAstIOS f = do
  nvarName <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  mvarName2 <- unsafeGetFreshAstVarName
  let !x = f (AstVarS nvarName) (AstVarS mvarName)
             (AstVarS nvarName2) (AstVarS mvarName2)
  return (nvarName, mvarName, nvarName2, mvarName2, x)

fun4ToAstS :: (AstShaped s rn shn -> AstShaped s rm shm
               -> AstShaped s rn shn -> AstShaped s rm shm
               -> AstShaped s rn shn)
           -> ( AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rm shm
              , AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rm shm
              , AstShaped s rn shn )
{-# NOINLINE fun4ToAstS #-}
fun4ToAstS f = unsafePerformIO $ fun4ToAstIOS f

fun4DToAstIOR :: ShapeInt n
              -> (AstRanked s rn n -> Domains (AstRanked s)
                  -> AstRanked s rn n -> Domains (AstRanked s)
                  -> AstRanked s rn n)
              -> DomainsOD
              -> IO ( AstVarName (AstRanked s) rn n
                    , [AstDynamicVarName]
                    , AstVarName (AstRanked s) rn n
                    , [AstDynamicVarName]
                    , AstRanked s rn n )
{-# INLINE fun4DToAstIOR #-}
fun4DToAstIOR shn f od = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars2, !asts2) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVar shn nvarName) asts
             (AstVar shn nvarName2) asts2
  return (nvarName, V.toList vars, nvarName2, V.toList vars2, x)

fun4DToAstR :: ShapeInt n
            -> (AstRanked s rn n -> Domains (AstRanked s)
                -> AstRanked s rn n -> Domains (AstRanked s)
                -> AstRanked s rn n)
            -> DomainsOD
            -> ( AstVarName (AstRanked s) rn n
               , [AstDynamicVarName]
               , AstVarName (AstRanked s) rn n
               , [AstDynamicVarName]
               , AstRanked s rn n )
{-# NOINLINE fun4DToAstR #-}
fun4DToAstR shn f od = unsafePerformIO $ fun4DToAstIOR shn f od

fun4DToAstIOS :: (AstShaped s rn shn -> Domains (AstRanked s)
                  -> AstShaped s rn shn -> Domains (AstRanked s)
                  -> AstShaped s rn shn)
              -> DomainsOD
              -> IO ( AstVarName (AstShaped s) rn shn
                    , [AstDynamicVarName]
                    , AstVarName (AstShaped s) rn shn
                    , [AstDynamicVarName]
                    , AstShaped s rn shn )
{-# INLINE fun4DToAstIOS #-}
fun4DToAstIOS f od = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars2, !asts2) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVarS nvarName) asts
             (AstVarS nvarName2) asts2
  return (nvarName, V.toList vars, nvarName2, V.toList vars2, x)

fun4DToAstS :: (AstShaped s rn shn -> Domains (AstRanked s)
                -> AstShaped s rn shn -> Domains (AstRanked s)
                -> AstShaped s rn shn)
            -> DomainsOD
            -> ( AstVarName (AstShaped s) rn shn
               , [AstDynamicVarName]
               , AstVarName (AstShaped s) rn shn
               , [AstDynamicVarName]
               , AstShaped s rn shn )
{-# NOINLINE fun4DToAstS #-}
fun4DToAstS f od = unsafePerformIO $ fun4DToAstIOS f od

funToAstDomainsIO
  :: (Domains (AstRanked s) -> AstRanked s r n)
  -> DomainsOD
  -> IO ([AstDynamicVarName], AstRanked s r n)
{-# INLINE funToAstDomainsIO #-}
funToAstDomainsIO g parameters0 = do
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar parameters0
  let !x = g asts
  return (V.toList vars, x)

dynamicToVar :: DynamicTensor (Flip OR.Array)
             -> IO (AstDynamicVarName, DynamicTensor (AstRanked s))
dynamicToVar (DynamicRanked @r2 @n2 e) = do
  let sh3 = OR.shapeL $ runFlip e
  freshId <- unsafeGetFreshAstVarId
  return $! Sh.withShapeP sh3 $ \(Proxy :: Proxy sh2) ->
    let !varE = AstDynamicVarName @Nat @r2 @sh2 freshId
        dynE :: AstDynamic s
        !dynE = DynamicRanked @r2 @n2
                              (AstVar (listShapeToShape sh3)
                                      (AstVarName freshId))
    in (varE, dynE)
dynamicToVar (DynamicShaped @r2 @sh2 _) = do
  freshId <- unsafeGetFreshAstVarId
  return $!
    let !varE = AstDynamicVarName @[Nat] @r2 @sh2 freshId
        dynE :: AstDynamic s
        !dynE = DynamicShaped @r2 @sh2
                              (AstVarS (AstVarName freshId))
    in (varE, dynE)
dynamicToVar (DynamicRankedDummy @r2 @sh2 _ _) = do
  let sh3 = Sh.shapeT @sh2
  freshId <- unsafeGetFreshAstVarId
  return $! withListShape sh3 $ \ (sh4 :: ShapeInt n2) ->
    let !varE = AstDynamicVarName @Nat @r2 @sh2 freshId
        dynE :: AstDynamic s
        !dynE = DynamicRanked @r2 @n2 (AstVar sh4 (AstVarName freshId))
    in (varE, dynE)
dynamicToVar (DynamicShapedDummy @r2 @sh2 _ _) = do
  freshId <- unsafeGetFreshAstVarId
  return $!
    let !varE = AstDynamicVarName @[Nat] @r2 @sh2 freshId
        dynE :: AstDynamic s
        !dynE = DynamicShaped @r2 @sh2
                              (AstVarS (AstVarName freshId))
    in (varE, dynE)

funToAstDomains
  :: (Domains (AstRanked s) -> AstRanked s r n)
  -> DomainsOD
  -> ([AstDynamicVarName], AstRanked s r n)
{-# NOINLINE funToAstDomains #-}
funToAstDomains g parameters0 =
  unsafePerformIO $ funToAstDomainsIO g parameters0

funToAstRevIO :: DomainsOD
              -> IO ( [AstDynamicVarName]
                    , Domains (AstRanked PrimalSpan)
                    , [AstDynamicVarName]
                    , Domains (AstRanked FullSpan) )
{-# INLINE funToAstRevIO #-}
funToAstRevIO parameters0 = do
  let f (DynamicRanked @r @n e) = do
        let sh2 = OR.shapeL $ runFlip e
        freshId <- unsafeGetFreshAstVarId
        return $! Sh.withShapeP sh2 $ \(Proxy :: Proxy sh) ->
          let !varE = AstDynamicVarName @Nat @r @sh freshId
              dynE :: AstDynamic s
              !dynE = DynamicRanked @r @n
                                    (AstVar (listShapeToShape sh2)
                                            (AstVarName freshId))
          in (varE, dynE, varE, dynE)
      f (DynamicShaped @r @sh _) = do
        freshId <- unsafeGetFreshAstVarId
        return $!
          let !varE = AstDynamicVarName @[Nat] @r @sh freshId
              dynE :: AstDynamic s
              !dynE = DynamicShaped @r @sh (AstVarS (AstVarName freshId))
          in (varE, dynE, varE, dynE)
      f (DynamicRankedDummy @r @sh _ _) = do
        let sh2 = Sh.shapeT @sh
        freshId <- unsafeGetFreshAstVarId
        return $! withListShape sh2 $ \ (sh :: ShapeInt n) ->
          let !varE = AstDynamicVarName @Nat @r @sh freshId
              dynE :: AstDynamic s
              !dynE = DynamicRanked @r @n (AstVar sh (AstVarName freshId))
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
  return (varsPrimal, vp, vars, va)

-- The AstVarName type with its parameter somehow prevents cse and crashes
-- compared with a bare AstVarId, so let's keep it.
funToAstRev :: DomainsOD
            -> ( AstVarId
               , [AstDynamicVarName]
               , Domains (AstRanked PrimalSpan)
               , [AstDynamicVarName]
               , Domains (AstRanked FullSpan) )
{-# NOINLINE funToAstRev #-}
funToAstRev parameters0 = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  (!varsPrimal, !astsPrimal, !vars, !asts) <- funToAstRevIO parameters0
  return (freshId, varsPrimal, astsPrimal, vars, asts)

funToAstFwdIO :: DomainsOD
              -> IO ( [AstDynamicVarName]
                    , Domains (AstRanked PrimalSpan)
                    , [AstDynamicVarName]
                    , Domains (AstRanked PrimalSpan)
                    , [AstDynamicVarName]
                    , Domains (AstRanked FullSpan) )
{-# INLINE funToAstFwdIO #-}
funToAstFwdIO parameters0 = do
  let f :: DynamicTensor (Flip OR.Array)
        -> IO ( AstDynamicVarName, AstDynamic PrimalSpan
              , AstDynamicVarName, AstDynamic PrimalSpan
              , AstDynamicVarName, AstDynamic FullSpan )
      f (DynamicRanked @r @n e) = do
        let sh2 = OR.shapeL $ runFlip e
        freshIdDs <- unsafeGetFreshAstVarId
        freshId <- unsafeGetFreshAstVarId
        return $! Sh.withShapeP sh2 $ \(Proxy :: Proxy sh) ->
          let varE :: AstVarId -> AstDynamicVarName
              varE varId = AstDynamicVarName @Nat @r @sh varId
              dynE :: AstVarId -> AstDynamic s
              dynE varId = DynamicRanked @r @n
                                     (AstVar (listShapeToShape sh2)
                                             (AstVarName varId))
              !vd = varE freshIdDs
              !dd = dynE freshIdDs
              !vi = varE freshId
              di :: AstDynamic s
              !di = dynE freshId
          in (vd, dd, vi, di, vi, di)
      f (DynamicShaped @r @sh _) = do
        freshIdDs <- unsafeGetFreshAstVarId
        freshId <- unsafeGetFreshAstVarId
        return $!
          let varE :: AstVarId -> AstDynamicVarName
              varE varId = AstDynamicVarName @[Nat] @r @sh varId
              dynE :: AstVarId -> AstDynamic s
              dynE varId = DynamicShaped @r @sh (AstVarS (AstVarName varId))
              !vd = varE freshIdDs
              !dd = dynE freshIdDs
              !vi = varE freshId
              di :: AstDynamic s
              !di = dynE freshId
          in (vd, dd, vi, di, vi, di)
      f (DynamicRankedDummy @r @sh _ _) = do
        let sh2 = Sh.shapeT @sh
        freshIdDs <- unsafeGetFreshAstVarId
        freshId <- unsafeGetFreshAstVarId
        return $! withListShape sh2 $ \ (sh :: ShapeInt n) ->
          let varE :: AstVarId -> AstDynamicVarName
              varE varId = AstDynamicVarName @Nat @r @sh varId
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
              varE varId = AstDynamicVarName @[Nat] @r @sh varId
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
  return (varsPrimalDs, vd, varsPrimal, vp, vars, va)

-- The AstVarName type with its parameter somehow prevents cse and crashes
-- compared with a bare AstVarId, so let's keep it.
funToAstFwd :: DomainsOD
            -> ( [AstDynamicVarName]
               , Domains (AstRanked PrimalSpan)
               , [AstDynamicVarName]
               , Domains (AstRanked PrimalSpan)
               , [AstDynamicVarName]
               , Domains (AstRanked FullSpan) )
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

funToAstIndexIO
  :: forall m p. KnownNat m
  => Int -> (AstIndex m -> AstIndex p) -> IO (AstVarList m, AstIndex p)
{-# INLINE funToAstIndexIO #-}
funToAstIndexIO m f = do
  varList <- replicateM m unsafeGetFreshAstVarName
  let !sz = listToSized varList
      !x = f (listToIndex $ map AstIntVar varList)
  return (sz, x)

funToAstIndex
  :: forall m p. KnownNat m
  => (AstIndex m -> AstIndex p) -> (AstVarList m, AstIndex p)
{-# NOINLINE funToAstIndex #-}
funToAstIndex = unsafePerformIO . funToAstIndexIO (valueOf @m)

funToAstIndexIOS
  :: forall sh1 sh2. Sh.Shape sh1
  => (AstIndexS sh1 -> AstIndexS sh2) -> IO (AstVarListS sh1, AstIndexS sh2)
{-# INLINE funToAstIndexIOS #-}
funToAstIndexIOS f = do
  let p = length $ Sh.shapeT @sh1
  varList <- replicateM p unsafeGetFreshAstVarName
  let !sz = ShapedList.listToSized varList
      !x = f (ShapedList.listToSized $ map AstIntVar varList)
  return (sz, x)

funToAstIndexS
  :: forall sh1 sh2. Sh.Shape sh1
  => (AstIndexS sh1 -> AstIndexS sh2) -> (AstVarListS sh1, AstIndexS sh2)
{-# NOINLINE funToAstIndexS #-}
funToAstIndexS = unsafePerformIO . funToAstIndexIOS
