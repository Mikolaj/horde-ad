-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of it escapes.
module HordeAd.Core.AstFreshId
  ( astRegisterFun, astRegisterADShare, astRegisterADShareS
  , funToAstIOR, funToAstR, fun2ToAstR, fun2ToAstS, fun3ToAstR, fun3ToAstS
  , fun4ToAstR, fun4ToAstS, funToAstDomains, funToAstDomainsS
  , funToAstRevIO, funToAstRev, funToAstRevIOS, funToAstRevS
  , funToAstFwdIO, funToAstFwd, funToAstFwdIOS, funToAstFwdS
  , funToAstIOI, funToAstI, funToAstIndexIO, funToAstIndex
  , funToAstIOS, funToAstS, astRegisterFunS, funToAstIndexIOS, funToAstIndexS
  , resetVarCounter
  ) where

import Prelude

import           Control.Monad (replicateM)
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as Sh
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.List (unzip4, unzip6)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat)
import           System.IO.Unsafe (unsafePerformIO)

import           HordeAd.Core.Ast
import           HordeAd.Core.AstTools
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
  => AstRanked s r n -> AstBindingsD (AstDynamic s)
  -> (AstBindingsD (AstDynamic s), AstRanked s r n)
{-# NOINLINE astRegisterFun #-}
astRegisterFun !r !l | astIsSmall True r = (l, r)
astRegisterFun r l = unsafePerformIO $ do
  !freshId <- unsafeGetFreshAstVarId
  let !r2 = AstVar (shapeAst r) $ AstVarName freshId
      !d = DynamicExists $ AstRToD r
  return ((freshId, d) : l, r2)

astRegisterFunS
  :: (Sh.Shape sh, GoodScalar r)
  => AstShaped s r sh -> AstBindingsD (AstDynamic s)
  -> (AstBindingsD (AstDynamic s), AstShaped s r sh)
{-# NOINLINE astRegisterFunS #-}
astRegisterFunS !r !l | astIsSmallS True r = (l, r)
astRegisterFunS r l = unsafePerformIO $ do
  !freshId <- unsafeGetFreshAstVarId
  let !r2 = AstVarS $ AstVarName freshId
      !d = DynamicExists $ AstSToD r
  return ((freshId, d) : l, r2)

astRegisterADShare :: (GoodScalar r, KnownNat n)
                   => AstRanked PrimalSpan r n -> ADShare
                   -> (ADShare, AstRanked PrimalSpan r n)
{-# NOINLINE astRegisterADShare #-}
astRegisterADShare !r !l | astIsSmall True r = (l, r)
astRegisterADShare r l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !l2 = insertADShare freshId (AstRToD r) l
      !r2 = AstVar (shapeAst r) $ AstVarName freshId
  return (l2, r2)

astRegisterADShareS :: (GoodScalar r, Sh.Shape sh)
                    => AstShaped PrimalSpan r sh -> ADShare
                    -> (ADShare, AstShaped PrimalSpan r sh)
{-# NOINLINE astRegisterADShareS #-}
astRegisterADShareS !r !l | astIsSmallS True r = (l, r)
astRegisterADShareS r l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !l2 = insertADShare freshId (AstSToD r) l
      !r2 = AstVarS $ AstVarName freshId
  return (l2, r2)

funToAstIOR :: forall n m s r r2. GoodScalar r
            => ShapeInt n -> (AstRanked s r n -> AstRanked s r2 m)
            -> IO ( AstVarName (AstRanked s) r n
                  , AstDynamicVarName (AstRanked s)
                  , AstRanked s r2 m )
{-# INLINE funToAstIOR #-}
funToAstIOR sh f = do
  varName <- unsafeGetFreshAstVarName
  return $! Sh.withShapeP (shapeToList sh) $ \(Proxy :: Proxy p_sh) ->
    let !x = f (AstVar sh varName)
    in (varName, AstDynamicVarName @Nat @p_sh varName, x)

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
                  , AstDynamicVarName (AstShaped s)
                  , AstShaped s r2 sh2 )
{-# INLINE funToAstIOS #-}
funToAstIOS f = do
  varName <- unsafeGetFreshAstVarName
  let !x = f (AstVarS varName)
  return (varName, AstDynamicVarName @[Nat] @sh varName, x)

funToAstS :: forall sh sh2 s r r2. (Sh.Shape sh, GoodScalar r)
          => (AstShaped s r sh -> AstShaped s r2 sh2)
          -> (AstVarName (AstShaped s) r sh, AstShaped s r2 sh2)
{-# NOINLINE funToAstS #-}
funToAstS f = unsafePerformIO $ do
  (!var, _, !ast) <- funToAstIOS f
  return (var, ast)

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

funToAstDomainsIO
  :: (Domains (AstDynamic s) -> AstRanked s r n)
  -> DomainsOD
  -> IO ( [AstDynamicVarName (AstRanked s)]
        , AstRanked s r n )
{-# INLINE funToAstDomainsIO #-}
funToAstDomainsIO g parameters0 = do
  let f (DynamicExists @r2 e) = do
        let sh = OD.shapeL e
        freshId <- unsafeGetFreshAstVarId
        return $! Sh.withShapeP sh $ \(Proxy :: Proxy p_sh) ->
          withListShape sh $ \ (_ :: Shape n Int) ->
            let varE :: AstDynamicVarName (AstRanked s)
                !varE = AstDynamicVarName @Nat @p_sh @r2 (AstVarName freshId)
                dynE :: DynamicExists (AstDynamic s)
                !dynE = DynamicExists @r2
                        $ AstRToD @n (AstVar (listShapeToShape sh)
                                             (AstVarName freshId))
            in (varE, dynE)
  (!vars, !asts) <- V.unzip <$> V.mapM f parameters0
  let !x = g asts
  return (V.toList vars, x)

funToAstDomains
  :: (Domains (AstDynamic s) -> AstRanked s r n)
  -> DomainsOD
  -> ( [AstDynamicVarName (AstRanked s)]
     , AstRanked s r n )
{-# NOINLINE funToAstDomains #-}
funToAstDomains g parameters0 =
  unsafePerformIO $ funToAstDomainsIO g parameters0

funToAstDomainsIOS
  :: (Domains (AstDynamic s) -> AstShaped s r sh)
  -> DomainsOD
  -> IO ( [AstDynamicVarName (AstShaped s)]
        , AstShaped s r sh )
{-# INLINE funToAstDomainsIOS #-}
funToAstDomainsIOS g parameters0 = do
  let f (DynamicExists @r2 e) = do
        let sh = OD.shapeL e
        freshId <- unsafeGetFreshAstVarId
        return $! Sh.withShapeP sh $ \(Proxy :: Proxy p_sh) ->
          let varE :: AstDynamicVarName (AstShaped s)
              !varE = AstDynamicVarName @[Nat] @p_sh @r2
                                        (AstVarName freshId)
              dynE :: DynamicExists (AstDynamic s)
              !dynE = DynamicExists @r2
                      $ AstSToD (AstVarS @p_sh (AstVarName freshId))
          in (varE, dynE)
  (!vars, !asts) <- V.unzip <$> V.mapM f parameters0
  let !x = g asts
  return (V.toList vars, x)

funToAstDomainsS
  :: (Domains (AstDynamic s) -> AstShaped s r sh)
  -> DomainsOD
  -> ( [AstDynamicVarName (AstShaped s)]
     , AstShaped s r sh )
{-# NOINLINE funToAstDomainsS #-}
funToAstDomainsS g parameters0 =
  unsafePerformIO $ funToAstDomainsIOS g parameters0

funToAstRevIO :: DomainsOD
              -> IO ( [AstDynamicVarName (AstRanked PrimalSpan)]
                    , Domains (AstDynamic PrimalSpan)
                    , [AstDynamicVarName (AstRanked FullSpan)]
                    , Domains (AstDynamic FullSpan) )
{-# INLINE funToAstRevIO #-}
funToAstRevIO parameters0 = do
  let f (DynamicExists @r2 e) = do
        let sh = OD.shapeL e
        freshId <- unsafeGetFreshAstVarId
        return $! Sh.withShapeP sh $ \(Proxy :: Proxy p_sh) ->
          withListShape sh $ \ (_ :: Shape n Int) ->
            let varE :: AstDynamicVarName (AstRanked s)
                !varE = AstDynamicVarName @Nat @p_sh @r2 (AstVarName freshId)
                dynE :: DynamicExists (AstDynamic s)
                !dynE = DynamicExists @r2
                        $ AstRToD @n (AstVar (listShapeToShape sh)
                                             (AstVarName freshId))
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
               , [AstDynamicVarName (AstRanked PrimalSpan)]
               , Domains (AstDynamic PrimalSpan)
               , [AstDynamicVarName (AstRanked FullSpan)]
               , Domains (AstDynamic FullSpan) )
{-# NOINLINE funToAstRev #-}
funToAstRev parameters0 = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  (!varsPrimal, !astsPrimal, !vars, !asts) <- funToAstRevIO parameters0
  return (freshId, varsPrimal, astsPrimal, vars, asts)

funToAstRevIOS :: DomainsOD
               -> IO ( [AstDynamicVarName (AstShaped PrimalSpan)]
                     , Domains (AstDynamic PrimalSpan)
                     , [AstDynamicVarName (AstShaped FullSpan)]
                     , Domains (AstDynamic FullSpan) )
{-# INLINE funToAstRevIOS #-}
funToAstRevIOS parameters0 = do
  let f (DynamicExists @r2 e) = do
        let sh = OD.shapeL e
        freshId <- unsafeGetFreshAstVarId
        return $! Sh.withShapeP sh $ \(Proxy :: Proxy p_sh) ->
          let varE :: AstDynamicVarName (AstShaped s)
              !varE = AstDynamicVarName @[Nat] @p_sh @r2 (AstVarName freshId)
              dynE :: DynamicExists (AstDynamic s)
              !dynE = DynamicExists @r2
                      $ AstSToD (AstVarS @p_sh (AstVarName freshId))
          in (varE, dynE, varE, dynE)
  (!varsPrimal, !astsPrimal, !vars, !asts)
    <- unzip4 <$> mapM f (V.toList parameters0)
  let !vp = V.fromList astsPrimal
      !ap = V.fromList asts
  return (varsPrimal, vp, vars, ap)

funToAstRevS :: DomainsOD
             -> ( AstVarId
                , [AstDynamicVarName (AstShaped PrimalSpan)]
                , Domains (AstDynamic PrimalSpan)
                , [AstDynamicVarName (AstShaped FullSpan)]
                , Domains (AstDynamic FullSpan) )
{-# NOINLINE funToAstRevS #-}
funToAstRevS parameters0 = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  (!varsPrimal, !astsPrimal, !vars, !asts) <- funToAstRevIOS parameters0
  return (freshId, varsPrimal, astsPrimal, vars, asts)

funToAstFwdIO :: DomainsOD
              -> IO ( [AstDynamicVarName (AstRanked PrimalSpan)]
                    , Domains (AstDynamic PrimalSpan)
                    , [AstDynamicVarName (AstRanked PrimalSpan)]
                    , Domains (AstDynamic PrimalSpan)
                    , [AstDynamicVarName (AstRanked FullSpan)]
                    , Domains (AstDynamic FullSpan) )
{-# INLINE funToAstFwdIO #-}
funToAstFwdIO parameters0 = do
  let f (DynamicExists @r2 e) = do
        let sh = OD.shapeL e
        freshIdDs <- unsafeGetFreshAstVarId
        freshId <- unsafeGetFreshAstVarId
        return $! Sh.withShapeP sh $ \(Proxy :: Proxy p_sh) ->
          withListShape sh $ \ (_ :: Shape n Int) ->
            let varE :: AstVarId -> AstDynamicVarName (AstRanked s)
                varE v = AstDynamicVarName @Nat @p_sh @r2 (AstVarName v)
                dynE :: AstVarId -> DynamicExists (AstDynamic s)
                dynE v = DynamicExists @r2
                         $ AstRToD @n (AstVar (listShapeToShape sh)
                                              (AstVarName v))
                !vd = varE freshIdDs
                !dd = dynE freshIdDs
                vi :: AstDynamicVarName (AstRanked s)
                !vi = varE freshId
                di :: DynamicExists (AstDynamic s)
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
            -> ( [AstDynamicVarName (AstRanked PrimalSpan)]
               , Domains (AstDynamic PrimalSpan)
               , [AstDynamicVarName (AstRanked PrimalSpan)]
               , Domains (AstDynamic PrimalSpan)
               , [AstDynamicVarName (AstRanked FullSpan)]
               , Domains (AstDynamic FullSpan) )
{-# NOINLINE funToAstFwd #-}
funToAstFwd parameters0 = unsafePerformIO $ funToAstFwdIO parameters0

funToAstFwdIOS :: DomainsOD
               -> IO ( [AstDynamicVarName (AstShaped PrimalSpan)]
                     , Domains (AstDynamic PrimalSpan)
                     , [AstDynamicVarName (AstShaped PrimalSpan)]
                     , Domains (AstDynamic PrimalSpan)
                     , [AstDynamicVarName (AstShaped FullSpan)]
                     , Domains (AstDynamic FullSpan) )
{-# INLINE funToAstFwdIOS #-}
funToAstFwdIOS parameters0 = do
  let f (DynamicExists @r2 e) = do
        let sh = OD.shapeL e
        freshIdDs <- unsafeGetFreshAstVarId
        freshId <- unsafeGetFreshAstVarId
        return $! Sh.withShapeP sh $ \(Proxy :: Proxy p_sh) ->
          let varE :: AstVarId -> AstDynamicVarName (AstShaped s)
              varE v = AstDynamicVarName @[Nat] @p_sh @r2 (AstVarName v)
              dynE :: AstVarId -> DynamicExists (AstDynamic s)
              dynE v = DynamicExists @r2
                       $ AstSToD (AstVarS @p_sh (AstVarName v))
              !vd = varE freshIdDs
              !dd = dynE freshIdDs
              vi :: AstDynamicVarName (AstShaped s)
              !vi = varE freshId
              di :: DynamicExists (AstDynamic s)
              !di = dynE freshId
          in (vd, dd, vi, di, vi, di)
  (!varsPrimalDs, !astsPrimalDs, !varsPrimal, !astsPrimal, !vars, !asts)
    <- unzip6 <$> mapM f (V.toList parameters0)
  let !vd = V.fromList astsPrimalDs
      !vp = V.fromList astsPrimal
      !va = V.fromList asts
  return (varsPrimalDs, vd, varsPrimal, vp, vars, va)

funToAstFwdS :: DomainsOD
             -> ( [AstDynamicVarName (AstShaped PrimalSpan)]
                , Domains (AstDynamic PrimalSpan)
                , [AstDynamicVarName (AstShaped PrimalSpan)]
                , Domains (AstDynamic PrimalSpan)
                , [AstDynamicVarName (AstShaped FullSpan)]
                , Domains (AstDynamic FullSpan) )
{-# NOINLINE funToAstFwdS #-}
funToAstFwdS parameters0 = unsafePerformIO $ funToAstFwdIOS parameters0

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
