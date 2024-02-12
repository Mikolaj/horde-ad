-- | Operations that (impurely, via a strictly increasing thread-safe counter)
-- generate fresh variables and sometimes also produce AST terms
-- by applying functions to such variables. This modules encapsulates
-- the impurity, though some functions are in IO and they are used
-- with @unsafePerformIO@ outside, so some of it escapes.
module HordeAd.Core.AstFreshId
  ( astRegisterFun, astRegisterFunS, astRegisterADShare, astRegisterADShareS
  , funToAstIOR, funToAstR, fun1DToAst
  , funToAst2R, funToAst2S, funToAstRH, funToAstSH, funToAstHH
  , funToAst3R, funToAst3S, funToAstRRH, funToAstSSH
  , funToAst4R, funToAst4S
  , funToAstRHRH, funToAstRHRG, funToAstSHSH, funToAstSHSG
  , funToAstHHHH, funToAstHHHG
  , funToAstHVector
  , funToAstRevIO, funToAstRev, funToAstFwdIO, funToAstFwd
  , funToAstIOI, funToAstI, funToAstIndexIO, funToAstIndex
  , funToAstIOS, funToAstS, funToAstIndexIOS, funToAstIndexS
  , resetVarCounter
  ) where

import Prelude

import           Control.Monad (replicateM)
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
import           HordeAd.Core.HVector
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
  return ((freshId, AstBindingsSimple d) : l, r2)

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
  return ((freshId, AstBindingsSimple d) : l, r2)

astRegisterADShare :: (GoodScalar r, KnownNat n)
                   => AstRanked PrimalSpan r n -> ADShare
                   -> (ADShare, AstRanked PrimalSpan r n)
{-# NOINLINE astRegisterADShare #-}
astRegisterADShare !r !l | astIsSmall True r = (l, r)
astRegisterADShare r l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !l2 = insertADShare freshId (AstBindingsSimple $ DynamicRanked r) l
      !r2 = AstVar (shapeAst r) $ AstVarName freshId
  return (l2, r2)

astRegisterADShareS :: (GoodScalar r, Sh.Shape sh)
                    => AstShaped PrimalSpan r sh -> ADShare
                    -> (ADShare, AstShaped PrimalSpan r sh)
{-# NOINLINE astRegisterADShareS #-}
astRegisterADShareS !r !l | astIsSmallS True r = (l, r)
astRegisterADShareS r l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !l2 = insertADShare freshId (AstBindingsSimple $ DynamicShaped r) l
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

funToAst2RIO :: ShapeInt n
             -> ShapeInt m
             -> (AstRanked s rn n -> AstRanked s rm m -> a)
             -> IO ( AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rm m
                   , a )
{-# INLINE funToAst2RIO #-}
funToAst2RIO shn shm f = do
  nvarName <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  let !x = f (AstVar shn nvarName) (AstVar shm mvarName)
  return (nvarName, mvarName, x)

funToAst2R :: ShapeInt n
           -> ShapeInt m
           -> (AstRanked s rn n -> AstRanked s rm m -> a)
           -> ( AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rm m
              , a )
{-# NOINLINE funToAst2R #-}
funToAst2R shn shm f = unsafePerformIO $ funToAst2RIO shn shm f

funToAst2SIO :: (AstShaped s rn shn -> AstShaped s rm shm -> a)
             -> IO ( AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rm shm
                   , a )
{-# INLINE funToAst2SIO #-}
funToAst2SIO f = do
  nvarName <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  let !x = f (AstVarS nvarName) (AstVarS mvarName)
  return (nvarName, mvarName, x)

funToAst2S :: (AstShaped s rn shn -> AstShaped s rm shm -> a)
           -> ( AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rm shm
              , a )
{-# NOINLINE funToAst2S #-}
funToAst2S f = unsafePerformIO $ funToAst2SIO f

funToAstRHIO :: ShapeInt n
             -> (AstRanked s rn n -> HVector (AstRanked s) -> a)
             -> VoidHVector
             -> IO ( AstVarName (AstRanked s) rn n
                   , [AstDynamicVarName]
                   , a )
{-# INLINE funToAstRHIO #-}
funToAstRHIO shn f od = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVar shn nvarName) asts
  return (nvarName, V.toList vars, x)

funToAstRH :: ShapeInt n
           -> (AstRanked s rn n -> HVector (AstRanked s) -> a)
           -> VoidHVector
           -> ( AstVarName (AstRanked s) rn n
              , [AstDynamicVarName]
              , a )
{-# NOINLINE funToAstRH #-}
funToAstRH shn f od = unsafePerformIO $ funToAstRHIO shn f od

funToAstSHIO :: (AstShaped s rn shn -> HVector (AstRanked s) -> a)
             -> VoidHVector
             -> IO ( AstVarName (AstShaped s) rn shn
                   , [AstDynamicVarName]
                   , a )
{-# INLINE funToAstSHIO #-}
funToAstSHIO f od = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVarS nvarName) asts
  return (nvarName, V.toList vars, x)

funToAstSH :: (AstShaped s rn shn -> HVector (AstRanked s) -> a)
           -> VoidHVector
           -> ( AstVarName (AstShaped s) rn shn
              , [AstDynamicVarName]
              , a )
{-# NOINLINE funToAstSH #-}
funToAstSH f od = unsafePerformIO $ funToAstSHIO f od

funToAstHHIO :: (HVector (AstRanked s) -> HVector (AstRanked s) -> a)
             -> VoidHVector
             -> VoidHVector
             -> IO ( [AstDynamicVarName]
                   , [AstDynamicVarName]
                   , a )
{-# INLINE funToAstHHIO #-}
funToAstHHIO f accShs eShs = do
  (!accvars, !acc) <- V.unzip <$> V.mapM dynamicToVar accShs
  (!evars, !e) <- V.unzip <$> V.mapM dynamicToVar eShs
  let !x = f acc e
  return (V.toList accvars, V.toList evars, x)

funToAstHH :: (HVector (AstRanked s) -> HVector (AstRanked s) -> a)
           -> VoidHVector
           -> VoidHVector
           -> ( [AstDynamicVarName]
              , [AstDynamicVarName]
              , a )
{-# NOINLINE funToAstHH #-}
funToAstHH f accShs eShs = unsafePerformIO $ funToAstHHIO f accShs eShs

funToAst3RIO :: ShapeInt n
             -> ShapeInt m
             -> (AstRanked s rn n -> AstRanked s rn n -> AstRanked s rm m -> a)
             -> IO ( AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rm m
                   , a )
{-# INLINE funToAst3RIO #-}
funToAst3RIO shn shm f = do
  nvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  let !x = f (AstVar shn nvarName) (AstVar shn nvarName2) (AstVar shm mvarName)
  return (nvarName, nvarName2, mvarName, x)

funToAst3R :: ShapeInt n
           -> ShapeInt m
           -> (AstRanked s rn n -> AstRanked s rn n -> AstRanked s rm m -> a)
           -> ( AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rm m
              , a )
{-# NOINLINE funToAst3R #-}
funToAst3R shn shm f = unsafePerformIO $ funToAst3RIO shn shm f

funToAst3SIO :: (AstShaped s rn shn -> AstShaped s rn shn -> AstShaped s rm shm
                 -> a)
             -> IO ( AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rm shm
                   , a )
{-# INLINE funToAst3SIO #-}
funToAst3SIO f = do
  nvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  let !x = f (AstVarS nvarName) (AstVarS nvarName2) (AstVarS mvarName)
  return (nvarName, nvarName2, mvarName, x)

funToAst3S :: (AstShaped s rn shn -> AstShaped s rn shn -> AstShaped s rm shm
               -> a)
           -> ( AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rm shm
              , a )
{-# NOINLINE funToAst3S #-}
funToAst3S f = unsafePerformIO $ funToAst3SIO f

funToAstRRHIO :: ShapeInt n
              -> (AstRanked s rn n -> AstRanked s rn n -> HVector (AstRanked s)
                  -> a)
              -> VoidHVector
              -> IO ( AstVarName (AstRanked s) rn n
                    , AstVarName (AstRanked s) rn n
                    , [AstDynamicVarName]
                    , a )
{-# INLINE funToAstRRHIO #-}
funToAstRRHIO shn f od = do
  nvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVar shn nvarName) (AstVar shn nvarName2) asts
  return (nvarName, nvarName2, V.toList vars, x)

funToAstRRH :: ShapeInt n
            -> (AstRanked s rn n -> AstRanked s rn n -> HVector (AstRanked s)
                -> a)
            -> VoidHVector
            -> ( AstVarName (AstRanked s) rn n
               , AstVarName (AstRanked s) rn n
               , [AstDynamicVarName]
               , a )
{-# NOINLINE funToAstRRH #-}
funToAstRRH shn f od = unsafePerformIO $ funToAstRRHIO shn f od

funToAstSSHIO :: (AstShaped s rn shn -> AstShaped s rn shn
                  -> HVector (AstRanked s)
                  -> a)
              -> VoidHVector
              -> IO ( AstVarName (AstShaped s) rn shn
                    , AstVarName (AstShaped s) rn shn
                    , [AstDynamicVarName]
                    , a )
{-# INLINE funToAstSSHIO #-}
funToAstSSHIO f od = do
  nvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVarS nvarName) (AstVarS nvarName2) asts
  return (nvarName, nvarName2, V.toList vars, x)

funToAstSSH :: (AstShaped s rn shn -> AstShaped s rn shn
                -> HVector (AstRanked s)
                -> a)
            -> VoidHVector
            -> ( AstVarName (AstShaped s) rn shn
               , AstVarName (AstShaped s) rn shn
               , [AstDynamicVarName]
               , a )
{-# NOINLINE funToAstSSH #-}
funToAstSSH f od = unsafePerformIO $ funToAstSSHIO f od

funToAst4RIO :: ShapeInt n
             -> ShapeInt m
             -> (AstRanked s rn n -> AstRanked s rm m
                 -> AstRanked s rn n -> AstRanked s rm m
                 -> a)
             -> IO ( AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rm m
                   , AstVarName (AstRanked s) rn n
                   , AstVarName (AstRanked s) rm m
                   , a )
{-# INLINE funToAst4RIO #-}
funToAst4RIO shn shm f = do
  nvarName <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  mvarName2 <- unsafeGetFreshAstVarName
  let !x = f (AstVar shn nvarName) (AstVar shm mvarName)
             (AstVar shn nvarName2) (AstVar shm mvarName2)
  return (nvarName, mvarName, nvarName2, mvarName2, x)

funToAst4R :: ShapeInt n
           -> ShapeInt m
           -> (AstRanked s rn n -> AstRanked s rm m
               -> AstRanked s rn n -> AstRanked s rm m
               -> a)
           -> ( AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rm m
              , AstVarName (AstRanked s) rn n
              , AstVarName (AstRanked s) rm m
              , a )
{-# NOINLINE funToAst4R #-}
funToAst4R shn shm f = unsafePerformIO $ funToAst4RIO shn shm f

funToAst4SIO :: (AstShaped s rn shn -> AstShaped s rm shm
                 -> AstShaped s rn shn -> AstShaped s rm shm
                 -> a)
             -> IO ( AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rm shm
                   , AstVarName (AstShaped s) rn shn
                   , AstVarName (AstShaped s) rm shm
                   , a )
{-# INLINE funToAst4SIO #-}
funToAst4SIO f = do
  nvarName <- unsafeGetFreshAstVarName
  mvarName <- unsafeGetFreshAstVarName
  nvarName2 <- unsafeGetFreshAstVarName
  mvarName2 <- unsafeGetFreshAstVarName
  let !x = f (AstVarS nvarName) (AstVarS mvarName)
             (AstVarS nvarName2) (AstVarS mvarName2)
  return (nvarName, mvarName, nvarName2, mvarName2, x)

funToAst4S :: (AstShaped s rn shn -> AstShaped s rm shm
               -> AstShaped s rn shn -> AstShaped s rm shm
               -> a)
           -> ( AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rm shm
              , AstVarName (AstShaped s) rn shn
              , AstVarName (AstShaped s) rm shm
              , a )
{-# NOINLINE funToAst4S #-}
funToAst4S f = unsafePerformIO $ funToAst4SIO f

funToAstRHRHIO :: ShapeInt n
               -> (AstRanked s rn n -> HVector (AstRanked s)
                   -> AstRanked s rn n -> HVector (AstRanked s)
                   -> a)
               -> VoidHVector
               -> IO ( AstVarName (AstRanked s) rn n
                     , [AstDynamicVarName]
                     , AstVarName (AstRanked s) rn n
                     , [AstDynamicVarName]
                     , a )
{-# INLINE funToAstRHRHIO #-}
funToAstRHRHIO shn f od = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars2, !asts2) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVar shn nvarName) asts
             (AstVar shn nvarName2) asts2
  return (nvarName, V.toList vars, nvarName2, V.toList vars2, x)

funToAstRHRH :: ShapeInt n
             -> (AstRanked s rn n -> HVector (AstRanked s)
                 -> AstRanked s rn n -> HVector (AstRanked s)
                 -> a)
             -> VoidHVector
             -> ( AstVarName (AstRanked s) rn n
                , [AstDynamicVarName]
                , AstVarName (AstRanked s) rn n
                , [AstDynamicVarName]
                , a )
{-# NOINLINE funToAstRHRH #-}
funToAstRHRH shn f od = unsafePerformIO $ funToAstRHRHIO shn f od

funToAstRHRGIO :: ShapeInt n
               -> (AstRanked s rn n -> HVector (AstRanked s)
                   -> AstRanked s rn n -> HVector (AstRanked s)
                   -> a)
               -> VoidHVector
               -> VoidHVector
               -> IO ( AstVarName (AstRanked s) rn n
                     , [AstDynamicVarName]
                     , AstVarName (AstRanked s) rn n
                     , [AstDynamicVarName]
                     , a )
{-# INLINE funToAstRHRGIO #-}
funToAstRHRGIO shn f domB domsOD = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar domB
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars2, !asts2) <- V.unzip <$> V.mapM dynamicToVar domsOD
  let !x = f (AstVar shn nvarName) asts
             (AstVar shn nvarName2) asts2
  return (nvarName, V.toList vars, nvarName2, V.toList vars2, x)

funToAstRHRG :: ShapeInt n
             -> (AstRanked s rn n -> HVector (AstRanked s)
                 -> AstRanked s rn n -> HVector (AstRanked s)
                 -> a)
             -> VoidHVector
             -> VoidHVector
             -> ( AstVarName (AstRanked s) rn n
                , [AstDynamicVarName]
                , AstVarName (AstRanked s) rn n
                , [AstDynamicVarName]
                , a )
{-# NOINLINE funToAstRHRG #-}
funToAstRHRG shn f domB domsOD =
  unsafePerformIO $ funToAstRHRGIO shn f domB domsOD

funToAstSHSHIO :: (AstShaped s rn shn -> HVector (AstRanked s)
                   -> AstShaped s rn shn -> HVector (AstRanked s)
                   -> a)
               -> VoidHVector
               -> IO ( AstVarName (AstShaped s) rn shn
                     , [AstDynamicVarName]
                     , AstVarName (AstShaped s) rn shn
                     , [AstDynamicVarName]
                     , a )
{-# INLINE funToAstSHSHIO #-}
funToAstSHSHIO f od = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar od
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars2, !asts2) <- V.unzip <$> V.mapM dynamicToVar od
  let !x = f (AstVarS nvarName) asts
             (AstVarS nvarName2) asts2
  return (nvarName, V.toList vars, nvarName2, V.toList vars2, x)

funToAstSHSH :: (AstShaped s rn shn -> HVector (AstRanked s)
                 -> AstShaped s rn shn -> HVector (AstRanked s)
                 -> a)
             -> VoidHVector
             -> ( AstVarName (AstShaped s) rn shn
                , [AstDynamicVarName]
                , AstVarName (AstShaped s) rn shn
                , [AstDynamicVarName]
                , a )
{-# NOINLINE funToAstSHSH #-}
funToAstSHSH f od = unsafePerformIO $ funToAstSHSHIO f od

funToAstSHSGIO :: (AstShaped s rn shn -> HVector (AstRanked s)
                   -> AstShaped s rn shn -> HVector (AstRanked s)
                   -> a)
               -> VoidHVector
               -> VoidHVector
               -> IO ( AstVarName (AstShaped s) rn shn
                     , [AstDynamicVarName]
                     , AstVarName (AstShaped s) rn shn
                     , [AstDynamicVarName]
                     , a )
{-# INLINE funToAstSHSGIO #-}
funToAstSHSGIO f domB domsOD = do
  nvarName <- unsafeGetFreshAstVarName
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar domB
  nvarName2 <- unsafeGetFreshAstVarName
  (!vars2, !asts2) <- V.unzip <$> V.mapM dynamicToVar domsOD
  let !x = f (AstVarS nvarName) asts
             (AstVarS nvarName2) asts2
  return (nvarName, V.toList vars, nvarName2, V.toList vars2, x)

funToAstSHSG :: (AstShaped s rn shn -> HVector (AstRanked s)
                 -> AstShaped s rn shn -> HVector (AstRanked s)
                 -> a)
             -> VoidHVector
             -> VoidHVector
             -> ( AstVarName (AstShaped s) rn shn
                , [AstDynamicVarName]
                , AstVarName (AstShaped s) rn shn
                , [AstDynamicVarName]
                , a )
{-# NOINLINE funToAstSHSG #-}
funToAstSHSG f domB domsOD = unsafePerformIO $ funToAstSHSGIO f domB domsOD

funToAstHHHHIO :: (HVector (AstRanked s) -> HVector (AstRanked s)
                   -> HVector (AstRanked s) -> HVector (AstRanked s)
                   -> a)
               -> VoidHVector
               -> VoidHVector
               -> IO ( [AstDynamicVarName]
                     , [AstDynamicVarName]
                     , [AstDynamicVarName]
                     , [AstDynamicVarName]
                     , a )
{-# INLINE funToAstHHHHIO #-}
funToAstHHHHIO f accShs eShs = do
  (!vs1, !asts1) <- V.unzip <$> V.mapM dynamicToVar accShs
  (!vs2, !asts2) <- V.unzip <$> V.mapM dynamicToVar eShs
  (!vs3, !asts3) <- V.unzip <$> V.mapM dynamicToVar accShs
  (!vs4, !asts4) <- V.unzip <$> V.mapM dynamicToVar eShs
  let !x = f asts1 asts2 asts3 asts4
  return (V.toList vs1, V.toList vs2, V.toList vs3, V.toList vs4, x)

funToAstHHHH :: (HVector (AstRanked s) -> HVector (AstRanked s)
                   -> HVector (AstRanked s) -> HVector (AstRanked s)
                   -> a)
               -> VoidHVector
               -> VoidHVector
               -> ( [AstDynamicVarName]
                  , [AstDynamicVarName]
                  , [AstDynamicVarName]
                  , [AstDynamicVarName]
                  , a )
{-# NOINLINE funToAstHHHH #-}
funToAstHHHH f accShs eShs = unsafePerformIO $ funToAstHHHHIO f accShs eShs

funToAstHHHGIO :: (HVector (AstRanked s) -> HVector (AstRanked s)
                   -> HVector (AstRanked s) -> HVector (AstRanked s)
                   -> a)
               -> VoidHVector
               -> VoidHVector
               -> VoidHVector
               -> IO ( [AstDynamicVarName]
                     , [AstDynamicVarName]
                     , [AstDynamicVarName]
                     , [AstDynamicVarName]
                     , a )
{-# INLINE funToAstHHHGIO #-}
funToAstHHHGIO f accShs bShs eShs = do
  (!vs1, !asts1) <- V.unzip <$> V.mapM dynamicToVar accShs
  (!vs2, !asts2) <- V.unzip <$> V.mapM dynamicToVar bShs
  (!vs3, !asts3) <- V.unzip <$> V.mapM dynamicToVar accShs
  (!vs4, !asts4) <- V.unzip <$> V.mapM dynamicToVar eShs
  let !x = f asts1 asts2 asts3 asts4
  return (V.toList vs1, V.toList vs2, V.toList vs3, V.toList vs4, x)

funToAstHHHG :: (HVector (AstRanked s) -> HVector (AstRanked s)
                   -> HVector (AstRanked s) -> HVector (AstRanked s)
                   -> a)
               -> VoidHVector
               -> VoidHVector
               -> VoidHVector
               -> ( [AstDynamicVarName]
                  , [AstDynamicVarName]
                  , [AstDynamicVarName]
                  , [AstDynamicVarName]
                  , a )
{-# NOINLINE funToAstHHHG #-}
funToAstHHHG f accShs bShs eShs =
  unsafePerformIO $ funToAstHHHGIO f accShs bShs eShs

funToAstHVectorIO
  :: (HVector (AstRanked s) -> AstRanked s r n)
  -> VoidHVector
  -> IO ([AstDynamicVarName], AstRanked s r n)
{-# INLINE funToAstHVectorIO #-}
funToAstHVectorIO g parameters0 = do
  (!vars, !asts) <- V.unzip <$> V.mapM dynamicToVar parameters0
  let !x = g asts
  return (V.toList vars, x)

dynamicToVar :: DynamicTensor VoidTensor
             -> IO (AstDynamicVarName, DynamicTensor (AstRanked s))
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
        !dynE = DynamicShaped @r2 @sh2 (AstVarS (AstVarName freshId))
    in (varE, dynE)

funToAstHVector
  :: (HVector (AstRanked s) -> AstRanked s r n)
  -> VoidHVector
  -> ([AstDynamicVarName], AstRanked s r n)
{-# NOINLINE funToAstHVector #-}
funToAstHVector g parameters0 =
  unsafePerformIO $ funToAstHVectorIO g parameters0

funToAstRevIO :: VoidHVector
              -> IO ( [AstDynamicVarName]
                    , HVector (AstRanked PrimalSpan)
                    , [AstDynamicVarName]
                    , HVector (AstRanked FullSpan) )
{-# INLINE funToAstRevIO #-}
funToAstRevIO parameters0 = do
  let f :: DynamicTensor VoidTensor
        -> IO ( AstDynamicVarName, AstDynamic PrimalSpan
              , AstDynamicVarName, AstDynamic FullSpan )
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
funToAstRev :: VoidHVector
            -> ( [AstDynamicVarName]
               , HVector (AstRanked PrimalSpan)
               , [AstDynamicVarName]
               , HVector (AstRanked FullSpan) )
{-# NOINLINE funToAstRev #-}
funToAstRev parameters0 = unsafePerformIO $ do
  (!varsPrimal, !astsPrimal, !vars, !asts) <- funToAstRevIO parameters0
  return (varsPrimal, astsPrimal, vars, asts)

funToAstFwdIO :: VoidHVector
              -> IO ( [AstDynamicVarName]
                    , HVector (AstRanked PrimalSpan)
                    , [AstDynamicVarName]
                    , HVector (AstRanked PrimalSpan)
                    , [AstDynamicVarName]
                    , HVector (AstRanked FullSpan) )
{-# INLINE funToAstFwdIO #-}
funToAstFwdIO parameters0 = do
  let f :: DynamicTensor VoidTensor
        -> IO ( AstDynamicVarName, AstDynamic PrimalSpan
              , AstDynamicVarName, AstDynamic PrimalSpan
              , AstDynamicVarName, AstDynamic FullSpan )
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
funToAstFwd :: VoidHVector
            -> ( [AstDynamicVarName]
               , HVector (AstRanked PrimalSpan)
               , [AstDynamicVarName]
               , HVector (AstRanked PrimalSpan)
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
