-- | Operations that (usually impurely) generate fresh variables.
module HordeAd.Core.AstFreshId
  ( astRegisterFun, astRegisterADShare, astRegisterADShareS
  , funToAstIOR, funToAstR
  , funToAstAllIO, funToAstAll, funToAstAllIOS, funToAstAllS
  , funToAstIOI, funToAstI, funToAstIndexIO, funToAstIndex
  , funToAstIOS, funToAstS, astRegisterFunS, funToAstIndexIOS, funToAstIndexS
  , resetVarCounter
  ) where

import Prelude

import           Control.Monad (replicateM)
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Shape as OS
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import           System.IO.Unsafe (unsafePerformIO)

import           HordeAd.Core.Ast
import           HordeAd.Core.AstTools
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.SizedList
import           HordeAd.Core.Types

-- Impure but in the most trivial way (only ever incremented counter).
unsafeAstVarCounter :: Counter
{-# NOINLINE unsafeAstVarCounter #-}
unsafeAstVarCounter = unsafePerformIO (newCounter 100000001)

-- Only for tests, e.g., to ensure show applied to terms has stable length.
-- Tests using this need to be run with -ftest_seq to avoid variable confusion.
resetVarCounter :: IO ()
resetVarCounter = writeIORefU unsafeAstVarCounter 100000001

unsafeGetFreshAstId :: IO AstId
{-# INLINE unsafeGetFreshAstId #-}
unsafeGetFreshAstId =
  intToAstId <$> atomicAddCounter_ unsafeAstVarCounter 1

unsafeGetFreshAstVarId :: IO (AstVarId s)
{-# INLINE unsafeGetFreshAstVarId #-}
unsafeGetFreshAstVarId =
  intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

unsafeGetFreshAstVarName :: IO (AstVarName s f r y)
{-# INLINE unsafeGetFreshAstVarName #-}
unsafeGetFreshAstVarName =
  AstVarName . intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

astRegisterFun
  :: (GoodScalar r, KnownNat n)
  => AstRanked s r n -> [(AstId, DynamicExists (AstDynamic s))]
  -> ([(AstId, DynamicExists (AstDynamic s))], AstRanked s r n)
{-# NOINLINE astRegisterFun #-}
astRegisterFun !r !l | astIsSmall True r = (l, r)
astRegisterFun !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstId
  let !r2 = AstVar (shapeAst r) $ AstVarName $ astIdToAstVarId freshId
  return ((freshId, DynamicExists $ AstRToD r) : l, r2)

astRegisterFunS
  :: (OS.Shape sh, GoodScalar r)
  => AstShaped s r sh -> [(AstId, DynamicExists (AstDynamic s))]
  -> ([(AstId, DynamicExists (AstDynamic s))], AstShaped s r sh)
{-# NOINLINE astRegisterFunS #-}
astRegisterFunS !r !l | astIsSmallS True r = (l, r)
astRegisterFunS !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstId
  let !r2 = AstVarS $ AstVarName $ astIdToAstVarId freshId
  return ((freshId, DynamicExists $ AstSToD r) : l, r2)

astRegisterADShare :: (GoodScalar r, KnownNat n)
                   => AstRanked AstPrimal r n -> ADShare
                   -> (ADShare, AstRanked AstPrimal r n)
{-# NOINLINE astRegisterADShare #-}
astRegisterADShare !r !l | astIsSmall True r = (l, r)
astRegisterADShare !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstId
  let !l2 = insertADShare freshId (AstRToD r) l
      !r2 = AstVar (shapeAst r) $ AstVarName $ astIdToAstVarId freshId
  return (l2, r2)

astRegisterADShareS :: (GoodScalar r, OS.Shape sh)
                    => AstShaped AstPrimal r sh -> ADShare
                    -> (ADShare, AstShaped AstPrimal r sh)
{-# NOINLINE astRegisterADShareS #-}
astRegisterADShareS !r !l | astIsSmallS True r = (l, r)
astRegisterADShareS !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstId
  let !l2 = insertADShare freshId (AstSToD r) l
      !r2 = AstVarS $ AstVarName $ astIdToAstVarId freshId
  return (l2, r2)

funToAstIOR :: forall n m s r r2. GoodScalar r
            => ShapeInt n -> (AstRanked s r n -> AstRanked s r2 m)
            -> IO ( AstVarName s (AstRanked s) r n
                  , AstDynamicVarName s (AstRanked s)
                  , AstRanked s r2 m )
{-# INLINE funToAstIOR #-}
funToAstIOR sh f = do
  freshId <- unsafeGetFreshAstVarId
  return $! OS.withShapeP (shapeToList sh) $ \(Proxy :: Proxy sh) ->
    let varName = AstVarName freshId
    in ( varName
       , AstDynamicVarName @sh varName
       , f (AstVar sh varName) )

funToAstR :: GoodScalar r
          => ShapeInt n -> (AstRanked s r n -> AstRanked s r2 m)
          -> (AstVarName s (AstRanked s) r n, AstRanked s r2 m)
{-# NOINLINE funToAstR #-}
funToAstR sh f = unsafePerformIO $ do
  (var, _, ast) <- funToAstIOR sh f
  return (var, ast)

funToAstIOS :: forall sh sh2 s r r2. (OS.Shape sh, GoodScalar r)
            => (AstShaped s r sh -> AstShaped s r2 sh2)
            -> IO ( AstVarName s (AstShaped s) r sh
                  , AstDynamicVarName s (AstShaped s)
                  , AstShaped s r2 sh2 )
{-# INLINE funToAstIOS #-}
funToAstIOS f = do
  freshId <- unsafeGetFreshAstVarId
  let varName = AstVarName freshId
  return ( varName
         , AstDynamicVarName @sh varName
         , f (AstVarS varName) )

funToAstS :: forall sh sh2 s r r2. (OS.Shape sh, GoodScalar r)
          => (AstShaped s r sh -> AstShaped s r2 sh2)
          -> (AstVarName s (AstShaped s) r sh, AstShaped s r2 sh2)
{-# NOINLINE funToAstS #-}
funToAstS f = unsafePerformIO $ do
  (var, _, ast) <- funToAstIOS f
  return (var, ast)

funToAstAllIO :: DomainsOD
              -> IO ( [AstDynamicVarName AstPrimal (AstRanked AstPrimal)]
                    , [DynamicExists (AstDynamic AstFull)]
                    , [DynamicExists (AstDynamic AstPrimal)] )
{-# INLINE funToAstAllIO #-}
funToAstAllIO parameters0 = do
  let f (DynamicExists @r2 e) = do
        let sh = OD.shapeL e
        fId <- unsafeGetFreshAstVarId
        let freshId :: AstVarId s
            freshId = intToAstVarId (fromEnum fId)
        return $! OS.withShapeP sh $ \(Proxy :: Proxy sh) ->
          case someNatVal $ toInteger $ length sh of
            Just (SomeNat @n _) ->
              let dynE :: DynamicExists (AstDynamic s)
                  dynE = DynamicExists @r2
                         $ AstRToD @n (AstVar (listShapeToShape sh)
                                              (AstVarName freshId))
              in (AstDynamicVarName @sh @r2 (AstVarName freshId), dynE, dynE)
            Nothing -> error "funToAstAllIO: impossible someNatVal error"
  unzip3 <$> mapM f (V.toList parameters0)

-- The AstVarName type with its parameter somehow prevents cse and crashes
-- compared with a bare AstVarId, so let's keep it.
funToAstAll :: DomainsOD
            -> ( ( AstVarName AstPrimal f r y
                 , [AstDynamicVarName AstPrimal (AstRanked AstPrimal)] )
               , [DynamicExists (AstDynamic AstFull)]
               , [DynamicExists (AstDynamic AstPrimal)] )
{-# NOINLINE funToAstAll #-}
funToAstAll parameters0 = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  (vars1, asts1, astsPrimal1) <- funToAstAllIO parameters0
  return ((AstVarName freshId, vars1), asts1, astsPrimal1)

funToAstAllIOS :: DomainsOD
               -> IO ( [AstDynamicVarName AstPrimal (AstShaped AstPrimal)]
                     , [DynamicExists (AstDynamic AstFull)]
                     , [DynamicExists (AstDynamic AstPrimal)] )
{-# INLINE funToAstAllIOS #-}
funToAstAllIOS parameters0 = do
  let f (DynamicExists @r2 e) = do
        let sh = OD.shapeL e
        fId <- unsafeGetFreshAstVarId
        let freshId :: AstVarId s
            freshId = intToAstVarId (fromEnum fId)
        return $! OS.withShapeP sh $ \(Proxy :: Proxy sh) ->
          let dynE :: DynamicExists (AstDynamic s)
              dynE = DynamicExists @r2
                     $ AstSToD (AstVarS @sh (AstVarName freshId))
          in (AstDynamicVarName @sh @r2 (AstVarName freshId), dynE, dynE)
  unzip3 <$> mapM f (V.toList parameters0)

-- The AstVarName type with its parameter somehow prevents cse and crashes
-- compared with a bare AstVarId, so let's keep it.
funToAstAllS :: DomainsOD
             -> ( ( AstVarName AstPrimal f r y
                  , [AstDynamicVarName AstPrimal (AstShaped AstPrimal)] )
                , [DynamicExists (AstDynamic AstFull)]
                , [DynamicExists (AstDynamic AstPrimal)] )
{-# NOINLINE funToAstAllS #-}
funToAstAllS parameters0 = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  (vars1, asts1, astsPrimal1) <- funToAstAllIOS parameters0
  return ((AstVarName freshId, vars1), asts1, astsPrimal1)

funToAstIOI :: (AstInt -> t) -> IO (IntVarName, t)
{-# INLINE funToAstIOI #-}
funToAstIOI f = do
  freshId <- unsafeGetFreshAstVarName
  return (freshId, f (AstIntVar freshId))

funToAstI :: (AstInt -> t) -> (IntVarName, t)
{-# NOINLINE funToAstI #-}
funToAstI = unsafePerformIO . funToAstIOI

funToAstIndexIO
  :: forall m p. KnownNat m
  => Int -> (AstIndex m -> AstIndex p) -> IO (AstVarList m, AstIndex p)
{-# INLINE funToAstIndexIO #-}
funToAstIndexIO p f = do
  varList <- replicateM p unsafeGetFreshAstVarName
  return (listToSized varList, f (listToIndex $ map AstIntVar varList))

funToAstIndex
  :: forall m p. KnownNat m
  => (AstIndex m -> AstIndex p) -> (AstVarList m, AstIndex p)
{-# NOINLINE funToAstIndex #-}
funToAstIndex = unsafePerformIO . funToAstIndexIO (valueOf @m)

funToAstIndexIOS
  :: forall sh1 sh2. OS.Shape sh1
  => (AstIndexS sh1 -> AstIndexS sh2)
  -> IO (AstVarListS sh1, AstIndexS sh2)
{-# INLINE funToAstIndexIOS #-}
funToAstIndexIOS f = do
  let p = length $ OS.shapeT @sh1
  varList <- replicateM p unsafeGetFreshAstVarName
  return ( ShapedList.listToSized varList
         , f (ShapedList.listToSized $ map AstIntVar varList) )

funToAstIndexS
  :: forall sh1 sh2. OS.Shape sh1
  => (AstIndexS sh1 -> AstIndexS sh2) -> (AstVarListS sh1, AstIndexS sh2)
{-# NOINLINE funToAstIndexS #-}
funToAstIndexS = unsafePerformIO . funToAstIndexIOS
