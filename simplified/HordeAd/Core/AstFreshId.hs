-- | Operations that (usually impurely) generate fresh variables.
module HordeAd.Core.AstFreshId
  ( astRegisterFun, astRegisterADShare, astRegisterADShareS
  , funToAstIOR, funToAstR, funToAst2, funToAstAll
  , funToAstIOI, funToAstI, funToAstIndexIO, funToAstIndex
  , funToAstIOS, funToAstS, astRegisterFunS, funToAstIndexIOS, funToAstIndexS
  , resetVarCounter
  ) where

import Prelude

import           Control.Monad (replicateM)
import qualified Data.Array.DynamicS as OD
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
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

unsafeGetFreshAstVarId :: IO AstVarId
{-# INLINE unsafeGetFreshAstVarId #-}
unsafeGetFreshAstVarId =
  intToAstVarId <$> atomicAddCounter_ unsafeAstVarCounter 1

astRegisterFun :: (GoodScalar r, KnownNat n)
               => AstRanked s r n -> [(AstVarId, DynamicExists (AstDynamic s))]
               -> ([(AstVarId, DynamicExists (AstDynamic s))], AstRanked s r n)
{-# NOINLINE astRegisterFun #-}
astRegisterFun !r !l | astIsSmall True r = (l, r)
astRegisterFun !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !r2 = AstVar (shapeAst r) freshId
  return ((freshId, DynamicExists $ AstRToD r) : l, r2)

astRegisterFunS :: (OS.Shape sh, GoodScalar r)
                => AstShaped s r sh -> [(AstVarId, DynamicExists (AstDynamic s))]
                -> ([(AstVarId, DynamicExists (AstDynamic s))], AstShaped s r sh)
{-# NOINLINE astRegisterFunS #-}
astRegisterFunS !r !l | astIsSmallS True r = (l, r)
astRegisterFunS !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !r2 = AstVarS freshId
  return ((freshId, DynamicExists $ AstSToD r) : l, r2)

astRegisterADShare :: (GoodScalar r, KnownNat n)
                   => AstRanked AstPrimal r n -> ADShare
                   -> (ADShare, AstRanked AstPrimal r n)
{-# NOINLINE astRegisterADShare #-}
astRegisterADShare !r !l | astIsSmall True r = (l, r)
astRegisterADShare !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !l2 = insertADShare freshId (AstRToD r) l
      !r2 = AstVar (shapeAst r) freshId
  return (l2, r2)

astRegisterADShareS :: (GoodScalar r, OS.Shape sh)
                    => AstShaped AstPrimal r sh -> ADShare
                    -> (ADShare, AstShaped AstPrimal r sh)
{-# NOINLINE astRegisterADShareS #-}
astRegisterADShareS !r !l | astIsSmallS True r = (l, r)
astRegisterADShareS !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !l2 = insertADShare freshId (AstSToD r) l
      !r2 = AstVarS freshId
  return (l2, r2)

funToAstIOR :: forall n m s r r2. GoodScalar r
            => ShapeInt n -> (AstRanked s r n -> AstRanked s r2 m)
            -> IO ( AstVarName (Flip OR.Array r n)
                  , AstDynamicVarName
                  , AstRanked s r2 m )
{-# INLINE funToAstIOR #-}
funToAstIOR sh f = do
  freshId <- unsafeGetFreshAstVarId
  return $! OS.withShapeP (shapeToList sh) $ \(Proxy :: Proxy sh) ->
    ( AstVarName freshId
    , AstDynamicVarName @sh @r freshId
    , f (AstVar sh freshId) )

funToAstR :: GoodScalar r
          => ShapeInt n -> (AstRanked s r n -> AstRanked s r2 m)
          -> (AstVarName (Flip OR.Array r n), AstRanked s r2 m)
{-# NOINLINE funToAstR #-}
funToAstR sh f = unsafePerformIO $ do
  (var, _, ast) <- funToAstIOR sh f
  return (var, ast)

funToAstIOS :: forall sh sh2 s r r2. (OS.Shape sh, GoodScalar r)
            => (AstShaped s r sh -> AstShaped s r2 sh2)
            -> IO ( AstVarName (Flip OS.Array r sh)
                  , AstDynamicVarName
                  , AstShaped s r2 sh2 )
{-# INLINE funToAstIOS #-}
funToAstIOS f = do
  freshId <- unsafeGetFreshAstVarId
  return ( AstVarName freshId
         , AstDynamicVarName @sh @r freshId
         , f (AstVarS freshId) )

funToAstS :: forall sh sh2 s r r2. (OS.Shape sh, GoodScalar r)
          => (AstShaped s r sh -> AstShaped s r2 sh2)
          -> (AstVarName (Flip OS.Array r sh), AstShaped s r2 sh2)
{-# NOINLINE funToAstS #-}
funToAstS f = unsafePerformIO $ do
  (var, _, ast) <- funToAstIOS f
  return (var, ast)

-- The "fun"ction in this case is fixed to be @id@.
funToAstDIO :: forall s r. GoodScalar r
            => Proxy r -> [Int]
            -> IO (AstDynamicVarName, DynamicExists (AstDynamic s))
{-# INLINE funToAstDIO #-}
funToAstDIO _ sh = do
  freshId <- unsafeGetFreshAstVarId
  return $! OS.withShapeP sh $ \(Proxy :: Proxy sh) ->
    ( AstDynamicVarName @sh @r freshId
    , DynamicExists @r $ AstSToD (AstVarS @sh freshId) )

funToAst2IO :: DomainsOD
            -> IO ([AstDynamicVarName], [DynamicExists (AstDynamic s)])
{-# INLINE funToAst2IO #-}
funToAst2IO parameters0 = do
  let f (DynamicExists @r2 e) = funToAstDIO (Proxy @r2) (OD.shapeL e)
  unzip <$> mapM f (V.toList parameters0)

funToAst2 :: DomainsOD -> ([AstDynamicVarName], [DynamicExists (AstDynamic s)])
{-# NOINLINE funToAst2 #-}
funToAst2 parameters0 = unsafePerformIO $ funToAst2IO parameters0

funToAstAllIO :: DomainsOD
              -> IO ( [AstDynamicVarName]
                    , [DynamicExists (AstDynamic AstFull)]
                    , [DynamicExists (AstDynamic AstPrimal)] )
{-# INLINE funToAstAllIO #-}
funToAstAllIO parameters0 = do
  let f (DynamicExists @r2 e) = do
        let sh = OD.shapeL e
        freshId <- unsafeGetFreshAstVarId
        return $! OS.withShapeP sh $ \(Proxy :: Proxy sh) ->
          let dynE :: DynamicExists (AstDynamic s)
              dynE = DynamicExists @r2 $ AstSToD (AstVarS @sh freshId)
          in (AstDynamicVarName @sh @r2 freshId, dynE, dynE)
  unzip3 <$> mapM f (V.toList parameters0)

-- The AstVarName type with its parameter somehow prevents cse and crashes
-- compared with a bare AstVarId, so let's keep it.
funToAstAll :: DomainsOD
            -> ( (AstVarName t, [AstDynamicVarName])
               , [DynamicExists (AstDynamic AstFull)]
               , [DynamicExists (AstDynamic AstPrimal)] )
{-# NOINLINE funToAstAll #-}
funToAstAll parameters0 = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  (vars1, asts1, astsPrimal1) <- funToAstAllIO parameters0
  return ((AstVarName freshId, vars1), asts1, astsPrimal1)

funToAstIOI :: (AstInt -> t) -> IO (AstVarId, t)
{-# INLINE funToAstIOI #-}
funToAstIOI f = do
  freshId <- unsafeGetFreshAstVarId
  return (freshId, f (AstIntVar freshId))

funToAstI :: (AstInt -> t) -> (AstVarId, t)
{-# NOINLINE funToAstI #-}
funToAstI = unsafePerformIO . funToAstIOI

funToAstIndexIO
  :: forall m p. KnownNat m
  => Int -> (AstIndex m -> AstIndex p) -> IO (AstVarList m, AstIndex p)
{-# INLINE funToAstIndexIO #-}
funToAstIndexIO p f = do
  varList <- replicateM p unsafeGetFreshAstVarId
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
  varList <- replicateM p unsafeGetFreshAstVarId
  return ( ShapedList.listToSized varList
         , f (ShapedList.listToSized $ map AstIntVar varList) )

funToAstIndexS
  :: forall sh1 sh2. OS.Shape sh1
  => (AstIndexS sh1 -> AstIndexS sh2) -> (AstVarListS sh1, AstIndexS sh2)
{-# NOINLINE funToAstIndexS #-}
funToAstIndexS = unsafePerformIO . funToAstIndexIOS
