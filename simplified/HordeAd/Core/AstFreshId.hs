-- | Operations that (usually impurely) generate fresh variables.
module HordeAd.Core.AstFreshId
  ( astRegisterFun, astRegisterADShare
  , funToAstR, funToAstD, ADAstVars, funToAstAll
  , funToAstIIO, funToAstI, funToAstIndexIO, funToAstIndex
  , funToAstIOS, funToAstS, astRegisterFunS, funToAstIndexIOS, funToAstIndexS
  , resetVarCounter
  ) where

import Prelude

import           Control.Monad (replicateM)
import           Data.Array.Internal (valueOf)
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as OS
import qualified Data.Array.ShapedS as OS
import           Data.IORef.Unboxed
  (Counter, atomicAddCounter_, newCounter, writeIORefU)
import           Data.Proxy (Proxy)
import           GHC.TypeLits (KnownNat, SomeNat (..), someNatVal)
import           System.IO.Unsafe (unsafePerformIO)

import           HordeAd.Core.Ast
import           HordeAd.Core.AstTools
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.SizedList

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

astRegisterFun :: (ShowAst r, KnownNat n)
               => AstRanked r n -> [(AstVarId, AstDynamic r)]
               -> ([(AstVarId, AstDynamic r)], AstRanked r n)
{-# NOINLINE astRegisterFun #-}
astRegisterFun !r !l | astIsSmall r = (l, r)
astRegisterFun !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !r2 = AstVar (shapeAst r) freshId
  return ((freshId, AstRToD r) : l, r2)

astRegisterADShare :: (ShowAst r, KnownNat n)
                   => AstRanked r n -> ADShare r
                   -> (ADShare r, AstRanked r n)
{-# NOINLINE astRegisterADShare #-}
astRegisterADShare !r !l | astIsSmall r = (l, r)
astRegisterADShare !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !l2 = insertADShare freshId (AstRToD r) l
      !r2 = AstVar (shapeAst r) freshId
  return (l2, r2)

funToAstRIO :: ShapeInt n -> (AstRanked r n -> AstRanked r m)
            -> IO (AstVarName (OR.Array n r), AstRanked r m)
{-# INLINE funToAstRIO #-}
funToAstRIO sh f = do
  freshId <- unsafeGetFreshAstVarId
  return (AstVarName freshId, f (AstVar sh freshId))

funToAstR :: ShapeInt n -> (AstRanked r n -> AstRanked r m)
          -> (AstVarName (OR.Array n r), AstRanked r m)
{-# NOINLINE funToAstR #-}
funToAstR sh f = unsafePerformIO $ funToAstRIO sh f

funToAstRshIO :: IO (AstVarName (OR.Array n r), ShapeInt n -> AstRanked r n)
{-# INLINE funToAstRshIO #-}
funToAstRshIO = do
  freshId <- unsafeGetFreshAstVarId
  return (AstVarName freshId, \sh -> AstVar sh freshId)

-- The "fun"ction in this case is fixed to be @id@.
funToAstDIO :: forall r. [Int] -> IO (AstDynamicVarName r, AstDynamic r)
{-# INLINE funToAstDIO #-}
funToAstDIO sh = do
  freshId <- unsafeGetFreshAstVarId
  return $! case someNatVal $ toInteger $ length sh of
    Just (SomeNat (_proxy :: Proxy p)) ->
      let shn = listShapeToShape @p sh
          varName = AstVarName @(OR.Array p r) freshId
      in (AstDynamicVarName varName, AstRToD (AstVar shn freshId))
    Nothing -> error "funToAstD: impossible someNatVal error"

funToAstD :: forall r. [Int] -> (AstDynamicVarName r, AstDynamic r)
{-# NOINLINE funToAstD #-}
funToAstD sh = unsafePerformIO $ funToAstDIO sh

type ADAstVars n r = (ShapeInt n -> AstRanked r n, [AstDynamic r])

funToAstAll :: [[Int]] -> (ADAstVarNames n r, ADAstVars n r)
{-# NOINLINE funToAstAll #-}
funToAstAll shapes1 = unsafePerformIO $ do
  (vnDt, vDt) <- funToAstRshIO
  (vn1, v1) <- unzip <$> (mapM funToAstDIO shapes1)
  return ((vnDt, vn1), (vDt, v1))

funToAstIIO :: (AstInt r -> t) -> IO (AstVarId, t)
{-# INLINE funToAstIIO #-}
funToAstIIO f = do
  freshId <- unsafeGetFreshAstVarId
  return (freshId, f (AstIntVar freshId))

funToAstI :: (AstInt r -> t) -> (AstVarId, t)
{-# NOINLINE funToAstI #-}
funToAstI = unsafePerformIO . funToAstIIO

funToAstIndexIO
  :: forall m p r. KnownNat m
  => Int -> (AstIndex r m -> AstIndex r p) -> IO (AstVarList m, AstIndex r p)
{-# INLINE funToAstIndexIO #-}
funToAstIndexIO p f = do
  varList <- replicateM p unsafeGetFreshAstVarId
  return (listToSized varList, f (listToIndex $ map AstIntVar varList))

funToAstIndex
  :: forall m p r. KnownNat m
  => (AstIndex r m -> AstIndex r p) -> (AstVarList m, AstIndex r p)
{-# NOINLINE funToAstIndex #-}
funToAstIndex = unsafePerformIO . funToAstIndexIO (valueOf @m)

funToAstIOS :: forall sh sh2 r. (AstShaped r sh -> AstShaped r sh2)
            -> IO (AstVarName (OS.Array sh r), AstShaped r sh2)
{-# INLINE funToAstIOS #-}
funToAstIOS f = do
  freshId <- unsafeGetFreshAstVarId
  return (AstVarName freshId, f (AstVarS freshId))

funToAstS :: forall sh sh2 r. (AstShaped r sh -> AstShaped r sh2)
          -> (AstVarName (OS.Array sh r), AstShaped r sh2)
{-# NOINLINE funToAstS #-}
funToAstS f = unsafePerformIO $ funToAstIOS f

astRegisterFunS :: (OS.Shape sh, KnownNat (OS.Rank sh))
                => AstShaped r sh -> [(AstVarId, AstDynamic r)]
                -> ([(AstVarId, AstDynamic r)], AstShaped r sh)
{-# NOINLINE astRegisterFunS #-}
-- astRegisterFun !r !l | astIsSmall r = (l, r)
astRegisterFunS !r !l = unsafePerformIO $ do
  freshId <- unsafeGetFreshAstVarId
  let !r2 = AstVarS freshId
  return ((freshId, AstSToD r) : l, r2)

funToAstIndexIOS
  :: forall sh1 sh2 r. OS.Shape sh1
  => (AstIndexS r sh1 -> AstIndexS r sh2)
  -> IO (AstVarListS sh1, AstIndexS r sh2)
{-# INLINE funToAstIndexIOS #-}
funToAstIndexIOS f = do
  let p = length $ OS.shapeT @sh1
  varList <- replicateM p unsafeGetFreshAstVarId
  return ( ShapedList.listToSized varList
         , f (ShapedList.listToSized $ map AstIntVar varList) )

funToAstIndexS
  :: forall sh1 sh2 r. OS.Shape sh1
  => (AstIndexS r sh1 -> AstIndexS r sh2) -> (AstVarListS sh1, AstIndexS r sh2)
{-# NOINLINE funToAstIndexS #-}
funToAstIndexS = unsafePerformIO . funToAstIndexIOS
