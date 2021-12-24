{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TypeSynonymInstances #-}
module AD (result) where

import Prelude

import           Control.Monad.Trans.State.Strict
import qualified Data.EnumMap.Lazy as EML
import           Data.Maybe (fromJust)
import qualified Data.Vector as V

type Result = Float

data Dual d = D Float d

type Vec a = V.Vector a

newtype DeltaId = DeltaId Int
  deriving (Show, Eq, Ord, Enum)

class Delta v m where
  dzero :: m v
  doneHot :: Int -> m v
  dscale :: Float -> v -> m v
  dadd :: v -> v -> m v
  dvar :: DeltaId -> m v
  dlet :: v -> m DeltaId

-- This can't be environment, because subtrees enter their own
-- identifiers, for sharing, not parents name their subtrees.
-- Each variable is created only once, but the subexpression it's in
-- can get duplicated grossly.
data DeltaState v = DeltaState
  { deltaCounter  :: DeltaId
  , deltaBindings :: EML.EnumMap DeltaId v
  , deltaDim      :: Int
  , deltaInput    :: v
  }

newtype DeltaImplementation a = DeltaImplementation
  { runDeltaImplementation :: StateT (DeltaState (Vec Float)) IO a }
  deriving (Monad, Functor, Applicative)

instance Delta (Vec Float) DeltaImplementation where
  dzero = DeltaImplementation $ do
    dim <- gets deltaDim
    return $! V.replicate dim 0
  doneHot i = DeltaImplementation $ do
    dim <- gets deltaDim
    input <- gets deltaInput
    return $! V.replicate dim 0 V.// [(i, input V.! i)]
  dscale k v1 = return $! V.map (* k) v1
  dadd v1 v2 = return $! V.zipWith (+) v1 v2
  dvar i = DeltaImplementation $ do
    bindings <- gets deltaBindings
    return $! bindings EML.! i
  dlet v = DeltaImplementation $ do
    i <- succ <$> gets deltaCounter
    modify $ \s ->
      s { deltaCounter = i
        , deltaBindings = EML.insert i v $ deltaBindings s
        }
    return i

(*\) :: Dual (Vec Float)
     -> Dual (Vec Float)
     -> DeltaImplementation (Dual (Vec Float))
(*\) (D u u') (D v v') = do
  scvu <- dscale v u'
  scuv <- dscale u v'
  a <- dadd scvu scuv
  i <- dlet a
  var <- dvar i
  return $! D (u * v) var

df :: (Vec (Dual (Vec Float)) -> DeltaImplementation (Dual (Vec Float)))
   -> Vec Float
   -> IO (Vec Result)
df f x = do
  let dx :: Vec (Dual (Vec Float))
      dx = V.imap (\i xi -> D xi (doneHot i)) x
      initialState = DeltaState
        { deltaCounter = DeltaId 0
        , deltaBindings = EML.empty
        , deltaDim = V.length x
        , deltaInput = x
        }
  D _result d <- evalStateT (runDeltaImplementation (f dx)) initialState
  return $! d

xsquared :: Vec (Dual (Vec Float))
         -> DeltaImplementation (Dual (Vec Float))
xsquared _vec = do
  let x = D 0 (doneHot 1)
  x *\ x

result :: IO (Vec Result)
result = df xsquared $ V.fromList [5]



-- higher order types of vars
-- recursion and recursive types
-- fusion and checkpointing

























-- THE END
