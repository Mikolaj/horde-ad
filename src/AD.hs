{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module AD (result) where

import Prelude

import           Control.Monad.Trans.State.Strict
import qualified Data.EnumMap.Lazy as EML
import qualified Data.Vector as V

type Result = Float

data Dual d = D Float d

type Vec a = V.Vector a

newtype DeltaId = DeltaId Int
  deriving (Show, Eq, Ord, Enum)

-- Tagless final doesn't seem to work well, because we need to gather
-- @Delta@ while doing @Dual Delta@ operations, but evaluate on concrete
-- vectors that correspond to only the second component of dual numbers.
-- Also, initial encoding gives us full control over
-- when to evaluate. With final, we'd need to be careful
-- about laziness to ensure the optimal evaluation order is chosen
-- (whatever it is for a given differentiated program).
data Delta =
    Zero
  | OneHot Int
  | Scale Float Delta
  | Add Delta Delta
  | Var DeltaId

-- This can't be environment, because subtrees enter their own
-- identifiers, for sharing, not parents name their subtrees.
-- Each variable is created only once, but the subexpression it's in
-- can get duplicated grossly.
data DeltaState = DeltaState
  { deltaCounter  :: DeltaId
  , deltaBindings :: EML.EnumMap DeltaId Delta
  }

newtype DeltaImplementation a = DeltaImplementation
  { runDeltaImplementation :: StateT DeltaState IO a }
  deriving (Monad, Functor, Applicative)

eval :: EML.EnumMap DeltaId Delta -> Int -> Delta -> Vec Result
eval deltaBindings dim d0 =
  let ev store = \case
        Zero -> (V.replicate dim 0, store)
        OneHot i -> (V.replicate dim 0 V.// [(i, 1)], store)
        Scale k d ->
          let (v1, storeNew) = ev store d
          in (V.map (* k) v1, storeNew)
        Add d1 d2 ->
          let (v1, store1) = ev store d1
              (v2, store2) = ev store1 d2
          in (V.zipWith (+) v1 v2, store2)
        Var i -> case EML.lookup i store of
          Nothing ->
            let (v, storeNew) = ev store $ deltaBindings EML.! i
            in (v, EML.insert i v storeNew)
          Just v -> (v, store)
  in fst $ ev EML.empty d0

dlet :: Delta -> DeltaImplementation DeltaId
dlet v = DeltaImplementation $ do
  i <- succ <$> gets deltaCounter
  modify $ \s ->
    s { deltaCounter = i
      , deltaBindings = EML.insert i v $ deltaBindings s
      }
  return i

(*\) :: Dual Delta -> Dual Delta -> DeltaImplementation (Dual Delta)
(*\) (D u u') (D v v') = do
  d <- dlet $ Add (Scale v u') (Scale u v')
  return $! D (u * v) (Var d)

df :: (Vec (Dual Delta) -> DeltaImplementation (Dual Delta))
   -> Vec Float
   -> IO (Vec Result)
df f deltaInput = do
  let dx :: Vec (Dual Delta)
      dx = V.imap (\i xi -> D xi (OneHot i)) deltaInput
      initialState = DeltaState
        { deltaCounter = DeltaId 0
        , deltaBindings = EML.empty
        }
  (D _result d, st) <- runStateT (runDeltaImplementation (f dx)) initialState
  return $! eval (deltaBindings st) (V.length deltaInput) d

xsquared :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
xsquared vec = do
  let x = vec V.! 0
      y = vec V.! 1
  xy <- x *\ y
  x *\ xy

result :: IO (Vec Result)
result = df xsquared $ V.fromList [3, 2]








-- higher order types of vars
-- recursion and recursive types
-- fusion and checkpointing

























-- THE END
