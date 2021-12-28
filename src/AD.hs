{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module AD where

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

-- This can't be environment in a Reader, because subtrees add their own
-- identifiers for sharing, instead of parents naming their subtrees.
-- This must be the "evaluate Let backwards" from SPJ's talk.
-- This and the need to control evaluation order contribute to
-- the difficulty of applying any HOAS concept instead of the monad
-- with bindings accumulated in state.
-- Note that each variable is created only once, but the subexpression
-- it's a part of can get duplicated grossly.
data DeltaState = DeltaState
  { deltaCounter  :: DeltaId
  , deltaBindings :: EML.EnumMap DeltaId Delta
  }

newtype DeltaImplementation a = DeltaImplementation
  { runDeltaImplementation :: State DeltaState a }
  deriving (Monad, Functor, Applicative)

eval :: EML.EnumMap DeltaId Delta -> Int -> Delta -> Vec Result
eval deltaBindings dim d0 =
  let ev store = \case
        Zero -> (V.replicate dim 0, store)
        OneHot i -> (V.replicate dim 0 V.// [(i, 1)], store)  -- dt is 1
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

df :: (Vec (Dual Delta) -> DeltaImplementation (Dual Delta))
   -> Vec Float
   -> (Vec Result, Float)
df f deltaInput =
  let dx :: Vec (Dual Delta)
      dx = V.imap (\i xi -> D xi (OneHot i)) deltaInput
      initialState = DeltaState
        { deltaCounter = DeltaId 0
        , deltaBindings = EML.empty
        }
      (D value d, st) = runState (runDeltaImplementation (f dx)) initialState
  in (eval (deltaBindings st) (V.length deltaInput) d, value)

gradDesc :: Float
         -> (Vec (Dual Delta) -> DeltaImplementation (Dual Delta))
         -> Vec Float
         -> [Vec Result]
gradDesc gamma f = iterate go where
  go :: Vec Float -> Vec Float
  go !vecInitial =
    let res = fst $ df f vecInitial
        scaled = V.map (* gamma) res
    in V.zipWith (-) vecInitial scaled

(*\) :: Dual Delta -> Dual Delta -> DeltaImplementation (Dual Delta)
(*\) (D u u') (D v v') = do
  d <- dlet $ Add (Scale v u') (Scale u v')
  return $! D (u * v) (Var d)

(+\) :: Dual Delta -> Dual Delta -> DeltaImplementation (Dual Delta)
(+\) (D u u') (D v v') = do
  d <- dlet $ Add u' v'
  return $! D (u + v) (Var d)

(-\) :: Dual Delta -> Dual Delta -> DeltaImplementation (Dual Delta)
(-\) (D u u') (D v v') = do
  d <- dlet $ Add u' (Scale (-1) v')
  return $! D (u - v) (Var d)

(**\) :: Dual Delta -> Dual Delta -> DeltaImplementation (Dual Delta)
(**\) (D u u') (D v v') = do
  d <- dlet $ Add (Scale (v * (u ** (v - 1))) u')
                  (Scale ((u ** v) * log u) v')
  return $! D (u ** v) (Var d)

scalar :: Float -> Dual Delta
scalar k = D k Zero

_scale :: Float -> Dual Delta -> DeltaImplementation (Dual Delta)
_scale k (D u u') = do
  d <- dlet $ Scale k u'
  return $! D (k * u) (Var d)

tanhAct :: Dual Delta -> DeltaImplementation (Dual Delta)
tanhAct (D u u') = do
  let y = tanh u
  d <- dlet $ Scale (1 - y * y) u'
  return $! D y (Var d)

reluAct :: Dual Delta -> DeltaImplementation (Dual Delta)
reluAct (D u u') = do
  d <- dlet $ Scale (if u > 0 then 1 else 0) u'
  return $! D (max 0 u) (Var d)













-- higher order types of vars
-- recursion and recursive types
-- fusion (eliminating spurious lets?) and checkpointing (limiting space usage?)
