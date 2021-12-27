{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module AD where

import Prelude

import           Control.Monad.Trans.State.Strict
import qualified Data.EnumMap.Lazy as EML
import           Data.List (foldl')
import           Data.Maybe (fromMaybe)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed

type Result = Float

data Dual d = D Float d

type Vec a = Data.Vector.Unboxed.Vector a

type VecDualDelta = Data.Vector.Vector (Dual Delta)

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
  , deltaBindings :: [(DeltaId, Delta)]
  }

newtype DeltaImplementation a = DeltaImplementation
  { runDeltaImplementation :: State DeltaState a }
  deriving (Monad, Functor, Applicative)

type Store = EML.EnumMap DeltaId Result

eval :: Float -> Store -> Delta -> Store
eval scale store = \case
  Zero -> store
  Scale k d -> eval (k * scale) store d
  Add d1 d2 -> eval scale (eval scale store d1) d2
  Var i -> addDelta i scale store

addDelta :: DeltaId -> Float -> Store -> Store
addDelta i scale =
  let alt mr = Just $ fromMaybe 0 mr + scale
  in EML.alter alt i

dlet :: Delta -> DeltaImplementation DeltaId
dlet v = DeltaImplementation $ do
  i <- succ <$> gets deltaCounter
  modify $ \s ->
    s { deltaCounter = i
      , deltaBindings = (i, v) : deltaBindings s
      }
  return i

df :: (VecDualDelta -> DeltaImplementation (Dual Delta))
   -> Vec Float
   -> (Vec Result, Float)
df f deltaInput =
  let dualizeInput i xi = D xi (Var $ DeltaId i)
      dx :: VecDualDelta
      dx = V.fromList $ zipWith dualizeInput [0 ..] (V.toList deltaInput)
      dim = V.length deltaInput
      initialState = DeltaState
        { deltaCounter = DeltaId dim
        , deltaBindings = []
        }
      (D value d, st) = runState (runDeltaImplementation (f dx)) initialState
      initialStore = eval 1 EML.empty d  -- dt is 1
      evalUnlessZero :: Store -> (DeltaId, Delta) -> Store
      evalUnlessZero store (i, d2) =
        let scale = EML.findWithDefault 0 i store
        in if scale == 0 then store else eval scale (EML.delete i store) d2
      finalStore = foldl' evalUnlessZero initialStore (deltaBindings st)
      rFromStore :: Int -> Result
      rFromStore i = fromMaybe 0 $ EML.lookup (DeltaId i) finalStore
  in (V.generate dim rFromStore, value)

gradDesc :: Float
         -> (VecDualDelta -> DeltaImplementation (Dual Delta))
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
-- selective fusion of delta (for individual subfunctions: pre-computing,
--   inlining results and simplifying delta-expressions; the usual inlining
--   considerations apply)
-- checkpointing (limiting space usage?)
