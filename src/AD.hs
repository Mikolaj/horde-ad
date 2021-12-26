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
  go vecInitial =
    let res = fst $ df f vecInitial
        scaled = V.map (* gamma) res
    in V.zipWith (-) vecInitial scaled

gradDescShow :: Float
             -> (Vec (Dual Delta) -> DeltaImplementation (Dual Delta))
             -> Vec Float
             -> Int
             -> (Vec Result, Float)
gradDescShow gamma f initVec n =
  let res = gradDesc gamma f initVec !! n
  in (res, snd $ df f res)

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

fX :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fX vec = do
  let x = vec V.! 0
  return x

fX1Y :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fX1Y vec = do
  let x = vec V.! 0
      y = vec V.! 1
  x1 <- x +\ scalar 1
  x1 *\ y

fXXY :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fXXY vec = do
  let x = vec V.! 0
      y = vec V.! 1
  xy <- x *\ y
  x *\ xy

fXYplusZ :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fXYplusZ vec = do
  let x = vec V.! 0
      y = vec V.! 1
      z = vec V.! 2
  xy <- x *\ y
  xy +\ z

fXtoY :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fXtoY vec = do
  let x = vec V.! 0
      y = vec V.! 1
  x **\ y

freluX :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
freluX vec = do
  let x = vec V.! 0
  reluAct x

fquad :: Vec (Dual Delta) -> DeltaImplementation (Dual Delta)
fquad vec = do
  let x = vec V.! 0
      y = vec V.! 1
  x2 <- x *\ x
  y2 <- y *\ y
  tmp <- x2 +\ y2
  tmp +\ scalar 5

scaleAddWithBias :: Dual Delta -> Dual Delta -> Int -> Vec (Dual Delta)
                 -> DeltaImplementation (Dual Delta)
scaleAddWithBias x y ixWeight vec = do
  let wx = vec V.! ixWeight
      wy = vec V.! (ixWeight + 1)
      bias = vec V.! (ixWeight + 2)
  sx <- x *\ wx
  sy <- y *\ wy
  sxy <- sx +\ sy
  sxy +\ bias

neuron :: (Dual Delta -> DeltaImplementation (Dual Delta))
       -> Dual Delta -> Dual Delta -> Int -> Vec (Dual Delta)
       -> DeltaImplementation (Dual Delta)
neuron factivation x y ixWeight vec = do
  sc <- scaleAddWithBias x y ixWeight vec
  factivation sc

nnXor :: (Dual Delta -> DeltaImplementation (Dual Delta))
      -> Dual Delta -> Dual Delta -> Vec (Dual Delta)
      -> DeltaImplementation (Dual Delta)
nnXor factivation x y vec = do
  n1 <- neuron factivation x y 0 vec
  n2 <- neuron factivation x y 3 vec
  neuron factivation n1 n2 6 vec

lossXor :: Dual Delta -> Dual Delta -> DeltaImplementation (Dual Delta)
lossXor u v = do
  diff <- u -\ v
  diff *\ diff

nnLoss :: (Dual Delta -> DeltaImplementation (Dual Delta))
      -> Float -> Float -> Float -> Vec (Dual Delta)
      -> DeltaImplementation (Dual Delta)
nnLoss factivation x y res vec = do
  r <- nnXor factivation (scalar x) (scalar y) vec
  lossXor r (scalar res)

setLoss :: (Dual Delta -> DeltaImplementation (Dual Delta))
        -> Vec (Dual Delta)
        -> DeltaImplementation (Dual Delta)
setLoss factivation vec = do
  n1 <- nnLoss factivation 0 0 0 vec
  n2 <- nnLoss factivation 0 1 1 vec
  n3 <- nnLoss factivation 1 0 1 vec
  n4 <- nnLoss factivation 1 1 0 vec
  n12 <- n1 +\ n2
  n34 <- n3 +\ n4
  n12 +\ n34

initWeights, initWeights2 :: Vec Float
initWeights = let w = [0.37, 0.28, 0.19] in V.fromList $ w ++ w ++ w
initWeights2 = let w = [-1.37, 2.28, -0.19] in V.fromList $ w ++ w ++ w

result :: [(Vec Result, Float)]
result =
  map (\(f, v) -> df f v)
    [ (fX, V.fromList [99])  -- 1
    , (fX1Y, V.fromList [3, 2])  -- 2, 4
    , (fXXY, V.fromList [3, 2])  -- 12, 9
    , (fXYplusZ, V.fromList [1, 2, 3])  -- 2, 1, 1
    , (fXtoY, V.fromList [0.00000000000001, 2])  -- ~0, ~0
    , (fXtoY, V.fromList [1, 2])  -- 2, 0
    , (freluX, V.fromList [-1])  -- 0
    , (freluX, V.fromList [0])  -- ? (0)
    , (freluX, V.fromList [0.0001])  -- 1
    , (freluX, V.fromList [99])  -- 1
    , (fquad, V.fromList [2, 3])  -- 4, 6
    ]
  ++ [ gradDescShow 0.1 fquad (V.fromList [2, 3]) 30
         -- 2.47588e-3, 3.7138206e-3
     , gradDescShow 0.01 fquad (V.fromList [2, 3]) 30
     , gradDescShow 0.01 fquad (V.fromList [2, 3]) 300
     , gradDescShow 0.01 fquad (V.fromList [2, 3]) 300000
         -- 3.5e-44, 3.5e-44
     , gradDescShow 0.1 (setLoss tanhAct) initWeights 500  -- 1.205092e-2
     , gradDescShow 0.1 (setLoss tanhAct) initWeights 5000  -- 1.8422995e-4
     , gradDescShow 0.01 (setLoss tanhAct) initWeights2 5000
     , gradDescShow 0.01 (setLoss reluAct) initWeights 5000  -- no cookie
     , gradDescShow 0.1 (setLoss reluAct) initWeights2 5000  -- no cookie
     ]

















-- higher order types of vars
-- recursion and recursive types
-- fusion (eliminating spurious lets?) and checkpointing (limiting space usage?)

























-- THE END
