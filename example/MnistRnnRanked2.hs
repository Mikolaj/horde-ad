{-# OPTIONS_GHC -Wno-missing-export-lists #-}
-- | Ranked tensor-based implementation of Recurrent Neural Network
-- for classification of MNIST digits. Sports 2 hidden layers.
module MnistRnnRanked2 where

import Prelude hiding (foldl')

import Data.Kind (Type)
import Data.List (foldl')
import Data.Vector.Generic qualified as V
import Data.Vector.Storable (Vector)
import GHC.TypeLits (KnownNat, Nat, type (+))

import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape

import HordeAd
import MnistData

-- | The differentiable type of all trainable parameters of this nn.
-- Shaped version, statically checking all dimension widths.
type ADRnnMnistParametersShaped (target :: Target) width r =
  ( LayerWeigthsRNNShaped target SizeMnistHeight width r
  , LayerWeigthsRNNShaped target width width r
  , ( target (TKS '[SizeMnistLabel, width] r)
    , target (TKS '[SizeMnistLabel] r) ) )

type LayerWeigthsRNNShaped :: Target -> Nat -> Nat -> Type -> Type
type LayerWeigthsRNNShaped target in_width out_width r =
  ( target (TKS '[out_width, in_width] r)   -- input weight
  , target (TKS '[out_width, out_width] r)  -- state weight
  , target (TKS '[out_width] r) )           -- bias

-- | The differentiable type of all trainable parameters of this nn.
type ADRnnMnistParameters target r =
  ( LayerWeigthsRNN target r
  , LayerWeigthsRNN target r
  , ( target (TKR 2 r)
    , target (TKR 1 r) ) )

type LayerWeigthsRNN (target :: Target) r =
  ( target (TKR 2 r)
  , target (TKR 2 r)
  , target (TKR 1 r) )

zeroStateR
  :: (BaseTensor target, GoodScalar r)
  => IShR n -> (target (TKR n r)  -- state
                    -> a)
  -> a
zeroStateR sh f = f (rrepl sh 0)

unrollLastR :: forall target state c w r n.
               (BaseTensor target, GoodScalar r, KnownNat n)
            => (state -> target (TKR n r) -> w -> (c, state))
            -> (state -> target (TKR (1 + n) r) -> w -> (c, state))
unrollLastR f s0 xs w =
  let g :: (c, state) -> target (TKR n r) -> (c, state)
      g (_, !s) x = f s x w
  in foldl' g (undefined, s0) (runravelToList xs)

rnnMnistLayerR
  :: (ADReady target, GoodScalar r, Differentiable r)
  => target (TKR 2 r)  -- in state, [out_width, batch_size]
  -> target (TKR 2 r)  -- input, [in_width, batch_size]
  -> LayerWeigthsRNN target r  -- in_width out_width
  -> target (TKR 2 r)  -- output state, [out_width, batch_size]
rnnMnistLayerR s x (wX, wS, b) = case rshape s of
  _out_width :$: batch_size :$: ZSR ->
    let y = wX `rmatmul2m` x + wS `rmatmul2m` s
            + rtr (rreplicate batch_size b)
    in tanh y

rnnMnistTwoR
  :: (ADReady target, GoodScalar r, Differentiable r)
  => target (TKR 2 r)  -- initial state, [2 * out_width, batch_size]
  -> PrimalOf target (TKR 2 r)  -- [sizeMnistHeight, batch_size]
  -> ( LayerWeigthsRNN target r  -- sizeMnistHeight out_width
     , LayerWeigthsRNN target r )  -- out_width out_width
  -> ( target (TKR 2 r)  -- [out_width, batch_size]
     , target (TKR 2 r) )  -- final state, [2 * out_width, batch_size]
rnnMnistTwoR s' x ((wX, wS, b), (wX2, wS2, b2)) = case rshape s' of
  out_width_x_2 :$: _batch_size :$: ZSR ->
    let out_width = out_width_x_2 `div` 2
        s3 = tlet s' $ \s ->
          let s1 = rslice 0 out_width s
              s2 = rslice out_width out_width s
              vec1 = rnnMnistLayerR s1 (rfromPrimal x) (wX, wS, b)
              vec2 = rnnMnistLayerR s2 vec1 (wX2, wS2, b2)
          in rappend vec1 vec2
    in (rslice out_width out_width s3, s3)

rnnMnistZeroR
  :: (ADReady target, GoodScalar r, Differentiable r)
  => Int
  -> PrimalOf target (TKR 3 r)  -- [sizeMnistWidth, sizeMnistHeight, batch_size]
  -> ADRnnMnistParameters target r  -- sizeMnistHeight out_width
  -> target (TKR 2 r)  -- [SizeMnistLabel, batch_size]
rnnMnistZeroR batch_size xs
              ((wX, wS, b), (wX2, wS2, b2), (w3, b3)) = case rshape b of
  out_width :$: ZSR ->
    let sh = 2 * out_width :$: batch_size :$: ZSR
        (out, _s) = zeroStateR sh (unrollLastR rnnMnistTwoR) xs
                                  ((wX, wS, b), (wX2, wS2, b2))
    in w3 `rmatmul2m` out + rtr (rreplicate batch_size b3)

-- TODO: This manual vectorization performs differently than the automatic
-- vectorization, even though it should perform the same. Also,
-- fewer tsmatmul2 get recognized and pretty-printed in tests,
-- even though the recognizing should be exhaustive as is. Investigate.
--
-- The answer is the reverse of this rule (and similar)
--   transpose perm (Ast.AstReplicate snat1@SNat _ (Ast.AstReplicate snat2 (STKS sh2 x) u))
--    | SNat' @1 `PCons` SNat' @0 `PCons` PNil <- perm ->
--      Ast.AstReplicate snat2 (STKS (snat1 :$$ sh2) x)
--                       (Ast.AstReplicate snat1 (STKS sh2 x) u)
-- which permits creating a transpose our of nested replicates
-- and so proves more matmuls can be recognized than we do currently.
-- Sadly, this is very messy, we need to check if there are >=2 or >=3 nested
-- replicates, depending on which permutation we require, etc.
-- OTOH, recognizing matmuls for nested replicates is probably not important.
rmatmul2m :: (BaseTensor target, GoodScalar r)
          => target (TKR 2 r) -> target (TKR 2 r) -> target (TKR 2 r)
rmatmul2m m1 m2 = case rshape m2 of
  _ :$: width2 :$: ZSR ->
    rsum (rtranspose [2,1,0] (rreplicate width2 m1)
          * rtranspose [1,0] (rreplicate (rwidth m1) m2))

rnnMnistLossFusedR
  :: (ADReady target, ADReady (PrimalOf target), GoodScalar r, Differentiable r)
  => Int
  -> (PrimalOf target (TKR 3 r), PrimalOf target (TKR 2 r))  -- batch_size
  -> ADRnnMnistParameters target r  -- SizeMnistHeight out_width
  -> target (TKScalar r)
rnnMnistLossFusedR batch_size (glyphR, labelR) adparameters =
  let xs = rtranspose [2, 1, 0] glyphR
      result = rnnMnistZeroR batch_size xs adparameters
      targets = rtr labelR
      loss = lossSoftMaxCrossEntropyR targets result
  in kfromPrimal (recip $ kconcrete $ fromIntegral batch_size) * loss

rnnMnistZeroR2
  :: (ADReady target, GoodScalar r, Differentiable r)
  => Int
  -> PrimalOf target (TKR 3 r)  -- [sizeMnistWidth, sizeMnistHeight, batch_size]
  -> ADRnnMnistParameters target r  -- sizeMnistHeight out_width
  -> target (TKR 2 r)  -- [SizeMnistLabel, batch_size]
rnnMnistZeroR2 batch_size xs
              ((wX, wS, b), (wX2, wS2, b2), (w3, b3)) = case rshape b of
  out_width :$: ZSR ->
    let sh = 2 * out_width :$: batch_size :$: ZSR
        (out, _s) = zeroStateR sh (unrollLastR rnnMnistTwoR) xs
                                  ((wX, wS, b), (wX2, wS2, b2))
    in w3 `rmatmul2m` out + rtr (rreplicate batch_size b3)

rnnMnistTestR
  :: forall target r.
     (target ~ Concrete, GoodScalar r, Differentiable r)
  => Int
  -> MnistDataBatchR r  -- batch_size
  -> ADRnnMnistParameters target r
  -> r
rnnMnistTestR 0 _ _ = 0
rnnMnistTestR batch_size (glyphR, labelR) testParams =
  let input :: target (TKR 3 r)
      input = rconcrete $ Nested.rtranspose [2, 1, 0] glyphR
      outputR :: Concrete (TKR 2 r)
      outputR =
        let nn :: ADRnnMnistParameters target r  -- SizeMnistHeight out_width
               -> target (TKR 2 r)  -- [SizeMnistLabel, batch_size]
            nn = rnnMnistZeroR2 batch_size input
        in nn testParams
      outputs = map rtoVector $ runravelToList
                $ rtranspose [1, 0] outputR
      labels = map rtoVector
               $ runravelToList @_ @(TKScalar r)
               $ rconcrete labelR
      matchesLabels :: Vector r -> Vector r -> Int
      matchesLabels output label | V.maxIndex output == V.maxIndex label = 1
                                 | otherwise = 0
  in fromIntegral (sum (zipWith matchesLabels outputs labels))
     / fromIntegral batch_size
