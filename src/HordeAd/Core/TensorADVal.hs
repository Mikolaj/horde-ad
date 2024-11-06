{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module HordeAd.Core.TensorADVal
  ( ) where

import Prelude hiding (foldl')

import Data.Vector.Generic qualified as V
import GHC.TypeLits (KnownNat)

import HordeAd.Core.Adaptor
import HordeAd.Core.Delta
import HordeAd.Core.DualNumber
import HordeAd.Core.HVector
import HordeAd.Core.TensorClass
import HordeAd.Core.Types

instance ( shaped ~ ShapedOf ranked, ADReadyNoLet ranked, ShareTensor ranked
         , ShareTensor (PrimalOf ranked) )
         => LetTensor (ADVal ranked) where
  dlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (ADVal ranked) x
       -> (RepDeep (ADVal ranked) x -> Rep (ADVal ranked) z)
       -> Rep (ADVal ranked) z
  dlet a f = case stensorKind @x of
    STKScalar{} -> blet a f
    STKR STKScalar{} _ -> blet a f
    STKS STKScalar{} _ -> blet a f
    STKX STKScalar{} _ -> blet a f
    stk@STKProduct{} -> blet a $ \ !uShared -> f (repDeepDuplicable stk uShared)
    STKUntyped{} ->
      let (!u, !u') = unADValHVector $ unHVectorPseudoTensor a
          !var2 = dunHVector $ unHVectorPseudoTensor $ tshare @_ @TKUntyped
                  $ HVectorPseudoTensor $ dmkHVector u
      in f (aDValHVector var2 u')
    _ -> error "TODO"
  tlet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (ADVal ranked) x
       -> (RepShallow (ADVal ranked) x -> Rep (ADVal ranked) z)
       -> Rep (ADVal ranked) z
  tlet a f = case stensorKind @x of
    STKScalar{} -> blet a f
    STKR STKScalar{} SNat -> blet a f
    STKS STKScalar{} sh -> withKnownShS sh $ blet a f
    STKX STKScalar{} sh -> withKnownShX sh $ blet a f
    STKProduct{} -> blet a f
    STKUntyped{} ->
      let (!u, !u') = unADValHVector $ unHVectorPseudoTensor a
          !var2 = dunHVector $ unHVectorPseudoTensor $ tshare @_ @TKUntyped
                  $ HVectorPseudoTensor $ dmkHVector u
            -- dunHVector is fine, because its argument is shared
            -- (and even without that, it comes from an explicit HVector)
            -- and tshare is needed due to f possibly using the argument many times
            -- and while the Haskell computation would be performed only once,
            -- a term could get duplicated and then interpreted many times.
            -- Normally it would be the reponsibility of f to share its argument
            -- but this is a let expression, so here we ensure what is passed
            -- to f is properly shared.
      in f (aDValHVector var2 u')
    _ -> error "TODO"
  blet :: forall x z. (TensorKind x, TensorKind z)
       => Rep (ADVal ranked) x
       -> (Rep (ADVal ranked) x -> Rep (ADVal ranked) z)
       -> Rep (ADVal ranked) z
  blet a f = case stensorKind @x of
    STKScalar{} -> blet (unRepScalar a) (f . RepScalar)
    STKR STKScalar{} SNat ->
      let (D u u') = a
          !var2 = tshare u
      in f (dDnotShared var2 u')
    STKS STKScalar{} sh -> withKnownShS sh $
      let (D u u') = a
          !var2 = tshare u
      in f (dDnotShared var2 u')
    STKX STKScalar{} sh -> withKnownShX sh $
      let (D u u') = a
          !var2 = tshare u
      in f (dDnotShared var2 u')
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      -- Sharing is preserved despite `a` being repeated, because
      -- each repetition concerns a disjoint portion of `a` and so the whole `a`
      -- is computed only once.
      blet (fst a) $ \ !a1 ->
        blet (snd a) $ \ !a2 -> f (a1, a2)
    STKUntyped{} ->
      let (!u, !u') = unADValHVector $ unHVectorPseudoTensor a
          !var2 = dunHVector $ unHVectorPseudoTensor $ tshare @_ @TKUntyped
                  $ HVectorPseudoTensor $ dmkHVector u
      in f (HVectorPseudoTensor $ aDValHVector var2 u')
    _ -> error "TODO"

  tconstant stk t = case stk of
    STKScalar _ -> RepScalar $ rconstant $ unRepScalar t
    STKR STKScalar{} SNat -> rconstant t
    STKS STKScalar{} sh -> withKnownShS sh $ sconstant t
    STKX STKScalar{} sh -> withKnownShX sh $ xconstant t
    STKProduct stk1 stk2 | Dict <- lemTensorKindOfS stk1
                         , Dict <- lemTensorKindOfS stk2 ->
      let (t1, t2) = tunpair t
          !c1 = tconstant stk1 t1
          !c2 = tconstant stk2 t2
      in (c1, c2)
    STKUntyped ->
      let fd :: DynamicTensor ranked -> DynamicTensor (ADVal ranked)
          fd = mapDynamic rconstant sconstant
      in HVectorPseudoTensor $ V.map fd $ tunvector t
    _ -> error "TODO"

instance ( shaped ~ ShapedOf ranked, ADReadyNoLet ranked
         , ShareTensor ranked
         , ShareTensor (PrimalOf ranked) )
         => ProductTensor (ADVal ranked) where

unADValHVector
  :: HVector (ADVal f)
  -> (HVector f, HVector (DeltaR f))
unADValHVector = undefined

aDValHVector = undefined
