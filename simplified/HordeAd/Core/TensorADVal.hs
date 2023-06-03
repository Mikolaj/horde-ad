{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | 'Tensor' class instances for dual number. The dual numbers are built
-- either from concrete floats or from 'Ast' term.
module HordeAd.Core.TensorADVal
  ( ADValClown
  ) where

import Prelude hiding ((<*))

import qualified Data.Array.RankedS as OR
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Product
import           Data.Boolean
import           Data.List (foldl1')
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))

import HordeAd.Core.Adaptor
import HordeAd.Core.Ast
import HordeAd.Core.Delta
import HordeAd.Core.DualClass
import HordeAd.Core.DualNumber
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass

type instance BooleanOf (ADVal f r z) = BooleanOf (f r z)

-- Boolean and numeric instances are easy to define for ADVal f r z
-- and then Clown, Flip and other instances are auto-derived on top of them.
-- OTOH, AdaptableDomains and other such instances are best defined
-- directly for Clown and others applied to ADVal.
instance (EqB (f r z), IsPrimal f r z) => EqB (ADVal f r z) where
  D l1 u _ ==* D l2 v _ = letWrapPrimal l1 u ==* letWrapPrimal l2 v
  D l1 u _ /=* D l2 v _ = letWrapPrimal l1 u /=* letWrapPrimal l2 v

instance (OrdB (f r z), IsPrimal f r z) => OrdB (ADVal f r z) where
  D l1 u _ <* D l2 v _ = letWrapPrimal l1 u <* letWrapPrimal l2 v
  D l1 u _ <=* D l2 v _ = letWrapPrimal l1 u <=* letWrapPrimal l2 v
  D l1 u _ >* D l2 v _ = letWrapPrimal l1 u >* letWrapPrimal l2 v
  D l1 u _ >=* D l2 v _ = letWrapPrimal l1 u >=* letWrapPrimal l2 v

instance IfB (ADVal (Flip OR.Array) r n) where
  ifB b v w = if b then v else w

-- This requires the Tensor instance, hence the definitions must be here.
instance (KnownNat n, GoodScalar r)
         => IfB (ADVal AstRanked r n) where
  ifB b v w = indexZ (fromList [v, w]) (singletonIndex $ ifB b 0 1)

-- TODO: speed up by using tindex0R and dIndex0 if the codomain is 0
-- and dD (u `tindex1R` ix) (dIndex1 u' ix (tlengthR u)) if only outermost
-- dimension affected.
--
-- First index is for outermost dimension; empty index means identity,
-- index ouf of bounds produces zero (but beware of vectorization).
indexZ :: forall ranked m n r.
          ( Tensor ranked, HasRanks ranked, IsPrimal ranked r n
          , KnownNat m, KnownNat n, GoodScalar r )
       => ADVal ranked r (m + n) -> IndexOf (ranked r 0) m
       -> ADVal ranked r n
indexZ (D l u u') ix = dD l (tindex u ix) (dIndexR u' ix (tshape u))

fromList :: ( Tensor ranked, HasRanks ranked, IsPrimal ranked r (1 + n)
            , KnownNat n, GoodScalar r )
         => [ADVal ranked r n]
         -> ADVal ranked r (1 + n)
fromList lu =
  -- TODO: if lu is empty, crash if n =\ 0 or use List.NonEmpty.
  dD (flattenADShare $ map ((\(D l _ _) -> l)) lu)
     (tfromList $ map (\(D _ u _) -> u) lu)
     (dFromListR $ map (\(D _ _ u') -> u') lu)

type ADValClown dynamic = Flip (ADVal (Clown dynamic)) '()

instance ( KnownNat n, GoodScalar r, dynamic ~ DynamicOf ranked
         , ConvertTensor ranked shaped, HasConversions ranked shaped )
         => AdaptableDomains (ADValClown dynamic)
                             (ADVal ranked r n) where
  type Underlying (ADVal ranked r n) = r
  type Value (ADVal ranked r n) = Flip OR.Array r n  -- !!! not ranked
  toDomains = undefined
  fromDomains _aInit inputs = case V.uncons inputs of
    Just (a, rest) -> Just (dToR (runFlip a), rest)
    Nothing -> Nothing

instance ( GoodScalar r, dynamic ~ DynamicOf shaped
         , ConvertTensor ranked shaped, HasConversions ranked shaped )
         => AdaptableDomains (ADValClown dynamic)
                             (ADVal shaped r sh) where
  type Underlying (ADVal shaped r sh) = r
  type Value (ADVal shaped r sh) = Flip OS.Array r sh  -- !!! not shaped
  toDomains = undefined
  fromDomains = undefined

dToR :: forall ranked shaped n r.
        ( ConvertTensor ranked shaped, HasConversions ranked shaped
        , KnownNat n, GoodScalar r )
      => ADVal (Clown (DynamicOf ranked)) r '() -> ADVal ranked r n
dToR (D l u u') = dDnotShared l (tfromD $ runClown u) (dDToR u')

rToD :: ( ConvertTensor ranked shaped, HasConversions ranked shaped
        , KnownNat n, GoodScalar r )
      => ADVal ranked r n -> ADVal (Clown (DynamicOf ranked)) r '()
rToD (D l u u') = dDnotShared l (Clown $ dfromR u) (dRToD u')

class (forall r15 y. (KnownNat y, GoodScalar r15) => c (ranked r15 y))
      => CRanked ranked c where
instance (forall r15 y. (KnownNat y, GoodScalar r15) => c (ranked r15 y))
         => CRanked ranked c where

class (forall r15 y. (KnownNat y, GoodScalar r15) => c ranked r15 y)
      => CRankedIP ranked c where
instance (forall r15 y. (KnownNat y, GoodScalar r15) => c ranked r15 y)
         => CRankedIP ranked c where

type instance IntOf (ADVal f r n) = IntOf (f r n)

type instance PrimalOf (ADVal f) = f

-- Morally:
-- type instance DualOf (Tannen ADVal f) = Product (Clown ADShare)
--                                                 (\r k -> Dual (f r k))

type instance DualOf (ADVal (Flip OR.Array)) =
  Product (Clown ADShare)
          (DeltaR (Flip OR.Array) (Flip OS.Array))

type instance DualOf (ADVal AstRanked) =
  Product (Clown ADShare)
          (DeltaR AstRanked AstShaped)

type instance DualOf (ADVal (Flip OS.Array)) =
  Product (Clown ADShare)
          (DeltaS (Flip OR.Array) (Flip OS.Array))

type instance DualOf (ADVal AstShaped) =
  Product (Clown ADShare)
          (DeltaS AstRanked AstShaped)

type instance DynamicOf (ADVal f) = ADValClown (DynamicOf f)

-- Note that these instances don't do vectorization. To enable it,
-- use the Ast instance and only then interpret in ADVal.
-- In any case, only the Ast instantiation of this instance
-- is used in the codebase, in particular, to satisfy the constraints
-- needed for the interpretation of Ast in ADVal.
-- The ADVal Double and ADVal Float instantiations are only used
-- in tests. None others are used anywhere.
instance ( DualOf (ADVal ranked)
           ~ Product (Clown ADShare) (DeltaR ranked shaped)
         , Dual ranked ~ DeltaR ranked shaped
         , DeltaR ranked shaped ~ Dual ranked
         , CRankedIP ranked IsPrimal
         , CRanked ranked Show
         , HasRanks ranked
         , Tensor ranked )
         => Tensor (ADVal ranked) where
  tlet (D l u u') f =
    let (l2, var2) = recordSharingPrimal u l
    in f (D l2 var2 u')
      -- TODO: What about sharing u'?

  tshape (D _ u _) = tshape u
  -- This is very slow, but is fortunately not needed:
  -- tshape (D l u _) = tshape (tletWrap l u)
  tminIndex0 (D l u _) = tminIndex0 (tletWrap l u)
  tmaxIndex0 (D l u _) = tmaxIndex0 (tletWrap l u)
  tfloor (D l u _) = tfloor (tletWrap l u)

  tindex v ix = indexZ v ix
  tsum = sum'
   where
    sum' (D l u u') = dD l (tsum u) (dSumR (tlength u) u')
  tsum0 = sum0
   where
    sum0 (D l u u') = dD l (tsum0 u) (dSum0R (tshape u) u')
  tdot0 = \u v -> dot0 u v
   where
    dot0 (D l1 ue u') (D l2 ve v') =
      -- The bangs below are neccessary for GHC 9.2.7 test results to match 9.4.
      let !(!l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
          !(!l4, v) = recordSharingPrimal ve l3
      in dD l4 (tdot0 u v) (dAdd (dDot0R v u') (dDot0R u v'))
  tfromIndex0 = \ix -> dDnotShared emptyADShare (tfromIndex0 ix) dZero
  tscatter = \sh t f -> scatterNClosure sh t f
   where
    scatterNClosure sh (D l u u') f =
      dD l (tscatter sh u f) (dScatterR sh u' f (tshape u))

  tfromList = fromList
  tfromVector = fromVector
   where
    fromVector lu =
      dD (flattenADShare $ map ((\(D l _ _) -> l)) $ V.toList lu)
         (tfromVector $ V.map (\(D _ u _) -> u) lu)
         (dFromVectorR $ V.map (\(D _ _ u') -> u') lu)
  treplicate = \k -> replicate' k
   where
    replicate' k (D l u u') = dD l (treplicate k u) (dReplicateR k u')
  tappend = \u v -> append u v
   where
    append (D l1 u u') (D l2 v v') =
      dD (l1 `mergeADShare` l2) (tappend u v) (dAppendR u' (tlength u) v')
  tslice = \i k -> slice i k
   where
    slice i k (D l u u') = dD l (tslice i k u) (dSliceR i k u' (tlength u))
  treverse = reverse'
   where
    reverse' (D l u u') = dD l (treverse u) (dReverseR u')
  ttranspose = \perm -> transpose perm
   where
    transpose perm (D l u u') = dD l (ttranspose perm u) (dTransposeR perm u')
  treshape :: forall n m r. (GoodScalar r, KnownNat n, KnownNat m)
           => ShapeInt m -> ADVal ranked r n -> ADVal ranked r m
  treshape = \sh -> reshape sh
   where
    reshape sh t@(D l u u') = case sameNat (Proxy @m) (Proxy @n) of
      Just Refl | sh == tshape u -> t
      _ -> dD l (treshape sh u) (dReshapeR (tshape u) sh u')
  tbuild1 = \k f -> build1 k f
   where
    build1 k f = fromList $ map (f . fromIntegral) [0 .. k - 1]
                   -- element-wise (POPL) version
  tgather = \sh t f -> gatherNClosure sh t f
   where
    gatherNClosure sh (D l u u') f =
      dD l (tgather sh u f) (dGatherR sh u' f (tshape u))

  tsumOfList lu =
    dD (flattenADShare $ map (\(D l _ _) -> l) lu)
       (tsumOfList $ map (\(D _ u _) -> u) lu)
       (foldl1' dAdd $ map (\(D _ _ u') -> u') lu)
  tmult (D l1 ue ZeroR) (D l2 ve v') =
    let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        (l4, v) = recordSharingPrimal ve l3
    in dD l4 (u * v) (dScale u v')
  tmult (D l1 ue u') (D l2 ve ZeroR) =
    let (l3, u) = recordSharingPrimal ue $ l1 `mergeADShare` l2
        (l4, v) = recordSharingPrimal ve l3
    in dD l4 (u * v) (dScale v u')
  tmult d e = d * e
  tconst t = dDnotShared emptyADShare (tconstBare t) dZero

  tconstant t = dDnotShared emptyADShare t dZero
  tprimalPart (D l u _) = tletWrap l u
  tdualPart (D l _ u') = Pair (Clown l) u'
  tD ast (Pair (Clown l) delta) = dD l ast delta
  tScale ast (Pair l delta) = Pair l (dScale ast delta)

instance (HasConversions ranked shaped, ConvertTensor ranked shaped)
         => ConvertTensor (ADVal ranked)
                          (ADVal shaped) where
  tfromD = dToR . runFlip
  tfromS = sToR
   where
    sToR (D l u u') = dDnotShared l (tfromS @ranked @shaped u) (dSToR u')
  dfromR = Flip . rToD
  dfromS = Flip . sToD
   where
    sToD (D l u u') = dDnotShared l (Clown $ dfromS @ranked @shaped u)
                                    (dSToD u')
  sfromD = dToS . runFlip
   where
    dToS (D l u u') = dDnotShared l (sfromD @ranked @shaped (runClown u))
                                    (dDToS u')
  sfromR = rToS
   where
    rToS (D l u u') = dDnotShared l (sfromR @ranked @shaped u) (dRToS u')
  ddummy = undefined
  disDummy = undefined
  daddR = undefined
  dshape = undefined


-- Strangely, this variant slows down simplifiedOnlyTest 3 times. Perhaps
-- that's because k is very low and the f functions are simple enough.
--
-- This does not work any more, because the dual numbers produced by f
-- are not simplified to transform ADShare, which breaks some pipelines.
-- Even if they were, the sharing would most likely be missing
-- or redundant or both.
--
-- This may be a problem with gatherNClosure, too, as soon as we have
-- integer sharing and it's shared in the whole transpose result.
_build1Closure
  :: ( Tensor ranked, HasRanks ranked, KnownNat n, GoodScalar r
     , IsPrimal ranked r (1 + n) )
  => Int -> (IntOf (ranked r 0) -> ADVal ranked r n)
  -> ADVal ranked r (1 + n)
_build1Closure k f =  -- stores closures on tape
  let g i = let D _ u _ = f i in u
      h i = let D _ _ u' = f i in u'
  in dD emptyADShare (tbuild1 k g) (dBuildR k h)
