{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The grammar of delta expressions.
--
-- A delta expression can be viewed as a concise representation
-- of a linear map (which is the derivative of the objective function)
-- and its evaluation on a given argument (in module "HordeAd.Core.DeltaEval")
-- as an adjoint (in the algebraic sense) of the linear map
-- applied to that argument. Since linear maps can be represented
-- as matrices, this operation corresponds to a transposition
-- of the matrix. However, the matrix is not constructed,
-- but is represented and transposed preserving the sparsity
-- of the representation.
--
-- The \'sparsity\' is less obvious when a delta expression
-- contains big concrete tensors, e.g., via the `DeltaScale` constructor.
-- However, via 'DeltaReplicate' and other constructors, the tensors
-- can be enlarged much beyond what's embedded in the delta term.
-- Also, if the expression refers to unknown inputs ('DeltaInput')
-- it may denote, after evaluation, a still larger tensor.
--
-- The algebraic structure here is an extension of vector space
-- with some additional constructors. The crucial extra constructor
-- 'DeltaInput' replaces the usual one-hot access to parameters
-- with something cheaper and more uniform.
-- A lot of the remaining additional constructors is for introducing
-- and reducing dimensions of tensors and it mimics many of the operations
-- available for the primal value arrays.
module HordeAd.Core.Delta
  ( -- * Delta identifiers
    NodeId, mkNodeId, nodeIdToFTK
  , InputId, mkInputId, inputIdToFTK
    -- * The grammar of delta expressions
  , Delta(..), NestedTarget(..)
    -- * Full tensor kind derivation for delta expressions
  , ftkDelta
  ) where

import Prelude

import Control.Exception.Assert.Sugar
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Kind (Type)
import Data.Type.Equality (TestEquality (..), gcastWith, testEquality, (:~:))
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
import GHC.TypeLits (type (+), type (<=))
import Text.Show.Functions ()

import Data.Array.Nested (type (++))
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Permutation qualified as Permutation
import Data.Array.Nested.Ranked.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (snatPlus, unsafeCoerceRefl)

import HordeAd.Core.Conversion
import HordeAd.Core.Ops
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * Delta identifiers

-- | The identifiers for nodes of delta expression trees.
type role NodeId nominal nominal
data NodeId :: Target -> TK -> Type where
  NodeId :: forall target y. FullShapeTK y -> Int -> NodeId target y

-- No Eq instance to limit hacks outside this module.

instance Show (NodeId target y) where
  showsPrec d (NodeId _ n) =
    showsPrec d n  -- less verbose, more readable

instance DMap.Enum1 (NodeId target) where
  type Enum1Info (NodeId target) = FullShapeTK
  fromEnum1 (NodeId ftk n) = (n, ftk)
  toEnum1 n ftk = NodeId ftk n

instance TestEquality (NodeId target) where
  testEquality (NodeId ftk1 _) (NodeId ftk2 _) = matchingFTK ftk1 ftk2

-- | Wrap non-negative (only!) integers in the t'NodeId' newtype.
mkNodeId :: FullShapeTK y -> Int -> NodeId f y
mkNodeId ftk i = assert (i >= 0) $ NodeId ftk i

nodeIdToFTK :: NodeId f y -> FullShapeTK y
nodeIdToFTK (NodeId ftk _) = ftk

-- | The identifiers for input leaves of delta expressions.
type role InputId nominal nominal
data InputId :: Target -> TK -> Type where
  InputId :: forall target y. FullShapeTK y -> Int -> InputId target y

-- No Eq instance to limit hacks outside this module.

instance Show (InputId target y) where  -- backward compatibility
  showsPrec _ (InputId _ n) =
    showParen True
    $ showString "InputId "
      . shows n

instance DMap.Enum1 (InputId target) where
  type Enum1Info (InputId target) = FullShapeTK
  fromEnum1 (InputId ftk n) = (n, ftk)
  toEnum1 n ftk = InputId ftk n

instance TestEquality (InputId target) where
  testEquality (InputId ftk1 _) (InputId ftk2 _) = matchingFTK ftk1 ftk2

-- | Wrap non-negative (only!) integers in the t'InputId' newtype.
mkInputId :: FullShapeTK y -> Int -> InputId f y
mkInputId ftk i = assert (i >= 0) $ InputId ftk i

inputIdToFTK :: InputId f y -> FullShapeTK y
inputIdToFTK (InputId ftk _) = ftk


-- * The grammar of delta expressions

-- | The grammar of delta expressions.
--
-- The t`NodeId` identifier that appears in a @DeltaShare n d@ expression
-- is the unique identity stamp of subterm @d@, that is, there is
-- no different term @e@ such that @DeltaShare n e@ appears in any delta
-- expression term in memory during the same run of an executable.
-- The subterm identity is used to avoid evaluating shared
-- subterms repeatedly in gradient and derivative computations.
-- The identifiers also represent data dependencies among terms
-- for the purpose of gradient and derivative computation. Computation for
-- a term may depend only on data obtained from terms with lower value
-- of their node identifiers. Such data dependency determination
-- agrees with the subterm relation, but is faster than traversing
-- the term tree in order to determine the relation of terms.
--
-- When computing gradients, node identifiers are also used to index,
-- directly or indirectly, the data accumulated for each node,
-- in the form of cotangents, that is partial derivatives
-- of the objective function with respect to the position(s)
-- of the node in the whole objective function dual number term
-- (or, more precisely, with respect to the single node in the term DAG,
-- in which subterms with the same node identifier are collapsed).
-- Only the @DeltaInput@ nodes have a separate data storage.
-- The t`InputId` identifiers in the @DeltaInput@ term constructors
-- are indexes into a contiguous vector of cotangents of @DeltaInput@
-- subterms of the whole term. The value at that index is the partial
-- derivative of the objective function (represented by the whole term,
-- or more precisely by (the data flow graph of) its particular
-- evaluation from which the delta expression originates)
-- with respect to the input parameter component at that index
-- in the objective function domain.
type role Delta nominal nominal
data Delta :: Target -> Target where
  -- Sharing-related operations
  DeltaShare :: NodeId target y -> Delta target y -> Delta target y
  DeltaInput :: InputId target y -> Delta target y

  -- General operations
  DeltaPair :: forall y z target.
               Delta target y -> Delta target z
            -> Delta target (TKProduct y z)
  DeltaProject1 :: forall y z target.
                   Delta target (TKProduct y z) -> Delta target y
  DeltaProject2 :: forall y z target.
                   Delta target (TKProduct y z) -> Delta target z
  DeltaFromVector :: forall y k target.
                     SNat k -> SingletonTK y
                  -> Data.Vector.Vector (Delta target y)
                  -> Delta target (BuildTensorKind k y)
  DeltaSum :: forall y k target.
              SNat k -> SingletonTK y
           -> Delta target (BuildTensorKind k y)
           -> Delta target y
  DeltaReplicate :: forall y k target.
                    SNat k -> SingletonTK y
                 -> Delta target y
                 -> Delta target (BuildTensorKind k y)
  DeltaMapAccumL
    :: forall target k accy by ey.
       ( Show (target (BuildTensorKind k accy))
       , Show (target (BuildTensorKind k ey)) )
    => SNat k
    -> FullShapeTK by
    -> FullShapeTK ey
    -> target (BuildTensorKind k accy)
    -> target (BuildTensorKind k ey)
    -> HFun (TKProduct (ADTensorKind (TKProduct accy ey))
                       (TKProduct accy ey))
            (ADTensorKind (TKProduct accy by))
    -> HFun (TKProduct (ADTensorKind (TKProduct accy by))
                       (TKProduct accy ey))
            (ADTensorKind (TKProduct accy ey))
    -> Delta target accy
    -> Delta target (BuildTensorKind k ey)
    -> Delta target (TKProduct accy (BuildTensorKind k by))

  -- Vector space operations
  DeltaZero :: FullShapeTK y -> Delta target y
  DeltaScale :: Num (target y)
             => NestedTarget target y -> Delta target y -> Delta target y
  DeltaAdd :: Num (target y)
           => Delta target y -> Delta target y -> Delta target y

  -- Scalar arithmetic
  DeltaCastK :: ( NumScalar r1, Differentiable r1
                , NumScalar r2, Differentiable r2 )
             => Delta target (TKScalar r1) -> Delta target (TKScalar r2)

  -- Ranked tensor operations
  DeltaCastR :: ( NumScalar r1, Differentiable r1
                , NumScalar r2, Differentiable r2 )
             => Delta target (TKR n r1) -> Delta target (TKR n r2)
  DeltaSum0R :: NumScalar r
             => Delta target (TKR n r) -> Delta target (TKScalar r)
  DeltaDot0R :: (NumScalar r, Show (target (TKR n r)))
             => target (TKR n r) -> Delta target (TKR n r)
             -> Delta target (TKScalar r)
  DeltaIndexR :: forall m n r target.
                 SNat n
              -> Delta target (TKR2 (m + n) r) -> IxROf target m
              -> Delta target (TKR2 n r)
  DeltaScatterR :: forall m n p r target.
                   SNat m -> SNat n -> SNat p
                -> IShR p -> Delta target (TKR2 (m + n) r)
                -> (IxROf target m -> IxROf target p)
                -> Delta target (TKR2 (p + n) r)
  DeltaGatherR :: forall m n p r target.
                  SNat m -> SNat n -> SNat p
               -> IShR m -> Delta target (TKR2 (p + n) r)
               -> (IxROf target m -> IxROf target p)
               -> Delta target (TKR2 (m + n) r)
  DeltaAppendR :: Delta target (TKR2 (1 + n) r)
               -> Delta target (TKR2 (1 + n) r)
               -> Delta target (TKR2 (1 + n) r)
  DeltaSliceR :: Int -> Int -> Delta target (TKR2 (1 + n) r)
              -> Delta target (TKR2 (1 + n) r)
  DeltaReverseR :: Delta target (TKR2 (1 + n) r)
                -> Delta target (TKR2 (1 + n) r)
  DeltaTransposeR :: Permutation.PermR -> Delta target (TKR2 n r)
                  -> Delta target (TKR2 n r)
  DeltaReshapeR :: IShR m -> Delta target (TKR2 n r)
                -> Delta target (TKR2 m r)

  -- Shaped tensor operations
  DeltaCastS :: ( NumScalar r1, Differentiable r1
                , NumScalar r2, Differentiable r2 )
             => Delta target (TKS sh r1) -> Delta target (TKS sh r2)
  DeltaSum0S :: NumScalar r
             => Delta target (TKS sh r) -> Delta target (TKScalar r)
  DeltaDot0S :: (NumScalar r, Show (target (TKS sh r)))
             => target (TKS sh r) -> Delta target (TKS sh r)
             -> Delta target (TKScalar r)
  DeltaIndexS :: forall shm shn r target.
                 ShS shn
              -> Delta target (TKS2 (shm ++ shn) r) -> IxSOf target shm
              -> Delta target (TKS2 shn r)
  DeltaScatterS :: forall shm shn shp r target.
                   ShS shm -> ShS shn -> ShS shp
                -> Delta target (TKS2 (shm ++ shn) r)
                -> (IxSOf target shm -> IxSOf target shp)
                -> Delta target (TKS2 (shp ++ shn) r)
  DeltaGatherS :: forall shm shn shp r target.
                  ShS shm -> ShS shn -> ShS shp
               -> Delta target (TKS2 (shp ++ shn) r)
               -> (IxSOf target shm -> IxSOf target shp)
               -> Delta target (TKS2 (shm ++ shn) r)
  DeltaAppendS :: forall target r m n sh.
                  Delta target (TKS2 (m ': sh) r)
               -> Delta target (TKS2 (n ': sh) r)
               -> Delta target (TKS2 ((m + n) ': sh) r)
  DeltaSliceS :: SNat i -> SNat n -> SNat k
              -> Delta target (TKS2 (i + n + k ': sh) r)
              -> Delta target (TKS2 (n ': sh) r)
  DeltaReverseS :: Delta target (TKS2 (n ': sh) r)
                -> Delta target (TKS2 (n ': sh) r)
  DeltaTransposeS :: forall perm sh r target.
                     (Permutation.IsPermutation perm, Rank perm <= Rank sh)
                  => Permutation.Perm perm
                  -> Delta target (TKS2 sh r)
                  -> Delta target (TKS2 (Permutation.PermutePrefix perm sh) r)
  DeltaReshapeS :: Product sh ~ Product sh2
                => ShS sh2
                -> Delta target (TKS2 sh r)
                -> Delta target (TKS2 sh2 r)

  -- Mixed tensor operations
  DeltaCastX :: ( NumScalar r1, Differentiable r1
                , NumScalar r2, Differentiable r2 )
             => Delta target (TKX sh r1) -> Delta target (TKX sh r2)
  DeltaSum0X :: NumScalar r
             => Delta target (TKX sh r) -> Delta target (TKScalar r)
  DeltaDot0X :: (NumScalar r, Show (target (TKX sh r)))
             => target (TKX sh r) -> Delta target (TKX sh r)
             -> Delta target (TKScalar r)
  DeltaIndexX :: forall shm shn r target.
                 StaticShX shn
              -> Delta target (TKX2 (shm ++ shn) r) -> IxXOf target shm
              -> Delta target (TKX2 shn r)
  DeltaScatterX :: StaticShX shm -> StaticShX shn -> StaticShX shp
                -> IShX shp -> Delta target (TKX2 (shm ++ shn) r)
                -> (IxXOf target shm -> IxXOf target shp)
                -> Delta target (TKX2 (shp ++ shn) r)
  DeltaGatherX :: StaticShX shm -> StaticShX shn -> StaticShX shp
               -> IShX shm -> Delta target (TKX2 (shp ++ shn) r)
               -> (IxXOf target shm -> IxXOf target shp)
               -> Delta target (TKX2 (shm ++ shn) r)
  DeltaAppendX :: forall m n sh r target.
                  Delta target (TKX2 (m ': sh) r)
               -> Delta target (TKX2 (n ': sh) r)
               -> Delta target (TKX2 (AddMaybe m n ': sh) r)
  DeltaSliceX :: SMayNat Int i -> SMayNat Int n -> SMayNat Int k
              -> Delta target (TKX2 (AddMaybe (AddMaybe i n) k ': sh) r)
              -> Delta target (TKX2 (n ': sh) r)
  DeltaReverseX :: Delta target (TKX2 (mn ': sh) r)
                -> Delta target (TKX2 (mn ': sh) r)
  DeltaTransposeX :: forall perm sh r target.
                     (Permutation.IsPermutation perm, Rank perm <= Rank sh)
                  => Permutation.Perm perm
                  -> Delta target (TKX2 sh r)
                  -> Delta target (TKX2 (Permutation.PermutePrefix perm sh) r)
  DeltaReshapeX :: IShX sh2 -> Delta target (TKX2 sh r)
                -> Delta target (TKX2 sh2 r)

  -- Conversions
  DeltaConvert :: TKConversion a b -> Delta target a -> Delta target b

deriving instance Show (IntOf target) => Show (Delta target y)

-- | A newtype defined only to cut the knot of 'Show' instances in 'DeltaScale'
-- that are problematic to pass around as dictionaries without
-- bloating each constructor. The @DeltaScale@ constructor appears
-- in delta expressions a lot and so the primal
-- subterm would bloat the pretty-printed output (though OTOH the primal
-- terms are often important).
--
-- Possibly, @Has Show (Delta target)@ is a better solution.
type NestedTarget :: Target -> Target
type role NestedTarget nominal nominal
newtype NestedTarget target y = NestedTarget (target y)

instance Show (NestedTarget target y) where
  showsPrec _ _ = showString "<primal>"


-- * Full tensor kind derivation for delta expressions

-- | Full tensor kind derivation for delta expressions.
ftkDelta :: forall target y.
            Delta target y -> FullShapeTK y
ftkDelta = \case
  DeltaShare i _ -> nodeIdToFTK i
  DeltaInput i -> inputIdToFTK i

  DeltaPair t1 t2 -> FTKProduct (ftkDelta t1) (ftkDelta t2)
  DeltaProject1 v -> case ftkDelta v of
    FTKProduct ftk1 _ -> ftk1
  DeltaProject2 v -> case ftkDelta v of
    FTKProduct _ ftk2 -> ftk2
  DeltaFromVector snat _ l -> case V.uncons l of
    Nothing -> error "ftkDelta: empty vector"
    Just (d, _) -> buildFTK snat (ftkDelta d)
  DeltaSum snat stk d -> razeFTK snat stk (ftkDelta d)
  DeltaReplicate snat _ d -> buildFTK snat (ftkDelta d)
  DeltaMapAccumL k bftk _eftk _q _es _df _rf acc0' _es' ->
    FTKProduct (ftkDelta acc0') (buildFTK k bftk)

  DeltaZero ftk -> ftk
  DeltaScale _ d -> ftkDelta d
  DeltaAdd (DeltaShare i _) _ -> nodeIdToFTK i
  DeltaAdd _ e -> ftkDelta e

  DeltaCastK{} -> FTKScalar

  DeltaCastR d -> case ftkDelta d of
    FTKR sh _ -> FTKR sh FTKScalar
  DeltaSum0R{} -> FTKScalar
  DeltaDot0R{} -> FTKScalar
  DeltaIndexR SNat d ix | SNat <- ixrRank ix -> case ftkDelta d of
    FTKR sh x -> FTKR (shrDrop sh) x
  DeltaScatterR (SNat @m) SNat _ shp d _ -> case ftkDelta d of
    FTKR sh x -> FTKR (shp `shrAppend` shrDrop @m sh) x
  DeltaGatherR _ SNat (SNat @p) shm d _ -> case ftkDelta d of
    FTKR sh x -> FTKR (shm `shrAppend` shrDrop @p sh) x
  -- Depite the warning, the pattern match is exhaustive and if a dummy
  -- pattern is added, GHC 9.14.1 complains about that, in turn.
  DeltaAppendR a b -> case ftkDelta a of
    FTKR (ai :$: ash) x -> case ftkDelta b of
      FTKR (bi :$: _) _ -> FTKR (ai + bi :$: ash) x
  DeltaSliceR _ n d -> case ftkDelta d of
    FTKR sh x -> FTKR (n :$: shrTail sh) x
  DeltaReverseR d -> ftkDelta d
  DeltaTransposeR perm d -> case ftkDelta d of
    FTKR sh x -> FTKR (shrPermutePrefix perm sh) x
  DeltaReshapeR sh d -> case ftkDelta d of
    FTKR _ x -> FTKR sh x

  DeltaCastS d -> case ftkDelta d of
    FTKS sh FTKScalar -> FTKS sh FTKScalar
  DeltaSum0S{} -> FTKScalar
  DeltaDot0S{} -> FTKScalar
  DeltaIndexS shn d _ix -> case ftkDelta d of
    FTKS _ x -> FTKS shn x
  DeltaScatterS _shm shn shp d _ -> case ftkDelta d of
    FTKS _ x -> FTKS (shp `shsAppend` shn) x
  DeltaGatherS shm shn _shp d _ -> case ftkDelta d of
    FTKS _ x -> FTKS (shm `shsAppend` shn) x
  DeltaAppendS a b -> case (ftkDelta a, ftkDelta b) of
    (FTKS (m :$$ sh) x, FTKS (n :$$ _) _) -> FTKS (snatPlus m n :$$ sh) x
  DeltaSliceS _ n@SNat _ d -> case ftkDelta d of
    FTKS (_ :$$ sh) x -> FTKS (n :$$ sh) x
  DeltaReverseS d -> ftkDelta d
  DeltaTransposeS perm d -> case ftkDelta d of
    FTKS sh x -> FTKS (shsPermutePrefix perm sh) x
  DeltaReshapeS sh2 d -> case ftkDelta d of
    FTKS _ x -> FTKS sh2 x

  DeltaCastX d -> case ftkDelta d of
    FTKX sh FTKScalar -> FTKX sh FTKScalar
  DeltaSum0X{} -> FTKScalar
  DeltaDot0X{} -> FTKScalar
  DeltaIndexX @shm @shn shn d ix -> case ftkDelta d of
    FTKX sh x | SNat @len <- ixxRank ix ->
      gcastWith (unsafeCoerceRefl :: Drop (Rank shm) (shm ++ shn) :~: shn) $
      withKnownShX shn $
      FTKX (shxDrop @len sh) x  -- TODO: (shxDropSSX sh (ssxFromIxX ix)) x
  DeltaScatterX @_ @shn ssm _ _ shp d _ -> case ftkDelta d of
    FTKX sh x -> FTKX (shp `shxAppend` shxDropSSX @_ @shn ssm sh) x
  DeltaGatherX @_ @shn _ _ ssp shm d _ -> case ftkDelta d of
    FTKX sh x -> FTKX (shm `shxAppend` shxDropSSX @_ @shn ssp sh) x
  DeltaAppendX a b -> case (ftkDelta a, ftkDelta b) of
    (FTKX (m :$% sh) x, FTKX (n :$% _) _) ->
      FTKX (smnAddMaybe m n :$% sh) x
  DeltaSliceX _ n _ d -> case ftkDelta d of
    FTKX (_ :$% sh) x -> FTKX (n :$% sh) x
  DeltaReverseX d -> ftkDelta d
  DeltaTransposeX perm d -> case ftkDelta d of
    FTKX sh x -> FTKX (shxPermutePrefix perm sh) x
  DeltaReshapeX sh2 d -> case ftkDelta d of
    FTKX _ x -> FTKX sh2 x

  DeltaConvert c d -> convertFTK c $ ftkDelta d
