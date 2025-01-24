{-# LANGUAGE AllowAmbiguousTypes, DerivingStrategies, QuantifiedConstraints,
             UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10000 #-}
-- | TODO: This and most of other haddocks in this module are out of date.
--
-- The second component of our rendition of dual numbers:
-- delta expressions, with their semantics.
--
-- A delta expression can be viewed as a concise representation
-- of a linear map (which is the derivative of the objective function)
-- and its evaluation on a given argument as an adjoint (in the algebraic
-- sense) of the linear map applied to that argument. Since linear maps
-- can be represented as matrices, this operation corresponds
-- to a transposition of the matrix. However, the matrix is not constructed,
-- but is represented and transposed preserving the sparsity
-- of the representation.
--
-- The \'sparsity\' is less obvious when the domain of the function consists
-- of multiple vectors, matrices and tensors and when the expressions themselves
-- contain vectors, matrices and tensors. However, a single tiny delta
-- expression (e.g., a sum of two inputs) may denote a vector of matrices.
-- Even a delta expression containing a big matrix usually denotes something
-- much bigger: a whole vector of such matrices and more.
--
-- The algebraic structure here is an extension of vector space.
-- The crucial extra constructor of an input replaces the one-hot
-- access to parameters with something cheaper and more uniform.
-- A lot of the remaining additional structure is for introducing
-- and reducing dimensions (ranks).
--
-- This simplified rendering of the library now contains two ranks:
-- scalars and (ranked) tensors. However, most haddocks and code comments
-- are unchanged since the times vectors were available instead of tensors.
-- The newer setting is a straightforward generalization of the older one,
-- so the rewritten comments would be very similar and slightly harder
-- to understand.
module HordeAd.Core.Delta
  ( -- * Delta expression evaluation
    gradientFromDelta, derivativeFromDelta
    -- * Abstract syntax trees of the delta expressions
  , Delta(..)
    -- * Delta expression identifiers
  , NodeId (..), InputId, toInputId
    -- * Exported to be specialized elsewhere
  , evalRevFromnMap, EvalState
  ) where

import Prelude

import Control.Arrow (second)
import Control.Exception.Assert.Sugar
import Data.Dependent.EnumMap.Strict (DEnumMap)
import Data.Dependent.EnumMap.Strict qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Some
import Data.Traversable (mapAccumL)
import Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import Data.Vector.Generic qualified as V
import Data.Vector.Strict qualified as Data.Vector
import GHC.TypeLits (KnownNat, sameNat, type (+), type (<=))
import Text.Show (showListWith)
import Text.Show.Functions ()
import Type.Reflection (typeRep)

import Data.Array.Mixed.Permutation (permInverse)
import Data.Array.Mixed.Permutation qualified as Permutation
import Data.Array.Mixed.Shape
  (shxAppend, shxDropSSX, shxTail, shxTakeSSX, ssxFromShape, withKnownShX)
import Data.Array.Mixed.Types (unsafeCoerceRefl)
import Data.Array.Nested
  ( IShR
  , IShX
  , KnownShS (..)
  , KnownShX (..)
  , MapJust
  , Rank
  , Replicate
  , ShR (..)
  , ShS (..)
  , ShX (..)
  , type (++)
  )
import Data.Array.Nested qualified as Nested
import Data.Array.Nested.Internal.Shape
  ( shCvtRX
  , shCvtSX
  , shCvtXR'
  , shrRank
  , shrTail
  , shsAppend
  , shsPermutePrefix
  , shsProduct
  , shsRank
  , withKnownShS
  )
import Data.Array.Nested.Internal.Shape qualified as Nested.Internal.Shape

import HordeAd.Core.HVectorOps
import HordeAd.Core.TensorClass
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

type IMap target = DEnumMap (InputId target) (RepM target)

type ADMap target = DEnumMap (NodeId target) (RepAD target)

gradientFromDelta
  :: forall x z target.
     (ADReadyNoLet target, ShareTensor target, TensorKind z)
  => FullTensorKind x
  -> target z
  -> Maybe (target (ADTensorKind z))
  -> Delta target z
  -> target (ADTensorKind x)
gradientFromDelta !parameters0 value !mdt deltaTopLevel =
  let oneAtF = constantTarget 1 $ aDFTK $ tftk (stensorKind @z) value
      dt = fromMaybe oneAtF mdt
      s0 = initEvalState parameters0
      s1 = evalRev s0 dt deltaTopLevel
      s2 = evalRevFromnMap s1
      rebuildInputs :: forall ady.  -- ady ~ ADTensorKind y
                       [Some (RepM target)] -> FullTensorKind ady
                    -> (target ady, [Some (RepM target)])
      rebuildInputs els = \case
        FTKScalar @r -> case els of
          Some mt@(MTKScalar @r2 t) : rest ->
            case testEquality (typeRep @r) (typeRep @r2) of
              Just Refl -> (t, rest)
              _ -> error $ "gradientFromDelta: wrong type: " ++ show mt
          Some mt@(MTKScalarDummy @r2) : rest
            | Just Refl <- testEquality (typeRep @r) (typeRep @r2) ->
              (evalRepM mt, rest)
          _ -> error $ "gradientFromDelta: illegal RepM: "
                       ++ show_iMap (iMap s2)
        FTKR @n sh x | SNat <- shrRank sh
                     , Dict <- lemTensorKindOfSTK (ftkToStk x) -> case els of
          Some mt@(MTKR @r2 @n2 t) : rest ->
            case ( sameNat (Proxy @n) (Proxy @n2)
                 , sameSTK (ftkToStk x) (stensorKind @r2) ) of
              (Just Refl, Just Refl) -> (t, rest)
              _ -> error $ "gradientFromDelta: wrong type: " ++ show mt
                           ++ " instead of "
                           ++ "FTKR @" ++ show (valueOf @n :: Int)
                           ++ " within " ++ show_iMap (iMap s2)
          Some mt@(MTKRDummy @_ @n2 sh2 x2) : rest
            | SNat <- shrRank sh2
            , Just Refl <- sameNat (Proxy @n) (Proxy @n2)  -- TODO: compare sh
            , Just Refl <- sameSTK (ftkToStk x) (ftkToStk x2) ->  -- TODO: compare ftk
              (evalRepM mt, rest)
          _ -> error $ "gradientFromDelta: illegal RepM: "
                       ++ show_iMap (iMap s2)
        FTKS @sh sh x | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          withKnownShS sh $ case els of
            Some mt@(MTKS @r2 @sh2 t) : rest ->
              case ( sameShape @sh @sh2
                   , sameSTK (ftkToStk x) (stensorKind @r2) ) of
                (Just Refl, Just Refl) -> (t, rest)
                _ -> error $ "gradientFromDelta: wrong type: " ++ show mt
                             ++ " instead of "
                             ++ "FTKS @" ++ show (knownShS @sh)
                             ++ " within " ++ show_iMap (iMap s2)
            Some mt@(MTKSDummy sh2 x2) : rest
              | Just Refl <- testEquality sh sh2
              , Just Refl <- sameSTK (ftkToStk x) (ftkToStk x2) ->
                (evalRepM mt, rest)
            _ -> error $ "gradientFromDelta: illegal RepM: "
                         ++ show_iMap (iMap s2)
        FTKX{} -> error "TODO"
        FTKProduct @y1 @y2 ftk1 ftk2
         | Dict <- lemTensorKindOfSTK (ftkToStk ftk1)
         , Dict <- lemTensorKindOfSTK (ftkToStk ftk2) ->
            let (t1, rest1) = rebuildInputs @y1 els ftk1
                (t2, rest2) = rebuildInputs @y2 rest1 ftk2
            in (tpair t1 t2, rest2)
      (res, remainder) = rebuildInputs @(ADTensorKind x) (DMap.elems $ iMap s2)
                         $ aDFTK parameters0
  in assert (null remainder) res

showsPrec_iMap
  :: (forall y. TensorKind y => Show (RepM target y))
  => Int -> IMap target -> ShowS
showsPrec_iMap d demap =
  showParen (d > 10) $
    showString "fromList "
    . showListWith
        (\(k :=> target) ->
          case tensorKindFromInputId k of
            Dict -> showsPrec 2 k . showString " :=> " . showsPrec 1 target)
        (DMap.toList demap)

show_iMap
  :: (forall y. TensorKind y => Show (RepM target y))
  => IMap target -> String
show_iMap iMap = showsPrec_iMap 0 iMap ""

derivativeFromDelta
  :: forall x z target.
     ( ADReadyNoLet target, ShareTensor target, TensorKind x, TensorKind z )
  => Delta target z -> target (ADTensorKind x)
  -> target (ADTensorKind z)
derivativeFromDelta deltaTopLevel ds | Dict <- lemTensorKindOfAD (stensorKind @x) =
  let -- Matches generateDeltaInputs.
      generateDSums :: Int -> FullTensorKind y -> target y
                    -> ( [DSum (InputId target) (RepM target)]
                       , Int )
      generateDSums j ftk t = case ftk of
        FTKScalar @r -> ([InputId j :=> MTKScalar @r t], j + 1)
        FTKR sh x | SNat <- shrRank sh
                  , Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          ([InputId j :=> MTKR t], j + 1)
        FTKS sh x | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          withKnownShS sh $
          ([InputId j :=> MTKS t], j + 1)
        FTKX{} -> error "TODO"
        FTKProduct ftk1 ftk2 | Dict <- lemTensorKindOfSTK (ftkToStk ftk1)
                             , Dict <- lemTensorKindOfSTK (ftkToStk ftk2) ->
          let (t1, t2) = tunpair t
              (ds1, j1) = generateDSums j ftk1 t1
              (ds2, j2) = generateDSums j1 ftk2 t2
          in (ds1 ++ ds2, j2)
      iMap = DMap.fromDistinctAscList $ fst
             $ generateDSums 0 (tftk stensorKind ds) ds
      s0 = DMap.empty
      !(!_s2, !c) = evalFwd iMap s0 deltaTopLevel
  in c

evalRepM :: forall target x. ADReadyNoLet target
         => RepM target x -> target x
evalRepM = \case
  MTKScalar t -> t
  MTKR t -> t
  MTKS t -> t
  MTKScalarDummy -> kconcrete 0
  MTKRDummy shr ftk -> constantTarget 0 (FTKR shr ftk)
  MTKSDummy sh ftk -> constantTarget 0 (FTKS sh ftk)

repToM
  :: STensorKindType x -> target x
  -> RepM target x
repToM stk t = case stk of
  STKScalar{} -> MTKScalar t
  STKR SNat x | Dict <- lemTensorKindOfSTK x -> MTKR t
  STKS sh x | Dict <- lemTensorKindOfSTK x -> withKnownShS sh $ MTKS t
  STKX sh x | Dict <- lemTensorKindOfSTK x -> withKnownShX sh $ error "TODO"
  STKProduct{} -> error "repToM: unexpected type"

addRepM :: forall target y. ADReadyNoLet target
        => RepM target y -> RepM target y -> RepM target y
addRepM a b = case (a, b) of
  (MTKScalar ta, MTKScalar tb) -> MTKScalar $ ta + tb
  (MTKR ta, MTKR tb) | STKR _ STKScalar{} <- stensorKind @y -> MTKR $ ta + tb
  (MTKR ta, MTKR tb) -> MTKR $ addTarget stensorKind ta tb
  (MTKScalarDummy, _) -> b
  (_, MTKScalarDummy) -> a
  (MTKRDummy{}, _) -> b
  (_, MTKRDummy{}) -> a
  (MTKS ta, MTKS tb) | STKS _ STKScalar{} <- stensorKind @y -> MTKS $ ta + tb
  (MTKS ta, MTKS tb) -> MTKS $ addTarget stensorKind ta tb
  (MTKSDummy{}, _) -> b
  (_, MTKSDummy{}) -> a

type role RepM nominal nominal
data RepM target y where
  MTKScalar :: GoodScalar r
            => target (TKScalar r)
            -> RepM target (TKScalar r)
  MTKR :: (TensorKind r, KnownNat n)
       => target (TKR2 n r)
       -> RepM target (TKR2 n r)
  MTKS :: (TensorKind r, KnownShS sh)
       => target (TKS2 sh r)
       -> RepM target (TKS2 sh r)
  MTKScalarDummy :: GoodScalar r
                 => RepM target (TKScalar r)
  MTKRDummy :: forall x n target.
               IShR n -> FullTensorKind x
            -> RepM target (TKR2 n x)
  MTKSDummy  :: forall x sh target.
                ShS sh -> FullTensorKind x
             -> RepM target (TKS2 sh x)

deriving instance ( (forall y7. TensorKind y7 => Show (target y7))
                  , TensorKind y )
                  => Show (RepM target y)

-- * Abstract syntax trees of the delta expressions

-- | TODO: This and most of other haddocks are out of date.
--
-- For each choice of the underlying scalar type @r@,
-- we have several primitive differentiable types based on the scalar:
-- the scalar type @r@ itself, @Vector r@ and (in the non-simplified
-- version of delta expressions) @Matrix r@ and tensors.
-- Many operations span the ranks and so span the datatypes, which makes
-- the datatypes mutually recursive. Later on in this module,
-- algorithms are implemented for computing gradients and for computing
-- derivatives of objective functions from which such delta expressions
-- are obtained via our dual number method.
--
-- The first pair of grammars given below are of delta-expressions
-- at tensor rank 0, that is, at the scalar level. The first few operations
-- have analogues at the level of vectors, matrices and arbitrary tensors,
-- but the other operations are specific to the rank.
--
-- The `NodeId` identifier that appears in a @DeltaShare n d@ expression
-- is the unique identity stamp of subterm @d@, that is, there is
-- no different term @e@ such that @DeltaShare n e@ appears in any delta
-- expression term in memory during the same run of an executable.
-- The subterm identity is used to avoid evaluating shared
-- subterms repeatedly in gradient and derivative computations.
-- The identifier also represents data dependencies among terms
-- for the purpose of gradient and derivative computation. Computation for
-- a term may depend only on data obtained from terms with lower value
-- of their node identifiers. Such data dependency determination
-- agrees with the subterm relation, but is faster than traversing
-- the term tree in order to determine the relation of terms.
--
-- There is one exception to the subterm data dependency rule:
-- any term containing a function (e.g., a @DeltaGather@ node)
-- may depend on terms generated by applying the function,
-- regardless of their node identifiers (which in our implementation
-- are going to be larger than their ancestors').
-- Note that the functions inside constructors can be readily converted
-- to AST terms (with distinguished variables) when we are working
-- in an AST instance. However, this is not needed, because the AST term
-- resulting from differentiation for that instance won't have any functions
-- embedded, so there's no problem with sending Haskell closures to a GPU.
-- And in other instances we can't directly use GPUs anyway (though we can
-- indirectly, e.g., via ArrayFire), because we don't produce AST terms
-- that could be compiled for a GPU, so we don't worry about it.
--
-- When computing gradients, node identifiers are also used to index,
-- directly or indirectly, the data accumulated for each node,
-- in the form of cotangents, that is partial derivatives
-- of the objective function with respect to the position(s)
-- of the node in the whole objective function dual number term
-- (or, more precisely, with respect to the single node in the term DAG,
-- in which subterms with the same node identifier are collapsed).
-- Only the @Input@ nodes of all ranks have a separate data storage.
-- The per-rank `InputId` identifiers in the @Input@ term constructors
-- are indexes into contiguous vectors of cotangents of exclusively @Input@
-- subterms of the whole term. The value at that index is the partial
-- derivative of the objective function (represented by the whole term,
-- or more precisely by (the data flow graph of) its particular
-- evaluation from which the delta expression originates)
-- with respect to the input parameter component at that index
-- in the objective function domain. The collection of all such
-- vectors of partial derivatives across all ranks is the gradient.
--
-- This is the grammar of delta-expressions corresponding to ranked tensors.
-- The comments refer to the ordinary (forward) semantics of the terms,
-- as given in @buildDerivative@. Evaluating the terms backwards
-- (transposing the represented linear map) in order to compute gradients
-- provides a different semantics.

type role Delta nominal nominal
data Delta :: Target -> TensorKindType -> Type where
  -- General operations, for scalar, ranked, shared and other tensors at once
  DeltaPair :: (TensorKind y, TensorKind z)
            => Delta target y -> Delta target z
            -> Delta target (TKProduct y z)
  DeltaProject1 :: (TensorKind x, TensorKind z)
                => Delta target (TKProduct x z) -> Delta target x
  DeltaProject2 :: (TensorKind x, TensorKind z)
                => Delta target (TKProduct x z) -> Delta target z
  DeltaFromVector :: TensorKind y  -- needed for the Show instance
                  => SNat k -> STensorKindType y
                  -> Data.Vector.Vector (Delta target y)
                  -> Delta target (BuildTensorKind k y)
    -- ^ Create a tensor from a boxed vector treated as the outermost dimension.
  DeltaSum :: TensorKind (BuildTensorKind k y)  -- needed for the Show instance
           => SNat k -> STensorKindType y
           -> Delta target (BuildTensorKind k y)
           -> Delta target y
  DeltaReplicate :: TensorKind y  -- needed for the Show instance
                 => SNat k -> STensorKindType y
                 -> Delta target y
                 -> Delta target (BuildTensorKind k y)
    -- ^ Copy the given tensor along the new, outermost dimension.
  DeltaMapAccumR
    :: forall target k accShs bShs eShs.
       ( TensorKind accShs, TensorKind bShs, TensorKind eShs
       , TensorKind (BuildTensorKind k eShs)
       , TensorKind (BuildTensorKind k accShs) )
    => SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> target (BuildTensorKind k accShs)
    -> target (BuildTensorKind k eShs)
    -> HFun (TKProduct (ADTensorKind (TKProduct accShs eShs))
                       (TKProduct accShs eShs))
            (ADTensorKind (TKProduct accShs bShs))
    -> HFun (TKProduct (ADTensorKind (TKProduct accShs bShs))
                       (TKProduct accShs eShs))
            (ADTensorKind (TKProduct accShs eShs))
    -> Delta target accShs
    -> Delta target (BuildTensorKind k eShs)
    -> Delta target (TKProduct accShs (BuildTensorKind k bShs))
  DeltaMapAccumL
    :: forall target k accShs bShs eShs.
       ( TensorKind accShs, TensorKind bShs, TensorKind eShs
       , TensorKind (BuildTensorKind k eShs)
       , TensorKind (BuildTensorKind k accShs) )
    => SNat k
    -> FullTensorKind accShs
    -> FullTensorKind bShs
    -> FullTensorKind eShs
    -> target (BuildTensorKind k accShs)
    -> target (BuildTensorKind k eShs)
    -> HFun (TKProduct (ADTensorKind (TKProduct accShs eShs))
                       (TKProduct accShs eShs))
            (ADTensorKind (TKProduct accShs bShs))
    -> HFun (TKProduct (ADTensorKind (TKProduct accShs bShs))
                       (TKProduct accShs eShs))
            (ADTensorKind (TKProduct accShs eShs))
    -> Delta target accShs
    -> Delta target (BuildTensorKind k eShs)
    -> Delta target (TKProduct accShs (BuildTensorKind k bShs))

  -- Sharing-related operations
  DeltaShare :: NodeId target y -> Delta target y -> Delta target y
  DeltaInput :: forall target y.
                FullTensorKind y -> InputId target y -> Delta target y

  -- Vector space operations
  DeltaZero :: FullTensorKind y -> Delta target y
  DeltaScale :: Num (target y)
             => target y -> Delta target y -> Delta target y
  DeltaAdd :: Num (target y)
           => Delta target y -> Delta target y -> Delta target y

  -- Scalar arithmetic
  DeltaCast :: (GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2)
            => Delta target (TKScalar r1) -> Delta target (TKScalar r2)

  -- Ranked tensor operations
  DeltaCastR :: ( GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2
                , KnownNat n )
             => Delta target (TKR n r1) -> Delta target (TKR n r2)
  DeltaIndexR :: (TensorKind r, KnownNat n, KnownNat m)
              => Delta target (TKR2 (m + n) r) -> IxROf target m
              -> Delta target (TKR2 n r)
    -- ^ The sub-tensor at the given index. The given shape is of the
    -- large tensor. If index is out of bounds, the result is defined and is 0.
  DeltaSum0R :: (TensorKind r, KnownNat n)
             => Delta target (TKR2 n r) -> Delta target (TKR2 0 r)
  DeltaDot0R :: (KnownNat n, GoodScalar r)
             => target (TKR n r) -> Delta target (TKR n r)
             -> Delta target (TKR 0 r)
  DeltaScatterR :: (TensorKind r, KnownNat m, KnownNat n, KnownNat p)
           => IShR (p + n) -> Delta target (TKR2 (m + n) r)
           -> (IxROf target m -> IxROf target p)
           -> Delta target (TKR2 (p + n) r)
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @DeltaScatter1 5 (const ZR) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @DeltaScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for DeltaScatter1; fix.
  DeltaAppendR :: (TensorKind r, KnownNat n)
               => Delta target (TKR2 (1 + n) r)
               -> Delta target (TKR2 (1 + n) r)
               -> Delta target (TKR2 (1 + n) r)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
  DeltaSliceR :: (TensorKind r, KnownNat n)
              => Int -> Int -> Delta target (TKR2 (1 + n) r)
              -> Delta target (TKR2 (1 + n) r)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
  DeltaReverseR :: (TensorKind r, KnownNat n)
                => Delta target (TKR2 (1 + n) r) -> Delta target (TKR2 (1 + n) r)
    -- ^ Reverse elements of the outermost dimension.
  DeltaTransposeR :: (TensorKind r, KnownNat n)
                  => Permutation.PermR -> Delta target (TKR2 n r)
                  -> Delta target (TKR2 n r)
    -- ^ Transpose according to the permutation.
  DeltaReshapeR :: (TensorKind r, KnownNat n, KnownNat m)
                => IShR m -> Delta target (TKR2 n r)
                -> Delta target (TKR2 m r)
    -- ^ Change the shape of the tensor to the given one.
  DeltaGatherR :: (TensorKind r, KnownNat m, KnownNat n, KnownNat p)
               => IShR (m + n) -> Delta target (TKR2 (p + n) r)
               -> (IxROf target m -> IxROf target p)
               -> Delta target (TKR2 (m + n) r)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @DeltaGather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @DeltaGatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for DeltaGather1; fix.
  DeltaZipR :: (TensorKind y, TensorKind z, KnownNat n)
            => Delta target (TKProduct (TKR2 n y) (TKR2 n z))
            -> Delta target (TKR2 n (TKProduct y z))
  DeltaUnzipR :: (TensorKind y, TensorKind z, KnownNat n)
              => Delta target (TKR2 n (TKProduct y z))
              -> Delta target (TKProduct (TKR2 n y) (TKR2 n z))

  -- Shaped tensor operations
  DeltaCastS :: ( GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2
                , KnownShS sh )
             => Delta target (TKS sh r1) -> Delta target (TKS sh r2)
  DeltaIndexS :: ( TensorKind r, KnownShS shm, KnownShS shn
                 , KnownShS (shm ++ shn) )  -- needed for the Show instance
              => Delta target (TKS2 (shm ++ shn) r)
              -> IxSOf target shm
              -> Delta target (TKS2 shn r)
    -- ^ The sub-tensor at the given index.
    -- If index is out of bounds, the result is defined and is 0.
  DeltaSum0S :: (TensorKind r, KnownShS sh)
             => Delta target (TKS2 sh r) -> Delta target (TKS2 '[] r)
  DeltaDot0S :: (GoodScalar r, KnownShS sh)
             => target (TKS sh r) -> Delta target (TKS sh r)
             -> Delta target (TKS '[] r)
  DeltaScatterS :: forall target r shm shn shp.
                   ( TensorKind r, KnownShS shm, KnownShS shn, KnownShS shp
                   , KnownShS (shm ++ shn) )  -- needed for the Show instance
                => Delta target (TKS2 (shm ++ shn) r)
                -> (IxSOf target shm -> IxSOf target shp)
                -> Delta target (TKS2 (shp ++ shn) r)
    -- ^ Build a tensor by adding up tensors of rank @n@ taken from
    -- the third argument and inserted in a zero tensor
    -- at indexes of length @p@. Indexes of length 0 insert tensors trivially,
    -- so that, e.g, @DeltaScatter1 5 (const ZR) (Replicate0R [5] d) []@ is equivalent
    -- to @5 * d@. If an index of length @p@ is out of bounds, no tensor
    -- is added at such an index (and similarly in @DeltaScatterN@).
    -- The semantics of the operation permits index out of bounds
    -- and then no tensors is added at such an index.
    -- TODO: this is a haddock for DeltaScatter1; fix.
  DeltaAppendS :: forall target r m n sh.
                  (TensorKind r, KnownNat m, KnownNat n, KnownShS sh)
               => Delta target (TKS2 (m ': sh) r)
               -> Delta target (TKS2 (n ': sh) r)
               -> Delta target (TKS2 ((m + n) ': sh) r)
    -- ^ Append two arrays along the outermost dimension.
    -- All dimensions, except the outermost, must be the same.
    -- The integer argument is the outermost size of the first array.
  DeltaSliceS :: forall target i n k r sh.
                 (TensorKind r, KnownNat i, KnownNat n, KnownNat k, KnownShS sh)
              => Delta target (TKS2 (i + n + k ': sh) r)
              -> Delta target (TKS2 (n ': sh) r)
    -- ^ Extract a slice of an array along the outermost dimension.
    -- The extracted slice must fall within the dimension.
    -- The last argument is the outermost size of the argument array.
  DeltaReverseS :: (TensorKind r, KnownShS sh, KnownNat n)
                => Delta target (TKS2 (n ': sh) r)
                -> Delta target (TKS2 (n ': sh) r)
    -- ^ Reverse elements of the outermost dimension.
  DeltaTransposeS :: forall perm sh r target.
                     (TensorKind r, PermC perm, KnownShS sh, Rank perm <= Rank sh)
                  => Permutation.Perm perm
                  -> Delta target (TKS2 sh r)
                  -> Delta target (TKS2 (Permutation.PermutePrefix perm sh) r)
    -- ^ Transpose according to the permutation.
  DeltaReshapeS :: ( TensorKind r, KnownShS sh, KnownShS sh2
                   , Nested.Product sh ~ Nested.Product sh2 )
                => Delta target (TKS2 sh r)
                -> Delta target (TKS2 sh2 r)
    -- ^ Change the shape of the tensor from the first to the second.
  DeltaGatherS :: forall target r shm shn shp.
                  ( TensorKind r, KnownShS shm, KnownShS shn, KnownShS shp
                  , KnownShS (shp ++ shn) )  -- needed for the Show instance
               => Delta target (TKS2 (shp ++ shn) r)
               -> (IxSOf target shm -> IxSOf target shp)
               -> Delta target (TKS2 (shm ++ shn) r)
    -- ^ Build a tensor by picking tensors of rank @n@ at the given indexes
    -- of length @p@. Index of length 0 results in identity, so that,
    -- e.g, @DeltaGather1 (const ZR) [] (ScalarR d) k@ is equivalent
    -- to @Replicate0R [k] d@. If an index of length @p@ is out of bounds,
    -- tensor 0 is chosen instead or projecting (and similarly in @DeltaGatherN@).
    -- The semantics of the operation permits index out of bounds
    -- and the result of such indexing is zero.
    -- TODO: this is a haddock for DeltaGather1; fix.
  DeltaZipS :: (TensorKind y, TensorKind z, KnownShS sh)
            => Delta target (TKProduct (TKS2 sh y) (TKS2 sh z))
            -> Delta target (TKS2 sh (TKProduct y z))
  DeltaUnzipS :: (TensorKind y, TensorKind z, KnownShS sh)
              => Delta target (TKS2 sh (TKProduct y z))
              -> Delta target (TKProduct (TKS2 sh y) (TKS2 sh z))

  -- Mixed tensor operations
  DeltaCastX :: ( GoodScalar r1, RealFrac r1, GoodScalar r2, RealFrac r2
                , KnownShX sh )
             => Delta target (TKX sh r1) -> Delta target (TKX sh r2)
  DeltaIndexX :: (KnownShX sh1, KnownShX sh2, KnownShX (sh1 ++ sh2), TensorKind r)
              => Delta target (TKX2 (sh1 ++ sh2) r)
              -> IxXOf target sh1
              -> Delta target (TKX2 sh2 r)
  DeltaSum0X :: (TensorKind r, KnownShX sh)
             => Delta target (TKX2 sh r) -> Delta target (TKX2 '[] r)
  DeltaDot0X :: (GoodScalar r, KnownShX sh)
             => target (TKX sh r) -> Delta target (TKX sh r)
             -> Delta target (TKX '[] r)
  DeltaScatterX :: forall target r shm shn shp.
                   ( TensorKind r, KnownShX shm, KnownShX shn, KnownShX shp
                   , KnownShX (shm ++ shn) )  -- needed for the Show instance
                => IShX (shp ++ shn) -> Delta target (TKX2 (shm ++ shn) r)
                -> (IxXOf target shm -> IxXOf target shp)
                -> Delta target (TKX2 (shp ++ shn) r)
  DeltaAppendX :: forall target r sh.
                  (TensorKind r, KnownShX sh)
               => Delta target (TKX2 (Nothing ': sh) r)
               -> Delta target (TKX2 (Nothing ': sh) r)
               -> Delta target (TKX2 (Nothing ': sh) r)
  DeltaSliceX :: forall target i n k r sh.
                 (TensorKind r, KnownNat i, KnownNat n, KnownNat k, KnownShX sh)
              => Delta target (TKX2 (Just (i + n + k) ': sh) r)
              -> Delta target (TKX2 (Just n ': sh) r)
  DeltaReverseX :: (TensorKind r, KnownShX sh)
                => Delta target (TKX2 (mn ': sh) r)
                -> Delta target (TKX2 (mn ': sh) r)
  DeltaTransposeX :: forall perm sh r target.
                     (TensorKind r, PermC perm, KnownShX sh, Rank perm <= Rank sh)
                  => Permutation.Perm perm
                  -> Delta target (TKX2 sh r)
                  -> Delta target (TKX2 (Permutation.PermutePrefix perm sh) r)
  DeltaReshapeX :: (TensorKind r, KnownShX sh, KnownShX sh2)
                => IShX sh2 -> Delta target (TKX2 sh r)
                -> Delta target (TKX2 sh2 r)
  DeltaGatherX :: forall target r shm shn shp.
                  ( TensorKind r, KnownShX shm, KnownShX shn, KnownShX shp
                  , KnownShX (shp ++ shn) )  -- needed for the Show instance
               => IShX (shm ++ shn) -> Delta target (TKX2 (shp ++ shn) r)
               -> (IxXOf target shm -> IxXOf target shp)
               -> Delta target (TKX2 (shm ++ shn) r)
  DeltaZipX :: (TensorKind y, TensorKind z, KnownShX sh)
            => Delta target (TKProduct (TKX2 sh y) (TKX2 sh z))
            -> Delta target (TKX2 sh (TKProduct y z))
  DeltaUnzipX :: (TensorKind y, TensorKind z, KnownShX sh)
              => Delta target (TKX2 sh (TKProduct y z))
              -> Delta target (TKProduct (TKX2 sh y) (TKX2 sh z))

  -- Conversions
  DeltaFromS :: forall y z target. (TensorKind y, TensorKind z)
             => Delta target y -> Delta target z
  DeltaSFromScalar :: GoodScalar r
                   => Delta target (TKScalar r) -> Delta target (TKS '[] r)
  DeltaSFromR :: forall sh r target.
                 (KnownShS sh, KnownNat (Rank sh), TensorKind r)
              => Delta target (TKR2 (Rank sh) r)
              -> Delta target (TKS2 sh r)
  DeltaSFromX :: forall sh sh' r target.
                 (KnownShS sh, KnownShX sh', Rank sh ~ Rank sh', TensorKind r)
              => Delta target (TKX2 sh' r)
              -> Delta target (TKS2 sh r)

  DeltaXNestR :: ( TensorKind x, KnownShX sh1, KnownNat m
                 , KnownShX (sh1 ++ Replicate m Nothing) )
              => Delta target (TKX2 (sh1 ++ Replicate m Nothing) x)
              -> Delta target (TKX2 sh1 (TKR2 m x))
    -- The constraints about ++ in these three are needed for deriving Show.
  DeltaXNestS :: ( TensorKind x, KnownShX sh1, KnownShS sh2
                 , KnownShX (sh1 ++ MapJust sh2) )
              => Delta target (TKX2 (sh1 ++ MapJust sh2) x)
              -> Delta target (TKX2 sh1 (TKS2 sh2 x))
  DeltaXNest :: (TensorKind x, KnownShX sh1, KnownShX sh2, KnownShX (sh1 ++ sh2))
             => Delta target (TKX2 (sh1 ++ sh2) x)
             -> Delta target (TKX2 sh1 (TKX2 sh2 x))
  DeltaXUnNestR :: (TensorKind x, KnownShX sh1, KnownNat m)
                => Delta target (TKX2 sh1 (TKR2 m x))
                -> Delta target (TKX2 (sh1 ++ Replicate m Nothing) x)
  DeltaXUnNestS :: (TensorKind x, KnownShX sh1, KnownShS sh2)
                => Delta target (TKX2 sh1 (TKS2 sh2 x))
                -> Delta target (TKX2 (sh1 ++ MapJust sh2) x)
  DeltaXUnNest :: (TensorKind x, KnownShX sh1, KnownShX sh2)
               => Delta target (TKX2 sh1 (TKX2 sh2 x))
               -> Delta target (TKX2 (sh1 ++ sh2) x)

deriving instance ( TensorKind y
                  , Show (IntOf target)
                  , (forall y7. TensorKind y7 => Show (target y7)) )
                  => Show (Delta target y)

shapeDeltaFull :: forall target y. TensorKind y
               => Delta target y -> FullTensorKind y
shapeDeltaFull = \case
  DeltaCast{} -> FTKScalar
  DeltaSFromScalar{} -> FTKS ZSS FTKScalar
  DeltaPair t1 t2 -> FTKProduct (shapeDeltaFull t1) (shapeDeltaFull t2)
  DeltaProject1 v -> case shapeDeltaFull v of
    FTKProduct ftk1 _ -> ftk1
  DeltaProject2 v -> case shapeDeltaFull v of
    FTKProduct _ ftk2 -> ftk2
  DeltaFromVector snat _ l -> case V.toList l of
    [] -> error "shapeDeltaFull: empty vector"
    d : _ -> buildFTK snat (shapeDeltaFull d)
  DeltaSum snat stk d -> razeFTK snat stk (shapeDeltaFull d)
  DeltaReplicate snat _ d -> buildFTK snat (shapeDeltaFull d)
  DeltaInput ftk _ -> ftk
  DeltaShare _ d -> shapeDeltaFull d
  DeltaZero ftk -> ftk
  DeltaScale _ d -> shapeDeltaFull d
  DeltaAdd d _ -> shapeDeltaFull d

  DeltaIndexR d _ -> case shapeDeltaFull d of
    FTKR sh x -> FTKR (dropShape sh) x
  DeltaSum0R d -> case shapeDeltaFull d of
    FTKR _ x -> FTKR ZSR x
  DeltaDot0R{} -> FTKR ZSR FTKScalar
  DeltaScatterR sh d _ -> case shapeDeltaFull d of
    FTKR _ x -> FTKR sh x
  DeltaAppendR a b -> case shapeDeltaFull a of
    FTKR ZSR _ -> error "shapeDeltaFull: impossible pattern needlessly required"
    FTKR (ai :$: ash) x -> case shapeDeltaFull b of
      FTKR ZSR _ -> error "shapeDeltaFull: impossible pattern needlessly required"
      FTKR (bi :$: _) _ -> FTKR (ai + bi :$: ash) x
  DeltaSliceR _ n d -> case shapeDeltaFull d of
    FTKR sh x -> FTKR (n :$: shrTail sh) x
  DeltaReverseR d -> shapeDeltaFull d
  DeltaTransposeR perm d -> case shapeDeltaFull d of
    FTKR sh x -> FTKR (Nested.Internal.Shape.shrPermutePrefix perm sh) x
  DeltaReshapeR sh d -> case shapeDeltaFull d of
    FTKR _ x -> FTKR sh x
  DeltaGatherR sh d _ -> case shapeDeltaFull d of
    FTKR _ x -> FTKR sh x
  DeltaCastR d -> FTKR (shapeDelta d) FTKScalar
  DeltaZipR d -> case shapeDeltaFull d of
    FTKProduct (FTKR sh y) (FTKR _ z) -> FTKR sh (FTKProduct y z)
  DeltaUnzipR d -> case shapeDeltaFull d of
    FTKR sh (FTKProduct y z) -> FTKProduct (FTKR sh y) (FTKR sh z)

  DeltaIndexS d _ix -> case shapeDeltaFull d of
    FTKS _ x -> FTKS knownShS x
  DeltaSum0S d -> case shapeDeltaFull d of
    FTKS _ x -> FTKS ZSS x
  DeltaDot0S{} -> FTKS ZSS FTKScalar
  DeltaScatterS @_ @_ @_ @shn @shp d _ -> case shapeDeltaFull d of
    FTKS _ x -> FTKS (knownShS @shp `shsAppend` knownShS @shn) x
  DeltaAppendS a _ -> case shapeDeltaFull a of
    FTKS _ x -> FTKS knownShS x
  DeltaSliceS d -> case shapeDeltaFull d of
    FTKS _ x -> FTKS knownShS x
  DeltaReverseS d -> shapeDeltaFull d
  DeltaTransposeS @_ @sh2 perm d -> case shapeDeltaFull d of
    FTKS _ x -> FTKS (shsPermutePrefix perm (knownShS @sh2)) x
  DeltaReshapeS d -> case shapeDeltaFull d of
    FTKS _ x -> FTKS knownShS x
  DeltaGatherS @_ @_ @shm @shn d _ -> case shapeDeltaFull d of
    FTKS _ x -> FTKS (knownShS @shm `shsAppend` knownShS @shn) x
  DeltaCastS{} -> FTKS knownShS FTKScalar
  DeltaZipS d -> case shapeDeltaFull d of
    FTKProduct (FTKS sh y) (FTKS _ z) -> FTKS sh (FTKProduct y z)
  DeltaUnzipS d -> case shapeDeltaFull d of
    FTKS sh (FTKProduct y z) -> FTKProduct (FTKS sh y) (FTKS sh z)

  DeltaIndexX @sh1 d _ix -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (shxDropSSX sh (knownShX @sh1)) x
  DeltaSum0X d -> case shapeDeltaFull d of
    FTKX _ x -> FTKX ZSX x
  DeltaDot0X{} -> FTKX ZSX FTKScalar
  DeltaScatterX sh d _ -> case shapeDeltaFull d of
    FTKX _ x -> FTKX sh x
  DeltaAppendX a _ -> shapeDeltaFull a
  DeltaSliceX @_ @_ @n d -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (Nested.SKnown (SNat @n) :$% shxTail sh) x
  DeltaReverseX d -> shapeDeltaFull d
  DeltaTransposeX perm d -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (shxPermutePrefix perm sh) x
  DeltaReshapeX sh2 d -> case shapeDeltaFull d of
    FTKX _ x -> FTKX sh2 x
  DeltaGatherX sh d _ -> case shapeDeltaFull d of
    FTKX _ x -> FTKX sh x
  DeltaCastX d -> case shapeDeltaFull d of
    FTKX sh FTKScalar -> FTKX sh FTKScalar
  DeltaZipX d -> case shapeDeltaFull d of
    FTKProduct (FTKX sh y) (FTKX _ z) -> FTKX sh (FTKProduct y z)
  DeltaUnzipX d -> case shapeDeltaFull d of
    FTKX sh (FTKProduct y z) -> FTKProduct (FTKX sh y) (FTKX sh z)

  DeltaFromS @_ @z d ->
    let fromS :: FullTensorKind y2 -> STensorKindType z2 -> FullTensorKind z2
        fromS ftk stk = case (ftk, stk) of
          _ | Just Refl <- sameSTK (ftkToStk ftk) stk -> ftk
          (FTKS ZSS (FTKScalar @r), STKScalar tr) ->
            case testEquality (typeRep @r) tr of
              Just Refl -> FTKScalar
              Nothing -> error "shapeDeltaFull: wrong tensor kinds for DeltaFromS"
          (FTKS sh x, STKR nx zx) ->
            case ( sameSTK (ftkToStk x) zx
                 , testEquality (shsRank sh) nx ) of
              (Just Refl, Just Refl) -> FTKR (shCastSR sh) x
              _ -> error $ "shapeDeltaFull: wrong tensor kinds for DeltaFromS: "
                           ++ show (ftkToStk x) ++ " vs " ++ show zx ++ " and "
                           ++ show sh ++ " vs " ++ show nx
          (FTKS sh x, STKX shx zx) ->
            case ( sameSTK (ftkToStk x) zx
                 , testEquality (shsRank sh) (ssxRank shx) ) of
              (Just Refl, Just Refl) -> FTKX (shCastSX shx sh) x
              _ -> error "shapeDeltaFull: wrong tensor kinds for DeltaFromS"
          (FTKProduct ftk1 ftk2, STKProduct stk1 stk2) ->
            FTKProduct (fromS ftk1 stk1) (fromS ftk2 stk2)
          _ -> error "shapeDeltaFull: wrong tensor kinds for DeltaFromS"
    in fromS (shapeDeltaFull d) (stensorKind @z)
  DeltaSFromR d -> case shapeDeltaFull d of
    FTKR _ x -> FTKS knownShS x
  DeltaSFromX d -> case shapeDeltaFull d of
    FTKX _ x -> FTKS knownShS x

  DeltaXNestR  @_ @sh1 @m d -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @(Replicate m Nothing))
                                  sh (knownShX @sh1))
                      (FTKR (shCvtXR' (shxDropSSX sh (knownShX @sh1))) x)
  DeltaXNestS @_ @sh1 @sh2 d -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @(MapJust sh2)) sh (knownShX @sh1))
                                  (FTKS knownShS x)
  DeltaXNest @_ @sh1 @sh2 d -> case shapeDeltaFull d of
    FTKX sh x -> FTKX (shxTakeSSX (Proxy @sh2) sh (knownShX @sh1))
                      (FTKX (shxDropSSX sh (knownShX @sh1)) x)
  DeltaXUnNestR d -> case shapeDeltaFull d of
    FTKX sh1 (FTKR sh2 x) -> FTKX (sh1 `shxAppend` shCvtRX sh2) x
  DeltaXUnNestS d -> case shapeDeltaFull d of
    FTKX sh1 (FTKS sh2 x) -> FTKX (sh1 `shxAppend` shCvtSX sh2) x
  DeltaXUnNest d -> case shapeDeltaFull d of
    FTKX sh1 (FTKX sh2 x) -> FTKX (sh1 `shxAppend` sh2) x

  DeltaMapAccumR @_ @_ @_ @bShs k accShs bShs _eShs _q _es _df _rf _acc0' _es'
    | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct accShs (buildFTK k bShs)
  DeltaMapAccumL @_ @_ @_ @bShs k accShs bShs _eShs _q _es _df _rf _acc0' _es'
    | Dict <- lemTensorKindOfBuild k (stensorKind @bShs) ->
      FTKProduct accShs (buildFTK k bShs)

shapeDelta :: forall target r n.
              (TensorKind r, KnownNat n)
           => Delta target (TKR2 n r) -> IShR n
shapeDelta t = case shapeDeltaFull t of
  FTKR sh _ -> sh

lengthDelta :: forall target r n.
               (TensorKind r, KnownNat n)
            => Delta target (TKR2 (1 + n) r) -> Int
lengthDelta d = case shapeDelta d of
  ZSR -> error "lengthDelta: impossible pattern needlessly required"
  k :$: _ -> k

shapeDeltaX :: forall target r sh.
               (TensorKind r, KnownShX sh)
            => Delta target (TKX2 sh r) -> IShX sh
shapeDeltaX t = case shapeDeltaFull t of
  FTKX sh _ -> sh


-- * Delta expression identifiers and evaluation state

type role NodeId nominal nominal
data NodeId :: Target -> TensorKindType -> Type where
  NodeId :: forall target y. TensorKind y => Int -> NodeId target y

instance Show (NodeId target y) where
  showsPrec d (NodeId n) =
    showsPrec d n  -- less verbose, more readable

  -- No Eq instance to limit hacks outside this module.
instance DMap.Enum1 (NodeId target) where
  type Enum1Info (NodeId target) = Some (Dict TensorKind)
  fromEnum1 (NodeId @_ @a n) = (n, Some @_ @a Dict)
  toEnum1 n (Some @_ @a Dict) = Some $ NodeId @target @a n

type role InputId nominal nominal
data InputId :: Target -> TensorKindType -> Type where
  InputId :: forall target y. TensorKind y => Int -> InputId target y

deriving instance Show (InputId target y)

instance DMap.Enum1 (InputId target) where
  type Enum1Info (InputId target) = Some (Dict TensorKind)
  fromEnum1 (InputId @_ @a n) = (n, Some @_ @a Dict)
  toEnum1 n (Some @_ @a Dict) = Some $ InputId @target @a n

-- | Wrap non-negative (only!) integers in the `InputId` newtype.
toInputId :: TensorKind y => Int -> InputId f y
toInputId i = assert (i >= 0) $ InputId i

tensorKindFromInputId :: InputId f y -> Dict TensorKind y
tensorKindFromInputId InputId{} = Dict

-- | The state of evaluation. It consists of several maps.
-- The maps indexed by input identifiers and node identifiers
-- eventually store cotangents for their respective nodes.
-- The cotangents are built gradually during the evaluation,
-- by summing cotangent contributions.
--
-- Data invariant:
-- 1. keys nMap == keys dMap
-- 2. key `member` dMap == nMap!key is ...
type role EvalState nominal
data EvalState target = EvalState
  { iMap :: IMap target
      -- ^ eventually, cotangents of objective function inputs
      -- (eventually copied to the vector representing the gradient
      -- of the objective function);
      -- the identifiers need to be contiguous and start at 0
  , dMap :: ADMap target
      -- ^ eventually, cotangents of non-input subterms indexed
      -- by their node identifiers
  , nMap :: DEnumMap (NodeId target) (Delta target)
      -- ^ nodes left to be evaluated;
      -- we can't evaluate them at once, because their other shared copies
      -- may still not be processed, so we'd not take advantage of the sharing
      -- and not take into account the whole summed context when finally
      -- evaluating
  }

type role RepAD nominal nominal
newtype RepAD target y =
  RepAD {unRepAD :: target (ADTensorKind y)}

-- | Delta expressions naturally denote forward derivatives, as encoded
-- in function 'derivativeFromDelta'. However, we are usually more
-- interested in computing gradients, which is what @gradientFromDelta@ does.
-- The two functions are bound by the equation from Lemma 5 from the paper
-- "Provably correct, asymptotically efficient, higher-order reverse-mode
-- automatic differentiation":
--
-- > dt <.> derivativeFromDelta d ds = gradientFromDelta d dt <.> ds
--
-- where @\<.\>@ denotes generalized dot product (multiplying
-- all tensors element-wise and summing the results), @d@ is the top level
-- delta expression from translation of the objective function @f@ to dual
-- numbers, @ds@ belongs to the domain of @f@ and @dt@ to the codomain.
-- In other words, @ds@ is a perturbation (small change) of the arguments
-- of @f@, for which we compute the derivative, and @dt@ is a perturbation
-- of the result of @f@, for which we compute the gradient.
-- We omitted for clarity the @dim@ arguments that are
-- the lengths of vectors of the tensors in the domain of @f@.
--
-- Let's first discuss in detail the semantics of delta-expressions
-- in terms of forward derivatives, since it's more straightforward.
-- Let @r@ be the type of underlying scalars. Let @f@ be a mathematical
-- differentiable function that takes arguments (a collection
-- of finite maps or vectors) of type @HVector r@ and produces
-- a single result of type @r@. Let a dual number counterpart
-- of @f@ applied to a fixed collection of parameters @P@
-- of type @HVector r@ be represented as a Haskell value @b@.
-- Let @d :: Delta0 r@ be the delta expression that is
-- the second component of @b@, let @ds@ belong to @HVector r@.
-- The semantics of @d@ is a linear function from @HVector r@
-- to @r@ that is the derivative of @f@ at point @P@
-- with respect to the perturbation @ds@. The mathematical formula
-- for the derivative follows straightforwardly the syntactic form
-- of the delta expression @d@ (see 'derivativeFromDelta').
--
-- Let's now describe the semantics of a delta expression @d@
-- as the gradient of @f@ at point @P@ with respect to a @dt@ that belongs
-- to @r@. Here the semantics of @d@ is a collection of finite maps
-- (vectors) @v0@, @v1@, ..., corresponding to @HVector r@.
-- The value of @vi@ at index @k@ is the partial derivative
-- of function @f@ at @P@ with respect to its parameter of type @ai@
-- residing at index @k@.
--
-- Consequently, obtaining the gradient amounts to transposing the linear map
-- that is straightforwardly represented by a delta expression. The @eval@
-- functions in @buildFinMaps@ below transpose a linear map and,
-- at the same time, evalute the transposed map, producing its value
-- when applied to afixed argument (contained in the second
-- parameter of @buildFinMaps@).
--
-- Function @gradientFromDelta@ computes the four vectors described above.
-- Requested lengths of the vectors are given in the first few arguments.
-- The delta expression to be evaluated, together with the @dt@ perturbation
-- value (usually set to @1@) are given as arguments.
initEvalState
  :: FullTensorKind x -> EvalState target
initEvalState ftk0 =
  let -- Matches generateDeltaInputs.
      generateDSums :: Int -> FullTensorKind y
                    -> ([DSum (InputId target) (RepM target)], Int)
      generateDSums j ftk  = case ftk of
        FTKScalar @r -> ([InputId j :=> MTKScalarDummy @r], j + 1)
        FTKR shr x | SNat <- shrRank shr
                   , Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          ([InputId j :=> MTKRDummy shr x], j + 1)
        FTKS sh x | Dict <- lemTensorKindOfSTK (ftkToStk x) ->
          withKnownShS sh $
          ([InputId j :=> MTKSDummy sh x], j + 1)
        FTKX{} -> error "TODO"
        FTKProduct ftk1 ftk2 ->
          let (ds1, j1) = generateDSums j ftk1
              (ds2, j2) = generateDSums j1 ftk2
          in (ds1 ++ ds2, j2)
      -- Create finite maps that hold values associated with inputs
      -- and with (possibly shared) term tree nodes.
      -- The former are usually initialized with dummy values so that it's cheap
      -- to check if any update has already been performed to a cell
      -- (allocating big vectors filled with zeros is too costly,
      -- especially if never used in an iteration, and adding to such vectors
      -- and especially using them as cotangent accumulators is wasteful.
      -- We take care to keep the scalar type of the dummy correct,
      -- but a shape is not preserved in a dummy, so it's not shape-correct.
      iMap = DMap.fromDistinctAscList $ fst $ generateDSums 0
             $ aDFTK ftk0
      dMap = DMap.empty
      nMap = DMap.empty
  in EvalState {..}


-- * Reverse pass, transpose/evaluation of the delta expressions

-- The first argument is the evaluation state being modified,
-- the second is the cotangent accumulator that will become an actual
-- cotangent contribution when complete (see below for an explanation)
-- and the third argument is the node to evaluate.
evalRevRuntimeSpecialized
  :: forall n r target.
     (GoodScalar r, KnownNat n, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKR n r))
  -> Delta target (TKR n r)
  -> EvalState target
evalRevRuntimeSpecialized !s !c =
  -- We dispatch on all expected underyling scalar types, which is
  -- necessary to run the correct specialization when unpacking
  -- an existential type. All IfDifferentiable and RowSum instances should
  -- be included in the list of expected underlying scalar types.
  -- If the scalar type is not on the list, performance suffers greatly.
  -- TODO: can I pattern match on (typeRep @r) instead?
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalRevSame @(TKR n Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalRevSame @(TKR n Float) s c
      _ -> const s

evalSRuntimeSpecialized
  :: forall sh r target.
     (GoodScalar r, KnownShS sh, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKS sh r))
  -> Delta target (TKS sh r)
  -> EvalState target
evalSRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalRevSame @(TKS sh Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalRevSame @(TKS sh Float) s c
      _ -> const s

evalXRuntimeSpecialized
  :: forall sh r target.
     (GoodScalar r, KnownShX sh, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind (TKX sh r))
  -> Delta target (TKX sh r)
  -> EvalState target
evalXRuntimeSpecialized !s !c =
  case testEquality (typeRep @r) (typeRep @Double) of
    Just Refl -> evalRevSame @(TKX sh Double) s c
    _ -> case testEquality (typeRep @r) (typeRep @Float) of
      Just Refl -> evalRevSame @(TKX sh Float) s c
      _ -> const s

evalRev
  :: forall y target.
     (TensorKind y, ADReadyNoLet target, ShareTensor target)
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRev !s !c d0 = case d0 of
  -- All constructors that admit a TKProduct kind need to be handled in evalRev
  -- except for DeltaInput that is always constructed only in basic kinds.
  DeltaPair @y1 @y2 d1 d2 | Dict <- lemTensorKindOfAD (stensorKind @y1)
                      , Dict <- lemTensorKindOfAD (stensorKind @y2) ->
    let (c1, c2) = tunpair c
    in evalRev (evalRev s c1 d1) c2 d2
  DeltaProject1 @_ @z d | Dict <- lemTensorKindOfAD (stensorKind @y)
                    , Dict <- lemTensorKindOfAD (stensorKind @z) ->
    case shapeDeltaFull d of
      FTKProduct _ ftk2 ->
        let zero = constantTarget 0 $ aDFTK ftk2
        in evalRev s (tpair c zero) d
    -- if y is, e.g., TKR Int 0, we eval this delta even though we could ignore it
    -- at the price of complicating or duplicating the code slightly more
  DeltaProject2 @x d | Dict <- lemTensorKindOfAD (stensorKind @y)
                 , Dict <- lemTensorKindOfAD (stensorKind @x) ->
    case shapeDeltaFull d of
      FTKProduct ftk1 _ ->
        let zero = constantTarget 0 $ aDFTK ftk1
        in evalRev s (tpair zero c) d
  DeltaFromVector snat stk ld | Refl <- lemBuildOfAD snat stk
                          , Dict <- lemTensorKindOfAD (stensorKind @y) ->
    let cShared = tshare c
        cxs = tunravelToListShare snat (aDSTK stk) cShared
    in foldl' (\ !s2 (cx, d2) -> evalRev s2 cx d2) s
       $ zip cxs (V.toList ld)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRev s (treplicateShare snat (aDSTK stk) c) d
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    evalRev s (tsumShare snat (aDSTK stk) c) d
  DeltaShare n d | Dict <- lemTensorKindOfAD (stensorKind @y) ->
    -- In this context, by construction, @d@ is the dual component
    -- of a dual number term. Let's say that, at this point, evaluation
    -- considers position (node) p out of possibly multiple positions
    -- at which that dual number resides in the whole term tree
    -- of the dual number representation of the objective function.
    -- (Equivalently, considers edges p, one of many leading to the only
    -- node with identifier @n@ in the DAG representing the term).
    -- If so, the @c@ argument of @eval0@ is the cotangent
    -- contribution for position p, that is, the partial derivative
    -- of the objective function with respect to position p.
    --
    -- If there are indeed multiple such positions (the term is shared)
    -- then, over the course of evaluation, cotangent contributions
    -- of them all are gradually accumulated in the finite
    -- maps and eventually their total sum represents the total
    -- influence of the objective function's subcomputation
    -- (more precisely, subgraph of the data flow graph in question)
    -- corresponding to the shared term @DeltaShare n d@. This total
    -- influence over the objective function's behaviour is called
    -- in short the cotangent of the node identifier @n@.
    -- In other words, the cotangent of @n@ is the sum,
    -- over all positions (edges) q in the global delta-expression DAG
    -- that are a reference to node @n@, of the partial derivative
    -- of the objective function with respect to the subcomputation
    -- corresponding to @q@ (meaning, subcomputations denoted by
    -- Haskell terms whose dual components are @Share n ...@).
    --
    -- For @Input@ terms, the eventual lists of cotangents end up
    -- in the cells of the gradient vectors that are the final
    -- result of the evaluation.
    assert (case d of  -- shouold match shareDelta
              DeltaZero{} -> False
              DeltaPair{} -> False
              DeltaInput{} -> False
              DeltaShare{} -> False
              _ -> True)
    $ case DMap.lookup n $ nMap s of
        Just _ ->
          let addc x = RepAD $ addTarget stensorKind c (unRepAD x)
          in s {dMap = DMap.adjust addc n $ dMap s}
        Nothing ->
          let cd = RepAD c
          in s { nMap = DMap.insert n d $ nMap s
               , dMap = DMap.insert n cd $ dMap s }
  DeltaMapAccumR @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            _df rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind bShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
        (c0, crest) = tunpair c
        dacc_des =
          dmapAccumL (Proxy @target)
                     k accShsAD eShsAD (FTKProduct bShsAD
                                                   (FTKProduct accShs eShs))
                     (\dx db_acc_e ->
                        tlet db_acc_e $ \ !db_acc_e1 ->
                          unHFun rf (tpair (tpair dx (tproject1 db_acc_e1))
                                           (tproject2 db_acc_e1)))
                     c0
                     (tpair crest (tpair q es))
        (dacc, des) = tunpair dacc_des
        s2 = evalRev s dacc acc0'
    in evalRev s2 des es'
  DeltaMapAccumL @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            _df rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind bShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
        (c0, crest) = tunpair c
        dacc_des =
          dmapAccumR (Proxy @target)
                     k accShsAD eShsAD (FTKProduct bShsAD
                                                   (FTKProduct accShs eShs))
                     (\dx db_acc_e ->
                        tlet db_acc_e $ \ !db_acc_e1 ->
                          unHFun rf (tpair (tpair dx (tproject1 db_acc_e1))
                                           (tproject2 db_acc_e1)))
                     c0
                     (tpair crest (tpair q es))
        (dacc, des) = tunpair dacc_des
        s2 = evalRev s dacc acc0'
    in evalRev s2 des es'
  DeltaFromS @_ @z (DeltaSFromR @sh @x d)
    | Just Refl <- sameSTK (aDSTK (stensorKind @z))
                           (aDSTK (stensorKind @(TKR2 (Rank sh) x))) ->
      evalRev s c d
  DeltaFromS @_ @z (DeltaSFromX @_ @sh' @x d)
    | Just Refl <- sameSTK (aDSTK (stensorKind @z))
                           (aDSTK (stensorKind @(TKX2 sh' x))) ->
      evalRev s c d
  DeltaFromS @y7 @z d -> case (stensorKind @y7, stensorKind @z) of
    (stky, stkz) | Just Refl <- sameSTK stky stkz -> evalRev s c d
    (STKS ZSS yx@(STKScalar try), STKScalar trz) ->
      case testEquality try trz of
        Just Refl -> case sameSTK yx (aDSTK yx) of
          Just Refl -> evalRev s (sfromScalar c) d
          _ -> s
        Nothing -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKR nx@SNat zx) | Dict <- lemTensorKindOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) nx) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          evalRev s (sfromR c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKS shy yx, STKX shx zx) | Dict <- lemTensorKindOfAD yx ->
      case (sameSTK yx zx, testEquality (shsRank shy) (ssxRank shx)) of
        (Just Refl, Just Refl) ->
          withKnownShS shy $
          withKnownShX shx $
          evalRev s (sfromX c) d
        _ -> error "evalRev: tensor kinds don't match"
    (STKProduct @y1 @y2 stky1 stky2, STKProduct @z1 @z2 stkz1 stkz2)
      | Dict <- lemTensorKindOfSTK stky1
      , Dict <- lemTensorKindOfSTK stky2
      , Dict <- lemTensorKindOfSTK stkz1
      , Dict <- lemTensorKindOfSTK stkz2
      , Dict <- lemTensorKindOfAD stkz1
      , Dict <- lemTensorKindOfAD stkz2 ->
        let (c1, c2) = tunpair c
        in evalRev (evalRev s c1 (DeltaFromS @y1 @z1 $ DeltaProject1 d))
                   c2 (DeltaFromS @y2 @z2 $ DeltaProject2 d)
             -- TODO: costly
    _ -> error "evalRev: wrong tensor kinds"

  _ | Dict <- lemTensorKindOfAD (stensorKind @y) ->
      case sameTensorKind @y @(ADTensorKind y) of
        Just Refl -> evalRevSame s c d0
        _ -> s  -- the constructors remaining here have y that is a non-TKProduct
                -- so if y is equal to ADTensorKind y, the latter has
                -- the () scalar type and so no influence on the derivative.

evalRevSame
  :: forall y target.
     ( TensorKind y, ADReadyNoLet target, ShareTensor target
     , y ~ ADTensorKind y )
  => EvalState target -> target (ADTensorKind y) -> Delta target y
  -> EvalState target
evalRevSame !s !c = \case
  -- All constructors that only admit a non-TKProduct kind
  -- (and the DeltaInput constructor and the vector space constructors)
  -- can be handled here, where the extra
  -- constraint makes it easier.
  DeltaCast @r1 d ->
    evalRev s (toADTensorKindShared (stensorKind @(TKScalar r1))
             $ kcast c) d
  DeltaSFromScalar d -> evalRevSame s (stoScalar c) d
  DeltaInput _ftk i ->
    let cs = repToM stensorKind c
    in s {iMap = DMap.adjust (addRepM cs) i
                 $ iMap s}
    -- This and similar don't need to be runtime-specialized,
    -- because the type of c determines the Num instance for (+).
    -- Note that we can't express sharing by inserting DeltaShare constructors
    -- into iMap, because often sharing needs to work across many
    -- iMap keys. That's why global sharing is used.
  -- By placing these here, we force their derivatives to be zeroed
  -- whenever they are called on non-base types, which they should not ever be.
  -- This is ensured by the types of the three constructors, assuming that
  -- no Num instances are defined for the non-base type tensors.
  DeltaZero{} -> s
  DeltaScale k d -> evalRevSame s (k * c) d
  DeltaAdd d e -> let cShared = tshare c
              in evalRevSame (evalRevSame s cShared d) cShared e

  DeltaIndexR d ix -> evalRevSame s (roneHot (takeShape $ shapeDelta d) c ix) d
  DeltaSum0R d ->
    evalRevSame s (rreplicate0N (shapeDelta d) c) d
  DeltaDot0R v vd ->
    evalRevSame s (v * rreplicate0N (rshape v) c) vd
      -- too slow: evalRevSame s (rmap0N (* (tscalar c)) v) vd
  DeltaScatterR _sh d f ->
    evalRevSame s (rgather (shapeDelta d) c f) d
  DeltaAppendR d e -> case rshape c of
    n :$: _ -> let cShared = tshare c
                   k = lengthDelta d
                   s2 = evalRevSame s (rslice 0 k cShared) d
               in evalRevSame s2 (rslice k (n - k) cShared) e
    ZSR -> error "evalRevSame: impossible pattern needlessly required"
  DeltaSliceR i n d -> case tftk (stensorKind @y) c of
    FTKR (n' :$: rest) x ->
      assert (n' == n `blame` (n', n)) $
      evalRevSame s
               (rconcat
                  [ constantTarget 0 (FTKR (i :$: rest) x)
                  , c
                  , constantTarget 0 (FTKR (lengthDelta d - i - n :$: rest) x) ])
               d
    FTKR ZSR _ -> error "evalRevSame: impossible pattern needlessly required"
  DeltaReverseR d -> evalRevSame s (rreverse c) d
  DeltaTransposeR perm d ->
    let permR = permRInverse perm
    in evalRevSame s (rtranspose permR c) d
  DeltaReshapeR _sh d ->
    evalRevSame s (rreshape (shapeDelta d) c) d
  DeltaGatherR _sh d f ->
    evalRevSame s (rscatter (shapeDelta d) c f) d
  DeltaCastR @r1 @_ @n d ->
    evalRevRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKR n r1))
                               $ rcast c) d
  DeltaZipR d ->
    evalRevSame s (runzip c) d
  DeltaUnzipR d ->
    evalRevSame s (rzip c) d

  DeltaIndexS d ix -> evalRevSame s (soneHot c ix) d
  DeltaSum0S @_ @sh d | SNat <- shsProduct (knownShS @sh) ->
    evalRevSame s (sreplicate0N c) d
  DeltaDot0S @_ @sh v vd | SNat <- shsProduct (knownShS @sh) ->
    evalRevSame s (v * sreplicate0N c) vd
      -- too slow: evalRevSame s (smap0N (* (sscalar c)) v) vd
  DeltaScatterS @_ @_ @shm @shn @shp d f ->
    evalRevSame s (sgather @_ @_ @shm @shn @shp c f) d
  DeltaAppendS @_ @_ @m d e ->
    let cShared = tshare c
        s2 = evalRevSame s (sslice (Proxy @0) Proxy cShared) d
    in evalRevSame s2 (sslice (Proxy @m) Proxy cShared) e
  DeltaSliceS @_ @i d -> case tftk (stensorKind @y) c of
    FTKS _ x -> evalRevSame s (sappend @_ @_ @i
                              (constantTarget 0 (FTKS knownShS x))
                              (sappend
                                 c (constantTarget 0 (FTKS knownShS x)))) d
  DeltaReverseS d -> evalRevSame s (sreverse c) d
  DeltaTransposeS @perm @sh2 perm d ->
    withKnownShS (shsPermutePrefix perm (knownShS @sh2)) $
    permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank permR :~: Rank perm)
        $ evalRevSame s (stranspose permRev c) d
  DeltaReshapeS d ->
    evalRevSame s (sreshape c) d
  DeltaGatherS @_ @_ @shm @shn @shp d f ->
    evalRevSame s (sscatter @_ @_ @shm @shn @shp c f) d
  DeltaCastS @r1 @_ @sh d ->
    evalSRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKS sh r1))
                               $ scast c) d
  DeltaZipS d ->
    evalRevSame s (sunzip c) d
  DeltaUnzipS d ->
    evalRevSame s (szip c) d

  DeltaIndexX{} -> error "TODO"
  DeltaSum0X d ->
    evalRevSame s (xreplicate0N (shapeDeltaX d) c) d
  DeltaDot0X v vd ->
    evalRevSame s (v * xreplicate0N (xshape v) c) vd
      -- too slow: evalRevSame s (smap0N (* (sscalar c)) v) vd
  DeltaScatterX @_ @_ @shm @shn @shp _sh d f ->
    evalRevSame s (xgather @_ @_ @shm @shn @shp (shapeDeltaX d) c f) d
  DeltaAppendX d e -> case (shapeDeltaX d, shapeDeltaX e) of
    (shd@(Nested.SUnknown m :$% rest), she@(Nested.SUnknown n :$% _)) ->
      withSNat m $ \(SNat @m) -> withSNat n $ \(SNat @n) ->
      let cShared =
            tshare $ xmcast (ssxFromShape
                             $ Nested.SKnown (SNat @(m + n)) :$% rest) c
          s2 = evalRevSame s (xmcast (ssxFromShape shd)
                              $ xslice (Proxy @0) (Proxy @m) cShared) d
      in evalRevSame s2 (xmcast (ssxFromShape she)
                         $ xslice (Proxy @m) (Proxy @n) cShared) e
  DeltaSliceX @_ @i @n @k d -> case tftk (stensorKind @y) c of
    FTKX (_ :$% rest) x ->
      evalRevSame s
        (xmcast (ssxFromShape $ Nested.SKnown (SNat @(i + n + k)) :$% rest)
         $ xconcat
          [ constantTarget 0 (FTKX (Nested.SUnknown (valueOf @i) :$% rest) x)
          , xmcast (ssxFromShape $ Nested.SUnknown (valueOf @n) :$% rest) c
          , constantTarget 0 (FTKX (Nested.SUnknown (valueOf @k) :$% rest) x) ])
        d
  DeltaReverseX d -> evalRevSame s (xreverse c) d
  DeltaTransposeX @perm @sh2 perm d ->
    withKnownShX (ssxPermutePrefix perm (knownShX @sh2)) $
    permInverse perm $ \(permRev :: Permutation.Perm permR) _ ->
        gcastWith (unsafeCoerceRefl
                   :: Permutation.PermutePrefix permR (Permutation.PermutePrefix perm sh2) :~: sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank (Permutation.PermutePrefix perm sh2) :~: Rank sh2)
        $ gcastWith (unsafeCoerceRefl
                     :: Rank permR :~: Rank perm)
        $ evalRevSame s (xtranspose permRev c) d
  DeltaReshapeX _sh d ->
    evalRevSame s (xreshape (shapeDeltaX d) c) d
  DeltaGatherX @_ @_ @shm @shn @shp _sh d f ->
    evalRevSame s (xscatter @_ @_ @shm @shn @shp (shapeDeltaX d) c f) d
  DeltaCastX @r1 @_ @sh d ->
    evalXRuntimeSpecialized s (toADTensorKindShared (stensorKind @(TKX sh r1))
                               $ xcast c) d
  DeltaZipX d ->
    evalRevSame s (xunzip c) d
  DeltaUnzipX d ->
    evalRevSame s (xzip c) d

  DeltaSFromR @sh @x (DeltaFromS @y2 d) -> case sameTensorKind @y2 @(TKS2 sh x) of
    Just Refl -> evalRevSame s c d
    _ -> error "evalRevSame: different shapes in DeltaSFromR(DeltaFromS)"
  DeltaSFromR d ->
    evalRevSame s (rfromS c) d
  DeltaSFromX @sh @_ @x (DeltaFromS @y2 d) -> case sameTensorKind @y2 @(TKS2 sh x) of
    Just Refl -> evalRevSame s c d
    _ -> error "evalRevSame: different shapes in DeltaSFromX(DeltaFromS)"
  DeltaSFromX d ->
    evalRevSame s (xfromS c) d

  DeltaXNestR d ->
    evalRevSame s (xunNestR c) d
  DeltaXNestS d ->
    evalRevSame s (xunNestS c) d
  DeltaXNest d ->
    evalRevSame s (xunNest c) d
  DeltaXUnNestR d ->
    evalRevSame s (xnestR knownShX c) d
  DeltaXUnNestS d ->
    evalRevSame s (xnestS knownShX c) d
  DeltaXUnNest d ->
    evalRevSame s (xnest knownShX c) d

  d -> evalRev s c d
    -- the remaining constructors are already handled in evalRev, so let's use that

evalRevFromnMap :: forall target. (ADReadyNoLet target, ShareTensor target)
             => EvalState target -> EvalState target
evalRevFromnMap s@EvalState{nMap, dMap} =
  -- We discharge the non-vector cases before the vector ones, because
  -- the latter tend to create and store more cases and so enlarge
  -- the working set of cases.
  case DMap.maxViewWithKey nMap of
    Just (n@(NodeId @_ @y _) :=> d, nMap2) ->
      let s2 = s {nMap = nMap2}
          errorMissing :: a
          errorMissing = error $ "evalRevFromnMap: missing cotangent " ++ show n
          s3 = case stensorKind @y of
            STKR @n SNat (STKScalar @r _) -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalRevRuntimeSpecialized @n @r s2 c d
              Nothing -> errorMissing
            STKS @sh sh (STKScalar @r _) ->
              withKnownShS sh $ case DMap.lookup n dMap of
                Just (RepAD c) -> evalSRuntimeSpecialized @sh @r s2 c d
                Nothing -> errorMissing
            STKX @sh sh (STKScalar @r _) ->
              withKnownShX sh $ case DMap.lookup n dMap of
                Just (RepAD c) -> evalXRuntimeSpecialized @sh @r s2 c d
                Nothing -> errorMissing
            _ -> case DMap.lookup n dMap of
              Just (RepAD c) -> evalRev s2 c d
              Nothing -> errorMissing
      in evalRevFromnMap s3
    Nothing -> s  -- loop ends

{-
        -- The general case is given as the last one below,
        -- but for a few constructors it's faster to inline @evalRev@ instead.
        -- BTW, such an optimization doesn't really belong in the simplified
        -- horde-ad and no consistent benefit should be expected here.
        DeltaIndex0 ZeroR{} _ _ -> s  -- shortcut
        DeltaIndex0 (InputR i) ixs' sh ->
          let ixs = indexToList ixs'
              f v = if isTensorDummy v
                    then treplicate0ND sh 0 `OD.update` [(ixs, c)]
                    else v `OD.update` [(ixs, v `rindex0D` ixs + c)]
          in s {iMap = DMap.adjust f i $ iMap s}
        DeltaIndex0 (ShareR n d) ixs' sh ->
          let ixs = indexToList ixs'
          in case DMap.lookup n $ nMap s of
            Just (DynamicRanked _) ->
              let f v = v `OD.update` [(ixs, v `rindex0D` ixs + c)]
              in s {dMap = DMap.adjust f n $ dMap s}
                -- This would be an asymptotic optimization compared to
                -- the general case below, if not for the non-mutable update,
                -- which implies copying the whole @v@ vector,
                -- so it's only several times faster (same allocation,
                -- but not adding to each cell of @v@).
            Nothing ->
              let v = treplicate0ND sh 0 `OD.update` [(ixs, c)]
              in s { nMap = DMap.insert n (DynamicRanked d) $ nMap s
                   , dMap = DMap.insert n v $ dMap s }
            _ -> error "evalRevFromnMap: corrupted nMap"
-}


-- * Forward derivative computation from the delta expressions

-- | Forward derivative computation via forward-evaluation of delta-expressions
-- (which is surprisingly competitive to the direct forward method,
-- until the allocation of deltas gets large enough to affect cache hits).
-- This is the directional derivative, calculated for the point,
-- at which the delta expression was computed (which is the point
-- represented by the parameters of the objective function and used
-- to compute it's dual number result) and along the direction vector(s)
-- given in the last parameter called @ds@.
--
-- This mimics the reverse derivative code, but in reverse. Perhaps this can be
-- simplified, but the obvious simplest formulation does not honour sharing
-- and evaluates shared subexpressions repeatedly, so this state-passing
-- formulation is adopted.
evalFwd
  :: forall target y.
     (ADReadyNoLet target, ShareTensor target, TensorKind y)
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
evalFwd params s d0 = case d0 of
  DeltaPair @y1 @y2 d1 d2 | Dict <- lemTensorKindOfAD (stensorKind @y1)
                      , Dict <- lemTensorKindOfAD (stensorKind @y2) ->
    let (s2, t) = evalFwd params s d1
        (s3, u) = evalFwd params s2 d2
    in (s3, tpair t u)
  DeltaProject1 @_ @z d | Dict <- lemTensorKindOfAD (stensorKind @y)
                    , Dict <- lemTensorKindOfAD (stensorKind @z) ->
    let (s2, v) = evalFwd params s d
    in (s2, tproject1 v)
  DeltaProject2 @x d | Dict <- lemTensorKindOfAD (stensorKind @y)
                 , Dict <- lemTensorKindOfAD (stensorKind @x) ->
    let (s2, v) = evalFwd params s d
    in (s2, tproject2 v)
  DeltaFromVector snat stk lsd | Refl <- lemBuildOfAD snat stk ->
    let (s2, l) = mapAccumL (evalFwd params) s lsd
    in (s2, tfromVectorShare snat (aDSTK stk) l)
  DeltaSum snat stk d | Refl <- lemBuildOfAD snat stk ->
    let (s2, t) = evalFwd params s d
    in (s2, tsumShare snat (aDSTK stk) t)
  DeltaReplicate snat stk d | Refl <- lemBuildOfAD snat stk ->
    let (s2, t) = evalFwd params s d
    in (s2, treplicateShare snat (aDSTK stk) t)
  DeltaInput _ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, toADTensorKindShared stensorKind $ evalRepM dtk)
      Nothing -> error "evalFwd: missing input"
  DeltaShare n d | Dict <- lemTensorKindOfAD (stensorKind @y) ->
    case DMap.lookup n s of
      Just e1 -> (s, unRepAD e1)
      Nothing ->
        let (s2, cRaw) = evalFwd params s d
            cShared = tshare cRaw
            cd = RepAD cShared
              -- cRaw is shared, because it's put into the map and then
              -- potentially looked up many times, so it'd get duplicated
            s3 = DMap.insert n cd s2
        in (s3, cShared)

  DeltaMapAccumR @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            df _rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind accShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
        (s2, cacc0) = evalFwd params s acc0'
        (s3, ces) = evalFwd params s2 es'
    in (s3, dmapAccumR (Proxy @target)
                       k accShsAD bShsAD (FTKProduct eShsAD
                                                     (FTKProduct accShs eShs))
                       (\dacc de_acc_e ->
                        tlet de_acc_e $ \ !de_acc_e1 ->
                          unHFun df (tpair (tpair dacc (tproject1 de_acc_e1))
                                           (tproject2 de_acc_e1)))
                       cacc0
                       (tpair ces (tpair q es)))
  DeltaMapAccumL @_ @_ @accShs @bShs @eShs
            k accShs bShs eShs
            q es
            df _rf acc0' es'
   | Dict <- lemTensorKindOfAD (stensorKind @accShs)
   , Dict <- lemTensorKindOfAD (stensorKind @bShs)
   , Dict <- lemTensorKindOfAD (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @accShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @eShs)
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind accShs))
   , Dict <- lemTensorKindOfBuild k (stensorKind @(ADTensorKind eShs))
   , Refl <- lemBuildOfAD k (stensorKind @bShs)
   , Refl <- lemBuildOfAD k (stensorKind @eShs) ->
    let accShsAD = aDFTK accShs
        bShsAD = aDFTK bShs
        eShsAD = aDFTK eShs
        (s2, cacc0) = evalFwd params s acc0'
        (s3, ces) = evalFwd params s2 es'
    in (s3, dmapAccumL (Proxy @target)
                       k accShsAD bShsAD (FTKProduct eShsAD
                                                     (FTKProduct accShs eShs))
                       (\dacc de_acc_e ->
                        tlet de_acc_e $ \ !de_acc_e1 ->
                          unHFun df (tpair (tpair dacc (tproject1 de_acc_e1))
                                           (tproject2 de_acc_e1)))
                       cacc0
                       (tpair ces (tpair q es)))
  DeltaFromS @_ @z (DeltaSFromR @sh @x d)
    | Just Refl <- sameSTK (aDSTK (stensorKind @z))
                           (aDSTK (stensorKind @(TKR2 (Rank sh) x))) ->
      evalFwd params s d
  DeltaFromS @_ @z (DeltaSFromX @_ @sh' @x d)
    | Just Refl <- sameSTK (aDSTK (stensorKind @z))
                           (aDSTK (stensorKind @(TKX2 sh' x))) ->
      evalFwd params s d
  DeltaFromS @y2 @z d | Dict <- lemTensorKindOfAD (stensorKind @y2)
                 , Dict <- lemTensorKindOfAD (stensorKind @z) ->
    second tfromSShare $ evalFwd params s d

  _ | Dict <- lemTensorKindOfAD (stensorKind @y) ->
      case sameTensorKind @y @(ADTensorKind y) of
        Just Refl -> evalFwdSame params s d0
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)

evalFwdSame
  :: forall target y.
     ( TensorKind y, ADReadyNoLet target, ShareTensor target
     , y ~ ADTensorKind y )
  => IMap target -> ADMap target -> Delta target y
  -> (ADMap target, target (ADTensorKind y))
evalFwdSame params s = \case
  d0@(DeltaCast @r1 d)
    | Dict <- lemTensorKindOfAD (stensorKind @(TKScalar r1)) ->
      case sameTensorKind @(TKScalar r1) @(ADTensorKind (TKScalar r1)) of
        Just Refl -> second kcast $ evalFwdSame params s d
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  DeltaSFromScalar d -> let (s2, t) = evalFwdSame params s d
                   in (s2, sfromScalar t)
  DeltaInput _ftk inputId ->
    case DMap.lookup inputId params of
      Just dtk -> (s, evalRepM dtk)
      Nothing -> error "evalFwdSame: missing input"
  -- See the comment about these three in evalRevSame.
  DeltaZero ftk -> (s, constantTarget 0 $ aDFTK ftk)
  DeltaScale k d -> second (* k) $ evalFwdSame params s d
  DeltaAdd d e -> let (s2, t) = evalFwdSame params s d
                      (s3, u) = evalFwdSame params s2 e
                  in (s3, t + u)

  DeltaIndexR d ix -> second (`rindex` ix) $ evalFwdSame params s d
  DeltaSum0R (DeltaZero (FTKR _ x)) -> (s, constantTarget 0 (FTKR ZSR x))
  DeltaSum0R d -> second rsum0 $ evalFwdSame params s d
  DeltaDot0R _ DeltaZero{} -> (s, rscalar 0)
  DeltaDot0R v d -> second (rdot0 v) $ evalFwdSame params s d
  DeltaScatterR sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, rscatter sh t f)
  DeltaAppendR d e ->
    let (s2, t) = evalFwdSame params s d
        (s3, u) = evalFwdSame params s2 e
    in (s3, rappend t u)
  DeltaSliceR i n d -> second (rslice i n) $ evalFwdSame params s d
  DeltaReverseR d -> second rreverse $ evalFwdSame params s d
  DeltaTransposeR perm d -> second (rtranspose perm) $ evalFwdSame params s d
  DeltaReshapeR sh d -> second (rreshape sh) $ evalFwdSame params s d
  DeltaGatherR sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, rgather sh t f)
  d0@(DeltaCastR @r1 @_ @n d)
    | Dict <- lemTensorKindOfAD (stensorKind @(TKR n r1)) ->
      case sameTensorKind @(TKR n r1) @(ADTensorKind (TKR n r1)) of
        Just Refl -> second rcast $ evalFwdSame params s d
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  DeltaZipR d -> second rzip $ evalFwdSame params s d
  DeltaUnzipR d -> second runzip $ evalFwdSame params s d
-- Not needed, because we take only the i-th component of the vector,
-- so v is not copied.
--  in (s2, rfromD $ tunvector v) V.! i)

  DeltaIndexS d ix -> second (`sindex` ix) $ evalFwdSame params s d
  DeltaSum0S (DeltaZero (FTKS _ x)) -> (s, constantTarget 0 (FTKS ZSS x))
  DeltaSum0S d -> second ssum0 $ evalFwdSame params s d
  DeltaDot0S _ DeltaZero{} -> (s, srepl 0)
  DeltaDot0S v d -> second (sdot0 v) $ evalFwdSame params s d
  DeltaScatterS @_ @_ @shm @shn @shp d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, sscatter @_ @_ @shm @shn @shp t f)
  DeltaAppendS d e ->
    let (s2, t) = evalFwdSame params s d
        (s3, u) = evalFwdSame params s2 e
    in (s3, sappend t u)
  DeltaSliceS @_ @i d -> second (sslice (Proxy @i) Proxy) $ evalFwdSame params s d
  DeltaReverseS d -> second sreverse $ evalFwdSame params s d
  DeltaTransposeS perm d -> second (stranspose perm)
                       $ evalFwdSame params s d
  DeltaReshapeS d -> second sreshape $ evalFwdSame params s d
  DeltaGatherS @_ @_ @shm @shn @shp d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, sgather @_ @_ @shm @shn @shp t f)
  d0@(DeltaCastS @r1 @_ @sh d)
    | Dict <- lemTensorKindOfAD (stensorKind @(TKS sh r1)) ->
      case sameTensorKind @(TKS sh r1) @(ADTensorKind (TKS sh r1)) of
        Just Refl -> second scast $ evalFwdSame params s d
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  DeltaZipS d -> second szip $ evalFwdSame params s d
  DeltaUnzipS d -> second sunzip $ evalFwdSame params s d
-- Not needed, because we take only the i-th component of the vector,
-- so v is not copied.
--  in (s2, sfromD $ tunvector v V.! i)

  DeltaIndexX d ix -> second (`xindex` ix) $ evalFwdSame params s d
  DeltaSum0X (DeltaZero (FTKX _ x)) -> (s, constantTarget 0 (FTKX ZSX x))
  DeltaSum0X d -> second xsum0 $ evalFwdSame params s d
  DeltaDot0X _ DeltaZero{} -> (s, xrepl ZSX 0)
  DeltaDot0X v d -> second (xdot0 v) $ evalFwdSame params s d
  DeltaScatterX @_ @_ @shm @shn @shp sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, xscatter @_ @_ @shm @shn @shp sh t f)
  DeltaAppendX d e ->
    let (s2, t) = evalFwdSame params s d
        (s3, u) = evalFwdSame params s2 e
    in (s3, xappend t u)
  DeltaSliceX @_ @i d -> second (xslice (Proxy @i) Proxy) $ evalFwdSame params s d
  DeltaReverseX d -> second xreverse $ evalFwdSame params s d
  DeltaTransposeX perm d -> second (xtranspose perm)
                       $ evalFwdSame params s d
  DeltaReshapeX sh2 d -> second (xreshape sh2) $ evalFwdSame params s d
  DeltaGatherX @_ @_ @shm @shn @shp sh d f ->
    let (s2, t) = evalFwdSame params s d
    in (s2, xgather @_ @_ @shm @shn @shp sh t f)
  d0@(DeltaCastX @r1 @_ @sh d)
    | Dict <- lemTensorKindOfAD (stensorKind @(TKX sh r1)) ->
      case sameTensorKind @(TKX sh r1) @(ADTensorKind (TKX sh r1)) of
        Just Refl -> second xcast $ evalFwdSame params s d
        _ -> (s, constantTarget 0 $ aDFTK $ shapeDeltaFull d0)
  DeltaZipX d -> second xzip $ evalFwdSame params s d
  DeltaUnzipX d -> second xunzip $ evalFwdSame params s d

  DeltaSFromR @sh @x (DeltaFromS @y2 d) -> case sameTensorKind @y2 @(TKS2 sh x) of
    Just Refl -> evalFwdSame params s d
    _ -> error "evalFwdSame: different shapes in DeltaSFromR(DeltaFromS)"
  DeltaSFromR d -> second sfromR $ evalFwdSame params s d
  DeltaSFromX @sh @_ @x (DeltaFromS @y2 d) -> case sameTensorKind @y2 @(TKS2 sh x) of
    Just Refl -> evalFwdSame params s d
    _ -> error "evalFwdSame: different shapes in DeltaSFromX(DeltaFromS)"
  DeltaSFromX d -> second sfromX $ evalFwdSame params s d

  DeltaXNestR d -> second (xnestR knownShX) $ evalFwdSame params s d
  DeltaXNestS d -> second (xnestS knownShX) $ evalFwdSame params s d
  DeltaXNest d -> second (xnest knownShX) $ evalFwdSame params s d
  DeltaXUnNestR d -> second xunNestR $ evalFwdSame params s d
  DeltaXUnNestS d -> second xunNestS $ evalFwdSame params s d
  DeltaXUnNest d -> second xunNest $ evalFwdSame params s d

  d -> evalFwd params s d
