{-# LANGUAGE CPP, DataKinds, DeriveAnyClass, DeriveGeneric, DerivingStrategies,
             GADTs, GeneralizedNewtypeDeriving, KindSignatures, RankNTypes,
             StandaloneDeriving, UnboxedTuples #-}
#if !MIN_VERSION_base(4,16,0)
{-# LANGUAGE IncoherentInstances #-}
#endif
#if defined(VERSION_ghc_typelits_natnormalise)
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
#endif
-- | The second component of our rendition of dual numbers:
-- delta expressions, with their semantics.
-- Neel Krishnaswami calls them \"sparse vector expressions\",
-- and indeed even in the simplest case of an objective function
-- defined on scalars only, the codomain of the function that computes
-- gradients from such delta expressions is a set of vectors, because
-- the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
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
-- This is an internal low-level API, while the module @DualClass@
-- is an intermediate mid-level API that generates 'NodeId' identifiers
-- and provides a generalization to other kinds of second components
-- of dual numbers, e.g., the same as primal component for fast computation
-- of forward derivatives (because @derivativeFromDelta@ below,
-- computing derivatives from delta-expressions, is slow once
-- the expressions grow large enough to affect cache misses).
module HordeAd.Internal.Delta
  ( -- * Abstract syntax trees of the delta expressions
    Delta0 (..), Delta1 (..), Delta2 (..), DeltaX (..), DeltaS (..)
  , -- * Delta expression identifiers
    NodeId(..), InputId, toInputId
  , -- * Evaluation of the delta expressions
    DeltaDt (..), Domain0, Domain1, Domain2, DomainX, Domains(..), nullDomains
  , gradientFromDelta, derivativeFromDelta
  , isTensorDummy, toVectorOrDummy, toMatrixOrDummy
  , toShapedOrDummy, toDynamicOrDummy, atIndexInTensor
  ) where

import Prelude

import           Control.DeepSeq (NFData)
import           Control.Exception (assert)
import           Control.Monad (liftM2, unless, zipWithM_)
import           Control.Monad.ST.Strict (ST, runST)
import qualified Data.Array.Convert
import qualified Data.Array.Dynamic as OTB
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Internal
import qualified Data.Array.Internal.DynamicG
import qualified Data.Array.Internal.DynamicS
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import qualified Data.EnumMap.Strict as EM
import           Data.Kind (Type)
import           Data.List.Index (imapM_)
import           Data.Primitive (Prim)
import           Data.Proxy (Proxy (Proxy))
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import           Data.STRef.Unboxed (STRefU, newSTRefU, readSTRefU, writeSTRefU)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           GHC.Generics (Generic)
import           GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector, (<.>))
import qualified Numeric.LinearAlgebra as LA
import qualified Numeric.LinearAlgebra.Devel
import           Text.Show.Functions ()

import qualified HordeAd.Internal.MatrixOuter as MO
import           HordeAd.Internal.OrthotopeOrphanInstances ()

-- * Abstract syntax trees of the delta expressions

-- | For each choice of the underlying scalar type @r@,
-- we have several primitive differentiable types based on the scalar:
-- the scalar type @r@ itself, @Vector r@, @Matrix r@ and tensors.
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
-- The `NodeId` identifier that appears in a @Let0 n d@ expression
-- is the unique identity stamp of subterm @d@, that is, there is
-- no different term @e@ such that @Let0 n e@ appears in any delta
-- expression term in memory during the same run of an executable.
-- The subterm identity is used to avoid evaluating shared
-- subterms repeatedly in gradient and derivative computations.
-- The identifier also represents data dependencies among terms
-- for the purpose of gradient and derivative computation. Computation for
-- a term may depend only on data obtained from terms with lower value
-- of their node identifiers. Such data dependency determination
-- agrees with the subterm relation, but is faster than traversing
-- the term tree in order to determine the relation of terms.
-- There is one exception to the subterm data dependency rule:
-- any term containing a function (e.g., a @Build1@ node)
-- may depend on terms generated by applying the function,
-- regardless of their node identifiers (which in our implementation
-- are going to be larger than their ancestors').
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
data Delta0 r =
    Zero0
  | Input0 (InputId r)
  | Scale0 r (Delta0 r)
  | Add0 (Delta0 r) (Delta0 r)
  | Let0 NodeId (Delta0 r)

  | SumElements10 (Delta1 r) Int  -- ^ see Note [SumElements10]
  | SumElements20 (Delta2 r) (Int, Int)
  | SumElementsX0 (DeltaX r) OT.ShapeL
  | Index10 (Delta1 r) Int Int  -- ^ second integer is the length of the vector
  | Index20 (Delta2 r) (Int, Int) (Int, Int)
  | IndexX0 (DeltaX r) [Int] OT.ShapeL

  | Dot0 (Vector r) (Delta1 r)  -- ^ Dot0 v vd == SumElements10 (Scale1 v vd) n

  | FromX0 (DeltaX r)  -- ^ one of many conversions
  | FromS0 (DeltaS '[] r)

deriving instance (Show r, Numeric r) => Show (Delta0 r)

-- | This is the grammar of delta-expressions at tensor rank 1, that is,
-- at vector level.
data Delta1 r =
    Zero1
  | Input1 (InputId (Vector r))
  | Scale1 (Vector r) (Delta1 r)
  | Add1 (Delta1 r) (Delta1 r)
  | Let1 NodeId (Delta1 r)

  | FromList1 [Delta0 r]
  | FromVector1 (Data.Vector.Vector (Delta0 r))  -- ^ "unboxing" conversion
  | Konst1 (Delta0 r) Int  -- ^ length; needed only for forward derivative
  | Append1 (Delta1 r) Int (Delta1 r)
      -- ^ second argument is the length of the first argument
  | Slice1 Int Int (Delta1 r) Int  -- ^ last integer is the length of argument
  | SumRows1 (Delta2 r) Int  -- ^ the integer is the number of columns
  | SumColumns1 (Delta2 r) Int  -- ^ the integer is the number of rows

  | M_VD1 (Matrix r)
          (Delta1 r)  -- ^ M_VD1 m vd == SumRows1 (M_MD2 m (AsRow2 vd))
  | MD_V1 (Delta2 r)
          (Vector r)  -- ^ MD_V1 md v == SumRows1 (MD_M2 md (asRow v))

  | FromX1 (DeltaX r)
  | forall len. KnownNat len
    => FromS1 (DeltaS '[len] r)

    -- unsorted and undocumented yet
  | Reverse1 (Delta1 r)
  | Flatten1 Int Int (Delta2 r)
  | FlattenX1 OT.ShapeL (DeltaX r)
  | forall sh. OS.Shape sh
    => FlattenS1 (DeltaS sh r)
  | Build1 Int (Int -> Delta0 r)
      -- ^ the first argument is length; needed only for forward derivative

deriving instance (Show r, Numeric r) => Show (Delta1 r)

-- | This is the grammar of delta-expressions at tensor rank 2, that is,
-- at matrix level.
data Delta2 r =
    Zero2
  | Input2 (InputId (Matrix r))
  | Scale2 (Matrix r) (Delta2 r)
  | Add2 (Delta2 r) (Delta2 r)
  | Let2 NodeId (Delta2 r)

  | FromList2 (Int, Int) [Delta0 r]
  | FromVector2 (Int, Int) (Data.Vector.Vector (Delta0 r))
  | FromRows2 (Data.Vector.Vector (Delta1 r))
  | FromColumns2 (Data.Vector.Vector (Delta1 r))
  | Konst2 (Delta0 r) (Int, Int)  -- ^ size; needed only for forward derivative
  | Transpose2 (Delta2 r)
  | M_MD2 (Matrix r) (Delta2 r)  -- ^ matrix-(matrix-expression) multiplication
  | MD_M2 (Delta2 r) (Matrix r)  -- ^ (matrix-expression)-matrix multiplication
  | RowAppend2 (Delta2 r) Int (Delta2 r)  -- ^ row-length of first argument
  | ColumnAppend2 (Delta2 r) Int (Delta2 r)  -- ^ col-length of first argument
  | RowSlice2 Int Int (Delta2 r) Int  -- ^ last arg is row-length of the matrix
  | ColumnSlice2 Int Int (Delta2 r) Int  -- ^ column-length of the matrix

  | AsRow2 (Delta1 r)  -- ^ AsRow2 vd == FromRows2 (V.replicate n vd)
  | AsColumn2 (Delta1 r)  -- ^ AsColumn2 vd == FromColumns2 (V.replicate n vd)

  | FromX2 (DeltaX r)
  | forall rows cols. (KnownNat rows, KnownNat cols)
    => FromS2 (DeltaS '[rows, cols] r)

    -- unsorted and undocumented yet
  | Flipud2 (Delta2 r)
  | Fliprl2 (Delta2 r)
  | Reshape2 Int (Delta1 r)
  | Conv2 (Matrix r) (Delta2 r)
  | Build2 (Int, Int) ((Int, Int) -> Delta0 r)
      -- ^ the first argument is size; needed only for forward derivative

deriving instance (Show r, Numeric r) => Show (Delta2 r)

-- | This is the grammar of delta-expressions at arbitrary tensor rank.
--
-- Warning: not tested enough nor benchmarked.
data DeltaX r =
    ZeroX
  | InputX (InputId (OT.Array r))
  | ScaleX (OT.Array r) (DeltaX r)
  | AddX (DeltaX r) (DeltaX r)
  | LetX NodeId (DeltaX r)

  | FromListX OT.ShapeL [Delta0 r]
  | FromVectorX OT.ShapeL (Data.Vector.Vector (Delta0 r))
  | KonstX (Delta0 r) OT.ShapeL  -- ^ size; needed only for forward derivative
  | AppendX (DeltaX r) Int (DeltaX r)
      -- ^ Append two arrays along the outermost dimension.
      -- All dimensions, except the outermost, must be the same.
      -- The integer argument is the outermost size of the first array.
  | SliceX Int Int (DeltaX r) Int
      -- ^ Extract a slice of an array along the outermost dimension.
      -- The extracted slice must fall within the dimension.
      -- The last argument is the outermost size of the argument array.
  | IndexX (DeltaX r) Int Int
      -- ^ The sub-tensors at the given index of the outermost dimension.
      -- The second integer is the length of the dimension.
  | RavelFromListX [DeltaX r]
      -- ^ Create a tensor from a list treated as the outermost dimension.
  | ReshapeX OT.ShapeL OT.ShapeL (DeltaX r)
      -- ^ Change the shape of the tensor from the first to the second.

  | From0X (Delta0 r)
  | From1X (Delta1 r)
  | From2X (Delta2 r) Int
  | forall sh. OS.Shape sh
    => FromSX (DeltaS sh r)

  | BuildX OT.ShapeL ([Int] -> Delta0 r)

deriving instance (Show r, Numeric r) => Show (DeltaX r)

-- | This is the grammar of delta-expressions at arbitrary tensor rank,
-- the fully typed Shaped version.
--
-- Warning: not tested enough nor benchmarked.
data DeltaS :: [Nat] -> Type -> Type where
  ZeroS :: DeltaS sh r
  InputS :: InputId (OS.Array sh r) -> DeltaS sh r
  ScaleS :: OS.Array sh r -> DeltaS sh r -> DeltaS sh r
  AddS :: DeltaS sh r -> DeltaS sh r -> DeltaS sh r
  LetS :: NodeId -> DeltaS sh r -> DeltaS sh r

  FromListS :: [Delta0 r] -> DeltaS sh r
  FromVectorS :: Data.Vector.Vector (Delta0 r) -> DeltaS sh r
  KonstS :: Delta0 r -> DeltaS sh r
  AppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
          => DeltaS (m ': sh) r -> DeltaS (n ': sh) r
          -> DeltaS ((m + n) ': sh) r
    -- ^ Append two arrays along the outermost dimension.
  SliceS :: (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
         => Proxy i -> Proxy n -> DeltaS (i + n + k ': rest) r
         -> DeltaS (n ': rest) r
    -- ^ Extract a slice of an array along the outermost dimension.
  IndexS :: (KnownNat ix, KnownNat k, OS.Shape rest)
         => DeltaS (ix + 1 + k ': rest) r -> Proxy ix -> DeltaS rest r
    -- ^ The sub-tensors at the given index of the outermost dimension.
  RavelFromListS :: (KnownNat k, OS.Shape rest)
                 => [DeltaS rest r] -> DeltaS (k : rest) r
    -- ^ Create a tensor from a list treated as the outermost dimension.
  ReshapeS :: (OS.Shape sh, OS.Shape sh', OS.Size sh ~ OS.Size sh')
           => DeltaS sh r -> DeltaS sh' r
    -- ^ Change the shape of the tensor.

  From0S :: Delta0 r -> DeltaS '[] r
  From1S :: Delta1 r -> DeltaS '[n] r
  From2S :: KnownNat cols
         => Proxy cols -> Delta2 r -> DeltaS '[rows, cols] r
  FromXS :: DeltaX r -> DeltaS sh r

  BuildS :: ([Int] -> Delta0 r) -> DeltaS sh r

instance Show (DeltaS sh r) where
  show _ = "a DeltaS delta expression"


-- * Delta expression identifiers

newtype NodeId = NodeId {fromNodeId :: Int}
  deriving newtype (Enum, Prim)
    -- The Prim instance conversions take lots of time when old-time profiling,
    -- but are completely optimized away in normal builds.
    -- No Eq instance to limit hacks outside this module.

instance Show NodeId where
  show (NodeId n) = show n  -- to keep debug printouts readable

newtype InputId a = InputId Int
  deriving Show
    -- No Eq instance to limit hacks outside this module.

-- | Wrap non-negative (only!) integers in the `InputId` newtype.
toInputId :: Int -> InputId a
toInputId i = assert (i >= 0) $ InputId i

newtype DeltaId a = DeltaId Int
  deriving newtype (Show, Prim)
    -- No Eq instance to limit hacks outside this module.

-- The key property is that it preserves the phantom type.
succDeltaId :: DeltaId a -> DeltaId a
succDeltaId (DeltaId i) = DeltaId (succ i)


-- * Evaluation of the delta expressions

-- | Helper definitions to shorten type signatures. @Domains@, among other
-- roles, is the internal representation of domains of objective functions.
type Domain0 r = Vector r

type Domain1 r = Data.Vector.Vector (Vector r)

type Domain2 r = Data.Vector.Vector (Matrix r)

type DomainX r = Data.Vector.Vector (OT.Array r)

data Domains r = Domains
  { domains0 :: Domain0 r
  , domains1 :: Domain1 r
  , domains2 :: Domain2 r
  , domainsX :: DomainX r
  }
  deriving (Show, Generic, NFData)

nullDomains :: Numeric r => Domains r -> Bool
nullDomains Domains{..} =
  V.null domains0 && V.null domains1 && V.null domains2 && V.null domainsX

-- | The main input of the differentiation functions:
-- the delta expression to be differentiated and the dt perturbation
-- (small change) of the objective function codomain, for which we compute
-- the gradient.
data DeltaDt r =
    DeltaDt0 r (Delta0 r)
  | DeltaDt1 (Vector r) (Delta1 r)
  | DeltaDt2 (Matrix r) (Delta2 r)
  | DeltaDtX (OT.Array r) (DeltaX r)
  | forall sh. OS.Shape sh
    => DeltaDtS (OS.Array sh r) (DeltaS sh r)

-- | Node identifiers left to be evaluated, with their corresponding
-- index into @dMap@ finite map and delta expression.
-- We can't evaluate them at once, because their other shared copies
-- may still not be processed, so we'd not take advantage of the sharing
-- and not take into account the whole summed context when finally evaluating.
data DeltaBinding r =
    DeltaBinding0 (DeltaId r) (Delta0 r)
  | DeltaBinding1 (DeltaId (Vector r)) (Delta1 r)
  | DeltaBinding2 (DeltaId (Matrix r)) (Delta2 r)
  | DeltaBindingX (DeltaId (OT.Array r)) (DeltaX r)
  | forall sh. OS.Shape sh
    => DeltaBindingS (DeltaId (OT.Array r)) (DeltaS sh r)

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
-- We omitted for clarity the @dim0@, @dim1@, @dim2@ and @dimX@ arguments
-- that are the lengths of vectors of the tensors in the domain of @f@.
--
-- Let's first discuss in detail the semantics of delta-expressions
-- in terms of forward derivatives, since it's more straightforward.
-- Let @r@ be the type of underlying scalars. Let @f@ be a mathematical
-- differentiable function that takes arguments (a collection
-- of finite maps or vectors) of type @Domains r@ and produces
-- a single result of type @r@. Let a dual number counterpart
-- of @f@ applied to a fixed collection of parameters @P@
-- of type @Domains r@ be represented as a Haskell value @b@.
-- Let @d :: Delta0 r@ be the delta expression that is
-- the second component of @b@, let @ds@ belong to @Domains r@.
-- The semantics of @d@ is a linear function from @Domains r@
-- to @r@ that is the derivative of @f@ at point @P@
-- with respect to the perturbation @ds@. The mathematical formula
-- for the derivative follows straightforwardly the syntactic form
-- of the delta expression @d@ (see 'derivativeFromDelta').
--
-- Let's now describe the semantics of a delta expression @d@
-- as the gradient of @f@ at point @P@ with respect to a @dt@ that belongs
-- to @r@. Here the semantics of @d@ is a collection of finite maps
-- (vectors) @v0@, @v1@, ..., corresponding to @Domains r@.
-- The value of @vi@ at index @k@ is the partial derivative
-- of function @f@ at @P@ with respect to its parameter of type @ai@
-- residing at index @k@.
--
-- Function @gradientFromDelta@ computes the four vectors described above.
-- Requested lengths of the vectors are given in the first few arguments.
-- The delta expression to be evaluated, together with the @dt@ perturbation
-- value (usually set to @1@) is given in the @DeltaDt r@ parameter.
gradientFromDelta
  :: (Eq r, Numeric r, Num (Vector r))
  => Int -> Int -> Int -> Int -> DeltaDt r
  -> Domains r
gradientFromDelta dim0 dim1 dim2 dimX deltaDt =
-- traceShow (dim0, dim1, dim2, dimX) $
  -- This is morally @V.create@ and so totally safe,
  -- but we can't just call @V.create@ four times, because it would run
  -- the @ST@ action four times, so we inline and extend @V.create@ here.
  runST $ do
    (iMap0, iMap1, iMap2, iMapX)
      <- buildFinMaps dim0 dim1 dim2 dimX deltaDt
    domains0 <- V.unsafeFreeze iMap0
    domains1 <- V.unsafeFreeze iMap1
    domains2 <- V.unsafeFreeze iMap2
    domainsX <- V.unsafeFreeze iMapX
    return $! Domains{..}
{-# SPECIALIZE gradientFromDelta
  :: Int -> Int -> Int -> Int -> DeltaDt Double
  -> Domains Double #-}

-- | Create vectors (representing finite maps) and an intmap that store
-- the state of evaluation, which holds values associated with inputs
-- and with (possibly shared) term tree nodes. For a pure rendition
-- of (a subset of) the state, with data invariants, see datatype
-- @EvalState@ in module @HordeAd.Internal.Delta@ in the codebase
-- of simplified horde-ad.
--
-- The vectors are, morally, indexed by input identifiers and node identifiers
-- and they eventually store cotangents for their respective nodes.
-- The cotangents are built gradually during the evaluation,
-- by summing cotangent contributions. The intmap records nodes
-- left to be processed.
--
-- The vectors indexed by input identifiers are initialized
-- with dummy values so that it's cheap to check
-- if any update has already been performed to a cell
-- (allocating big vectors and matrices filled with zeros is too costly,
-- especially if never used in an iteration, and adding to such matrices
-- and especially using them as cotangent accumulators is wasteful;
-- additionally, it may not be easy to deduce the sizes of the vectors
-- and matrices).
initializeFinMaps
  :: forall s r. Numeric r
  => Int -> Int -> Int -> Int
  -> ST s ( Data.Vector.Storable.Mutable.MVector s r
          , Data.Vector.Mutable.MVector s (Vector r)
          , Data.Vector.Mutable.MVector s (Matrix r)
          , Data.Vector.Mutable.MVector s (OT.Array r)
          , STRefU s (DeltaId r)
          , STRefU s (DeltaId (Vector r))
          , STRefU s (DeltaId (Matrix r))
          , STRefU s (DeltaId (OT.Array r))
          , STRef s (Data.Vector.Storable.Mutable.MVector s r)
          , STRef s (Data.Vector.Mutable.MVector s (Vector r))
          , STRef s (Data.Vector.Mutable.MVector s (MO.MatrixOuter r))
          , STRef s (Data.Vector.Mutable.MVector s (OT.Array r))
          , STRefU s Int
          , STRefU s Int
          , STRefU s Int
          , STRefU s Int
          , STRef s (EM.EnumMap NodeId (DeltaBinding r)) )
              -- Map and HashTable are way slower than the IntMap/EnumMap
initializeFinMaps dim0 dim1 dim2 dimX = do
  -- Eventually, cotangents of objective function inputs of rank 0.
  -- When filled and frozen, these four vectors together become
  -- the gradient of the objective function.
  iMap0 <- VM.replicate dim0 0  -- correct value; below are dummy
  iMap1 <- VM.replicate dim1 (V.empty :: Vector r)
  iMap2 <- VM.replicate dim2 (LA.fromRows [])
  iMapX <- VM.replicate dimX dummyTensor
  -- These indicate the current position for writing into the respective
  -- four vectors below. The position is only ever incremented.
  didCur0 <- newSTRefU (DeltaId 0)
  didCur1 <- newSTRefU (DeltaId 0)
  didCur2 <- newSTRefU (DeltaId 0)
  didCurX <- newSTRefU (DeltaId 0)
  -- Eventually, cotangents of non-input subterms.
  -- Unsafe is fine, because it initializes to bottoms and we always
  -- write before reading.
  dMap0' <- VM.unsafeNew (max 1 dim0)
  dMap1' <- VM.unsafeNew (max 1 dim1)
  dMap2' <- VM.unsafeNew (max 1 dim2)
  dMapX' <- VM.unsafeNew (max 1 dimX)
  dMap0 <- newSTRef dMap0'
  dMap1 <- newSTRef dMap1'
  dMap2 <- newSTRef dMap2'
  dMapX <- newSTRef dMapX'
  -- These keep current lengths of the vectors above.
  len0 <- newSTRefU (VM.length dMap0')
  len1 <- newSTRefU (VM.length dMap1')
  len2 <- newSTRefU (VM.length dMap2')
  lenX <- newSTRefU (VM.length dMapX')
  -- Node identifiers left to be evaluated, with their corresponding
  -- index into @dMap@ finite map and delta expression.
  nMap <- newSTRef EM.empty
  return ( iMap0, iMap1, iMap2, iMapX
         , didCur0, didCur1, didCur2, didCurX
         , dMap0, dMap1, dMap2, dMapX
         , len0, len1, len2, lenX
         , nMap )

buildFinMaps :: forall s r. (Eq r, Numeric r, Num (Vector r))
             => Int -> Int -> Int -> Int -> DeltaDt r
             -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                     , Data.Vector.Mutable.MVector s (Vector r)
                     , Data.Vector.Mutable.MVector s (Matrix r)
                     , Data.Vector.Mutable.MVector s (OT.Array r) )
buildFinMaps dim0 dim1 dim2 dimX deltaDt = do
  ( iMap0, iMap1, iMap2, iMapX
   ,didCur0, didCur1, didCur2, didCurX
   ,dMap0, dMap1, dMap2, dMapX
   ,len0, len1, len2, lenX
   ,nMap )
    <- initializeFinMaps dim0 dim1 dim2 dimX

  let addToVector :: Vector r -> Vector r -> Vector r
      addToVector c = \v -> if V.null v then c else v + c
      addToMatrix :: Matrix r -> Matrix r -> Matrix r
      addToMatrix c = \v -> if LA.rows v <= 0 then c else v + c
      addToArray :: OT.Array r -> OT.Array r -> OT.Array r
      addToArray c = \v -> if isTensorDummy v then c else v + c
      addToArrayS :: OS.Shape sh => OS.Array sh r -> OT.Array r -> OT.Array r
      addToArrayS c = \v -> let cs = Data.Array.Convert.convert c
                            in if isTensorDummy v
                               then cs
                               else v + cs

      -- This function modifies state comprising of vectors and a map.
      -- The first argument is the cotangent accumulator that will become
      -- an actual cotangent contribution when complete (see below for
      -- an explanation) and the second argument is the node to evaluate.
      eval0 :: r -> Delta0 r -> ST s ()
      eval0 !c = \case
        Zero0 -> return ()
        Input0 (InputId i) ->
          VM.modify iMap0 (+ c) i
        Scale0 k d -> eval0 (k * c) d
        Add0 d e -> eval0 c d >> eval0 c e
        Let0 n d -> assert (case d of
                      Zero0 -> False
                      Input0{} -> False
                      Let0{} -> False  -- wasteful and nonsensical
                      _ -> True)
                    $ do
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
          -- corresponding to the shared term @Let0 n d@. This total
          -- influence over the objective function's behaviour is called
          -- in short the cotangent of the node identifier @n@.
          -- In other words, the cotangent of @n@ is the sum,
          -- over all positions (edges) q in the global delta-expression DAG
          -- that are a reference to node @n@, of the partial derivative
          -- of the objective function with respect to the subcomputation
          -- corresponding to @q@ (meaning, subcomputations denoted by
          -- Haskell terms whose dual components are @Let n ...@).
          --
          -- For @Input@ terms, the eventual lists of cotangents end up
          -- in the cells of the gradient vectors that are the final
          -- result of the evaluation.
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding0 (DeltaId i) _) -> do
              dm <- readSTRef dMap0
              VM.modify dm (+ c) i
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCur0
              writeSTRefU didCur0 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding0 did d) nm
              len <- readSTRefU len0
              dm <- readSTRef dMap0
              if i >= len then do
                -- Unsafe is fine, because it initializes to bottoms (not to
                -- random words than may look like pointers) and we always
                -- write before reading.
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i c
                writeSTRef dMap0 dmG
                writeSTRefU len0 $ 2 * len
              else
                VM.write dm i c
            _ -> error "buildFinMaps: corrupted nMap"

        SumElements10 d n -> eval1 (LA.konst c n) d
        SumElements20 d (rows, cols) -> eval2 (MO.konst c rows cols) d
        SumElementsX0 d sh -> evalX (OT.constant sh c) d
        Index10 Zero1 _ _ -> return ()  -- shortcut
        Index10 (Input1 (InputId i)) ix k -> do
          let f v = if V.null v
                    then LA.konst 0 k V.// [(ix, c)]
                    else v V.// [(ix, v V.! ix + c)]
          VM.modify iMap1 f i
        Index10 (Let1 n d) ix k -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding1 (DeltaId i) _) -> do
              dm <- readSTRef dMap1
              let f v = v V.// [(ix, v V.! ix + c)]
              VM.modify dm f i
                -- This would be an asymptotic optimization compared to
                -- the general case below, if not for the non-mutable update,
                -- which implies copying the whole @v@ vector,
                -- so it's only several times faster (same allocation,
                -- but not adding to each cell of @v@).
                -- TODO: test, benchmark, improve and extend to higher ranks
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCur1
              writeSTRefU didCur1 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding1 did d) nm
              len <- readSTRefU len1
              dm <- readSTRef dMap1
              let v = LA.konst 0 k V.// [(ix, c)]
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i v
                writeSTRef dMap1 dmG
                writeSTRefU len1 $ 2 * len
              else
                VM.write dm i v
            _ -> error "buildFinMaps: corrupted nMap"
        Index10 d ix k -> eval1 (LA.konst 0 k V.// [(ix, c)]) d
          -- this general case can't occur, unless @Let1@ is optimized away,
          -- so best if it's optimized away together with any enclosing
          -- @Index10@ constructor
        Index20 d ix rowsCols -> do
          let mInit = LA.konst 0 rowsCols
              m = LA.accum mInit const [(ix, c)]  -- TODO: or flip const?
              mo = MO.MatrixOuter (Just m) Nothing Nothing
          eval2 mo d
        IndexX0 d ix sh -> evalX (OT.constant sh 0 `OT.update` [(ix, c)]) d
          -- TODO: perhaps inline eval2 and evalX, just as for Index10

        Dot0 v vd -> eval1 (LA.scale c v) vd

        FromX0 d -> evalX (OT.scalar c) d
        FromS0 d -> evalS (OS.scalar c) d

      eval1 :: Vector r -> Delta1 r -> ST s ()
      eval1 !c = \case
        Zero1 -> return ()
        Input1 (InputId i) ->
          VM.modify iMap1 (addToVector c) i
        Scale1 k d -> eval1 (k * c) d
        Add1 d e -> eval1 c d >> eval1 c e
        Let1 n d -> assert (case d of
                      Zero1 -> False
                      Input1{} -> False
                      Let1{} -> False  -- wasteful and nonsensical
                      _ -> True)
                    $ do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding1 (DeltaId i) _) -> do
              dm <- readSTRef dMap1
              VM.modify dm (+ c) i
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCur1
              writeSTRefU didCur1 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding1 did d) nm
              len <- readSTRefU len1
              dm <- readSTRef dMap1
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i c
                writeSTRef dMap1 dmG
                writeSTRefU len1 $ 2 * len
              else
                VM.write dm i c
            _ -> error "buildFinMaps: corrupted nMap"

        FromList1 lsd -> imapM_ (\i d -> eval0 (c V.! i) d) lsd
          -- lsd is a list (boxed vector) of scalar delta expressions
        FromVector1 lsd -> V.imapM_ (\i d -> eval0 (c V.! i) d) lsd
          -- lsd is a boxed vector of scalar delta expressions
        Konst1 d _n -> V.mapM_ (`eval0` d) c
        Append1 d k e -> eval1 (V.take k c) d >> eval1 (V.drop k c) e
        Slice1 i n d len ->
          eval1 (LA.konst 0 i V.++ c V.++ LA.konst 0 (len - i - n)) d
        SumRows1 dm cols -> eval2 (MO.asColumn c cols) dm
        SumColumns1 dm rows -> eval2 (MO.asRow c rows) dm

        M_VD1 m dRow ->
          mapM_ (`eval1` dRow)
                (MO.toRows (MO.MatrixOuter (Just m) (Just c) Nothing))
        MD_V1 md row -> eval2 (MO.MatrixOuter Nothing (Just c) (Just row)) md

        FromX1 d -> evalX (OT.fromVector [V.length c] c) d
        FromS1 d -> evalS (OS.fromVector c) d

        Reverse1 d -> eval1 (V.reverse c) d
        Flatten1 rows cols d ->
          eval2 (MO.MatrixOuter (Just $ rows LA.>< cols $ V.toList c)
                                Nothing Nothing)
                d
        FlattenX1 sh d -> evalX (OT.fromVector sh c) d
        FlattenS1 d -> evalS (OS.fromVector c) d
        Build1 _n f -> V.imapM_ (\i c0 -> eval0 c0 (f i)) c

      eval2 :: MO.MatrixOuter r -> Delta2 r -> ST s ()
      eval2 !c = \case
        Zero2 -> return ()
        Input2 (InputId i) ->
          VM.modify iMap2 (addToMatrix $ MO.convertMatrixOuter c) i
        Scale2 k d -> eval2 (MO.multiplyWithOuter k c) d
        Add2 d e -> eval2 c d >> eval2 c e
        Let2 n d -> assert (case d of
                      Zero2 -> False
                      Input2{} -> False
                      Let2{} -> False  -- wasteful and nonsensical
                      _ -> True)
                    $ do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding2 (DeltaId i) _) -> do
              dm <- readSTRef dMap2
              VM.modify dm (MO.plus c) i
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCur2
              writeSTRefU didCur2 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding2 did d) nm
              len <- readSTRefU len2
              dm <- readSTRef dMap2
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i c
                writeSTRef dMap2 dmG
                writeSTRefU len2 $ 2 * len
              else
                VM.write dm i c
            _ -> error "buildFinMaps: corrupted nMap"

        FromList2 _rowsCols lsd -> do
          -- TODO: speedup likely via an indexing operation on MatrixOuter
          -- or perhaps a flatten/toList operation
          let vc = LA.flatten $ MO.convertMatrixOuter c
          imapM_ (\i d -> eval0 (vc V.! i) d) lsd
        FromVector2 __rowsCols lsd -> do
          let vc = LA.flatten $ MO.convertMatrixOuter c
          V.imapM_ (\i d -> eval0 (vc V.! i) d) lsd
        FromRows2 lvd -> zipWithM_ eval1 (MO.toRows c) (V.toList lvd)
        FromColumns2 lvd -> zipWithM_ eval1 (MO.toColumns c) (V.toList lvd)
        Konst2 d _sz -> mapM_ (V.mapM_ (`eval0` d)) $ MO.toRows c
        Transpose2 md -> eval2 (MO.transpose c) md  -- TODO: test!
        M_MD2 m md ->
          let mo = MO.MatrixOuter (Just $ LA.tr' m) Nothing Nothing
          in eval2 (MO.matMul mo c) md
        MD_M2 md m ->
          let mo = MO.MatrixOuter (Just $ LA.tr' m) Nothing Nothing
          in eval2 (MO.matMul c mo) md
        RowAppend2 d k e -> eval2 (MO.takeRows k c) d
                            >> eval2 (MO.dropRows k c) e
        ColumnAppend2 d k e -> eval2 (MO.takeColumns k c) d
                               >> eval2 (MO.dropColumns k c) e
        RowSlice2 i n d rows ->
          assert (MO.rows c == n) $
          let cols = MO.cols c
          in eval2 (MO.konst 0 i cols
                    `MO.rowAppend` c
                    `MO.rowAppend` MO.konst 0 (rows - i - n) cols)
                   d
        ColumnSlice2 i n d cols ->
          assert (MO.cols c == n) $
          let rows = MO.rows c
          in eval2 (MO.konst 0 rows i
                    `MO.columnAppend` c
                    `MO.columnAppend` MO.konst 0 rows (cols - i - n))
                   d

        AsRow2 dRow -> mapM_ (`eval1` dRow) (MO.toRows c)
        AsColumn2 dCol -> mapM_ (`eval1` dCol) (MO.toColumns c)

        FromX2 d -> evalX (OT.fromVector [MO.rows c, MO.cols c]
                                         (V.concat $ MO.toRows c)) d
        FromS2 d -> evalS (OS.fromVector $ V.concat $ MO.toRows c) d

        Flipud2 d -> eval2 (MO.flipud c) d
        Fliprl2 d -> eval2 (MO.fliprl c) d
        Reshape2 _cols d -> eval1 (V.concat $ MO.toRows c) d
        Conv2 m md ->
          let moc = MO.convertMatrixOuter c
              convolved = LA.corr2 m moc
              moConv = MO.MatrixOuter (Just convolved) Nothing Nothing
          in eval2 moConv md
        Build2 _rowsCols f -> do
          let moc = MO.convertMatrixOuter c
          Numeric.LinearAlgebra.Devel.mapMatrixWithIndexM_
            (\rowsCols c0 -> eval0 c0 (f rowsCols)) moc

      evalX :: OT.Array r -> DeltaX r -> ST s ()
      evalX !c = \case
        ZeroX -> return ()
        InputX (InputId i) ->
          VM.modify iMapX (addToArray c) i
        ScaleX k d -> evalX (k * c) d
        AddX d e -> evalX c d >> evalX c e
        LetX n d -> assert (case d of
                      ZeroX -> False
                      InputX{} -> False
                      LetX{} -> False  -- wasteful and nonsensical
                      _ -> True)
                    $ do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBindingX (DeltaId i) _) -> do
              dm <- readSTRef dMapX
              VM.modify dm (+ c) i
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCurX
              writeSTRefU didCurX $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBindingX did d) nm
              len <- readSTRefU lenX
              dm <- readSTRef dMapX
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i c
                writeSTRef dMapX dmG
                writeSTRefU lenX $ 2 * len
              else
                VM.write dm i c
            _ -> error "buildFinMaps: corrupted nMap"

        FromListX _sh lsd -> do
          let vc = OT.toVector c
          imapM_ (\i d -> eval0 (vc V.! i) d) lsd
        FromVectorX _sh lsd -> do
          let vc = OT.toVector c
          V.imapM_ (\i d -> eval0 (vc V.! i) d) lsd
        KonstX d _sh -> mapM_ (`eval0` d) $ OT.toList c
        AppendX d k e -> case OT.shapeL c of
          n : _ -> evalX (OT.slice [(0, k)] c) d
                   >> evalX (OT.slice [(k, n - k)] c) e
          [] -> error "evalX: appending a 0-dimensional tensor"
        SliceX i n d len -> case OT.shapeL c of
          n' : rest ->
            assert (n' == n) $
            evalX (OT.concatOuter [ OT.constant (i : rest) 0
                                  , c
                                  , OT.constant (len - i - n : rest) 0 ])
                  d
          [] -> error "evalX: slicing a 0-dimensional tensor"
        IndexX d ix len ->
          let rest = OT.shapeL c
          in evalX (OT.concatOuter [ OT.constant (ix : rest) 0
                                   , OT.reshape (1 : rest) c
                                   , OT.constant (len - ix - 1 : rest) 0 ])
                   d  -- TODO: optimize for input case
        RavelFromListX ld -> do
          let lc = OTB.toList $ OT.unravel c
          mapM_ (uncurry evalX) (zip lc ld)
        ReshapeX sh _sh' d -> evalX (OT.reshape sh c) d

        From0X d -> eval0 (OT.unScalar c) d
        From1X d -> eval1 (OT.toVector c) d
        From2X d cols ->
          eval2 (MO.MatrixOuter (Just $ LA.reshape cols $ OT.toVector c)
                                Nothing Nothing)
                d
        FromSX d -> evalS (Data.Array.Convert.convert c) d

        BuildX sh f -> do
          -- Copied from Data.Array.Internal.
          let getStridesT :: OT.ShapeL -> [Int]
              getStridesT = scanr (*) 1
              ss = case getStridesT sh of
                _ : ss2 -> ss2
                [] -> error "scanr in buildDerivative"
              toIx [] _ = []
              toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
          V.imapM_ (\i c0 -> eval0 c0 (f $ toIx ss i)) $ OT.toVector c

      evalS :: OS.Shape sh
            => OS.Array sh r -> DeltaS sh r -> ST s ()
      evalS !c = \case
        ZeroS -> return ()
        InputS (InputId i) ->
         VM.modify iMapX (addToArrayS c) i
        ScaleS k d -> evalS (k * c) d
        AddS d e -> evalS c d >> evalS c e
        LetS n d -> assert (case d of
                      ZeroS -> False
                      InputS{} -> False
                      LetS{} -> False  -- wasteful and nonsensical
                      _ -> True)
                    $ do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBindingS (DeltaId i) _) -> do
              dm <- readSTRef dMapX
              let cs = Data.Array.Convert.convert c
              VM.modify dm (+ cs) i
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCurX
              writeSTRefU didCurX $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBindingS did d) nm
              len <- readSTRefU lenX
              dm <- readSTRef dMapX
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i (Data.Array.Convert.convert c)
                writeSTRef dMapX dmG
                writeSTRefU lenX $ 2 * len
              else
                VM.write dm i (Data.Array.Convert.convert c)
            _ -> error "buildFinMaps: corrupted nMap"

#if defined(VERSION_ghc_typelits_natnormalise)
        FromListS lsd -> do
          let vc = OS.toVector c
          imapM_ (\i d -> eval0 (vc V.! i) d) lsd
        FromVectorS lsd -> do
          let vc = OS.toVector c
          V.imapM_ (\i d -> eval0 (vc V.! i) d) lsd
        KonstS d -> mapM_ (`eval0` d) $ OS.toList c
        AppendS (d :: DeltaS (k ': rest) c) (e :: DeltaS (l ': rest) c) ->
          evalS (OS.slice @'[ '(0, k) ] c) d
          >> evalS (OS.slice @'[ '(k, l) ] c) e
        SliceS (_ :: Proxy i) _ (d :: DeltaS (i_plus_n_plus_k ': rest) c) ->
          evalS (OS.constant @(i ': rest) 0
                 `OS.append` c
                 `OS.append` OS.constant 0)
                d
        IndexS (d :: DeltaS (ix_plus_1_plus_k ': rest) c) (_ :: Proxy ix) ->
          evalS (OS.constant @(ix ': rest) 0
                 `OS.append` OS.reshape c
                 `OS.append` OS.constant 0)
                d  -- TODO: optimize for input case
        RavelFromListS ld -> do
          let lc = OSB.toList $ OS.unravel c
          mapM_ (uncurry evalS) (zip lc ld)
        ReshapeS d -> evalS (OS.reshape c) d

        From0S d -> eval0 (OS.unScalar c) d
        From1S d -> eval1 (OS.toVector c) d
        From2S proxyCols d ->
          eval2 (MO.MatrixOuter
                   (Just $ LA.reshape (fromInteger $ natVal proxyCols)
                         $ OS.toVector c)
                   Nothing Nothing)
                d
        FromXS d -> evalX (Data.Array.Convert.convert c) d

        BuildS f -> do
          -- Copied from Data.Array.Internal.
          let getStridesT :: OS.ShapeL -> [Int]
              getStridesT = scanr (*) 1
              ss = case getStridesT sh of
                _ : ss2 -> ss2
                [] -> error "scanr in buildDerivative"
              toIx [] _ = []
              toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
              sh = OS.shapeL c
          V.imapM_ (\i c0 -> eval0 c0 (f $ toIx ss i)) $ OS.toVector c
#endif

  case deltaDt of
    DeltaDt0 dt deltaTopLevel -> eval0 dt deltaTopLevel
    DeltaDt1 dt deltaTopLevel -> eval1 dt deltaTopLevel
    DeltaDt2 dt deltaTopLevel ->
      eval2 (MO.MatrixOuter (Just dt) Nothing Nothing) deltaTopLevel
    DeltaDtX dt deltaTopLevel -> evalX dt deltaTopLevel
    DeltaDtS dt deltaTopLevel -> evalS dt deltaTopLevel

  let evalUnlessZero :: DeltaBinding r -> ST s ()
      evalUnlessZero (DeltaBinding0 (DeltaId i) d) = do
        dm <- readSTRef dMap0
        c <- dm `VM.read` i
        unless (c == 0) $  -- a cheap optimization in case of scalars
          eval0 c d
      evalUnlessZero (DeltaBinding1 (DeltaId i) d) = do
        dm <- readSTRef dMap1
        c <- dm `VM.read` i
        eval1 c d
      evalUnlessZero (DeltaBinding2 (DeltaId i) d) = do
        dm <- readSTRef dMap2
        c <- dm `VM.read` i
        eval2 c d
      evalUnlessZero (DeltaBindingX (DeltaId i) d) = do
        dm <- readSTRef dMapX
        c <- dm `VM.read` i
        evalX c d
      evalUnlessZero (DeltaBindingS (DeltaId i) d) = do
        dm <- readSTRef dMapX
        c <- dm `VM.read` i
        evalS (Data.Array.Convert.convert c) d
      evalFromnMap :: ST s ()
      evalFromnMap = do
        nm <- readSTRef nMap
        case EM.maxView nm of
          Just (b, nm2) -> do
            writeSTRef nMap $! nm2
            evalUnlessZero b
            evalFromnMap
          Nothing -> return ()  -- loop ends
  evalFromnMap

  return (iMap0, iMap1, iMap2, iMapX)
{-# SPECIALIZE buildFinMaps
  :: Int -> Int -> Int -> Int -> DeltaDt Double
  -> ST s ( Data.Vector.Storable.Mutable.MVector s Double
          , Data.Vector.Mutable.MVector s (Vector Double)
          , Data.Vector.Mutable.MVector s (Matrix Double)
          , Data.Vector.Mutable.MVector s (OT.Array Double) ) #-}

-- | Forward derivative computation via forward-evaluation of delta-expressions
-- (which is surprisingly competitive to the direct forward method,
-- until the allocation of deltas gets large enough to affect cache hits).
-- This is the directional derivative, calculated for the point,
-- at which the delta expression was computed (which is the point
-- represented by the parameters of the objective function and used
-- to compute it's dual number result) and along the direction vector(s)
-- given in the last parameter called @ds@.
derivativeFromDelta
  :: (Numeric r, Num (Vector r))
  => Int -> Int -> Int -> Int -> Delta0 r -> Domains r -> r
derivativeFromDelta dim0 dim1 dim2 dimX deltaTopLevel ds =
  runST $ buildDerivative dim0 dim1 dim2 dimX deltaTopLevel ds

-- | This mimics 'buildFinMaps', but in reverse. Perhaps this can be
-- simplified, but the obvious simplest formulation does not honour sharing
-- and evaluates shared subexpressions repeatedly.
buildDerivative
  :: forall s r. (Numeric r, Num (Vector r))
  => Int -> Int -> Int -> Int -> Delta0 r -> Domains r
  -> ST s r
buildDerivative dim0 dim1 dim2 dimX deltaTopLevel
                Domains{..} = do
  ( _, _, _, _
   ,didCur0, didCur1, didCur2, didCurX
   ,dMap0, dMap1, _, dMapX
   ,len0, len1, len2, lenX
   ,nMap )
   <- initializeFinMaps dim0 dim1 dim2 dimX
  -- We use normal hmatrix matrices rather than the sparse replacement.
  lenOuter <- readSTRefU len2
  dMap2' :: Data.Vector.Mutable.MVector s (Matrix r)
    <- VM.replicate lenOuter (LA.fromRows [])
  dMap2 <- newSTRef dMap2'
  let eval0 :: Delta0 r -> ST s r
      eval0 = \case
        Zero0 -> return 0
        Input0 (InputId i) ->
          if i < dim0
          then return $! domains0 V.! i
          else error "derivativeFromDelta.eval': wrong index for an input"
        Scale0 k d -> (k *) <$> eval0 d
        Add0 d e -> liftM2 (+) (eval0 d) (eval0 e)
        Let0 n d -> do
          -- This is too complex, but uses components already defined
          -- for initializeFinMaps and some of a similar code.
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding0 (DeltaId i) _) -> do
              dm <- readSTRef dMap0
              VM.read dm i
            Nothing -> do
              c <- eval0 d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMap0
              did@(DeltaId i) <- readSTRefU didCur0
              writeSTRefU didCur0 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding0 did d) nmNew
              len <- readSTRefU len0
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i c
                writeSTRef dMap0 dmG
                writeSTRefU len0 $ 2 * len
              else
                VM.write dm i c
              return c
            _ -> error "buildDerivative: corrupted nMap"

        SumElements10 d _ -> LA.sumElements <$> eval1 d
        SumElements20 d _ -> LA.sumElements <$> eval2 d
        SumElementsX0 d _ -> OT.sumA <$> evalX d
        Index10 d ix _k -> flip (V.!) ix <$> eval1 d
        Index20 d ix _rowsCols -> flip LA.atIndex ix <$> eval2 d
        IndexX0 d ix _sh -> flip atIndexInTensor ix <$> evalX d

        Dot0 vc vd -> (<.>) vc <$> eval1 vd

        FromX0 d -> OT.unScalar <$> evalX d
        FromS0 d -> OS.unScalar <$> evalS d

      eval1 :: Delta1 r -> ST s (Vector r)
      eval1 = \case
        Zero1 -> return 0
        Input1 (InputId i) ->
          if i < dim1
          then return $! domains1 V.! i
          else error "derivativeFromDelta.eval': wrong index for an input"
        Scale1 k d -> (k *) <$> eval1 d
        Add1 d e -> liftM2 (+) (eval1 d) (eval1 e)
        Let1 n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding1 (DeltaId i) _) -> do
              dm <- readSTRef dMap1
              VM.read dm i
            Nothing -> do
              c <- eval1 d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMap1
              did@(DeltaId i) <- readSTRefU didCur1
              writeSTRefU didCur1 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding1 did d) nmNew
              len <- readSTRefU len1
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i c
                writeSTRef dMap1 dmG
                writeSTRefU len1 $ 2 * len
              else
                VM.write dm i c
              return c
            _ -> error "buildDerivative: corrupted nMap"

        FromList1 lsd -> do
          l <- mapM eval0 lsd
          return $! V.fromList l
        FromVector1 lsd -> do
          v <- V.mapM eval0 lsd
          return $! V.convert v
        Konst1 d n -> flip LA.konst n <$> eval0 d
        Append1 d _k e -> liftM2 (V.++) (eval1 d) (eval1 e)
        Slice1 i n d _len -> V.slice i n <$> eval1 d
        SumRows1 dm _cols ->
          V.fromList . map LA.sumElements . LA.toRows <$> eval2 dm
        SumColumns1 dm _rows ->
          V.fromList . map LA.sumElements . LA.toColumns <$> eval2 dm

        M_VD1 m dRow -> (LA.#>) m <$> eval1 dRow
        MD_V1 md row -> flip (LA.#>) row <$> eval2 md

        FromX1 d -> OT.toVector <$> evalX d
        FromS1 d -> OS.toVector <$> evalS d

        Reverse1 d -> V.reverse <$> eval1 d
        Flatten1 _rows _cols d -> LA.flatten <$> eval2 d
        FlattenX1 _sh d -> OT.toVector <$> evalX d
        FlattenS1 d -> OS.toVector <$> evalS d
        Build1 n f -> do
          l <- mapM (eval0 . f) [0 .. n - 1]
          return $! V.fromList l

      eval2 :: Delta2 r -> ST s (Matrix r)
      eval2 = \case
        Zero2 -> return 0
        Input2 (InputId i) ->
          if i < dim2
          then return $! domains2 V.! i
          else error "derivativeFromDelta.eval': wrong index for an input"
        Scale2 k d -> (k *) <$> eval2 d
        Add2 d e -> liftM2 (+) (eval2 d) (eval2 e)
        Let2 n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding2 (DeltaId i) _) -> do
              dm <- readSTRef dMap2
              VM.read dm i
            Nothing -> do
              c <- eval2 d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMap2
              did@(DeltaId i) <- readSTRefU didCur2
              writeSTRefU didCur2 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding2 did d) nmNew
              len <- readSTRefU len2
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i c
                writeSTRef dMap2 dmG
                writeSTRefU len2 $ 2 * len
              else
                VM.write dm i c
              return c
            _ -> error "buildDerivative: corrupted nMap"

        FromList2 (rows, cols) lsd -> do
          l <- mapM eval0 lsd
          return $! (rows LA.>< cols) l
        FromVector2 (_i, j) lsd -> do
          v <- V.mapM eval0 lsd
          return $! LA.reshape j $ V.convert v  -- TODO: fail if _i fake
        FromRows2 lvd -> do
          l <- mapM eval1 $ V.toList lvd
          return $! LA.fromRows l
        FromColumns2 lvd -> do
          l <- mapM eval1 $ V.toList lvd
          return $! LA.fromColumns l
        Konst2 d sz -> flip LA.konst sz <$> eval0 d
        Transpose2 md -> LA.tr' <$> eval2 md
        M_MD2 m md -> (LA.<>) m <$> eval2 md
        MD_M2 md m -> flip (LA.<>) m <$> eval2 md
        RowAppend2 d _k e -> liftM2 (LA.===) (eval2 d) (eval2 e)
        ColumnAppend2 d _k e -> liftM2 (LA.|||) (eval2 d) (eval2 e)
        RowSlice2 i n d _rows ->
          LA.takeRows n . LA.dropRows i <$> eval2 d
        ColumnSlice2 i n d _cols ->
          LA.takeColumns n . LA.dropColumns i <$> eval2 d

        AsRow2 dRow -> LA.asRow <$> eval1 dRow  -- TODO: risky
        AsColumn2 dCol -> LA.asColumn <$> eval1 dCol  -- TODO: risky

        FromX2 d -> do
          t <- evalX d
          case OT.shapeL t of
            [_rows, cols] -> return $! LA.reshape cols $ OT.toVector t
            _ -> error "eval2: wrong tensor dimensions"
        FromS2 d -> do
          t <- evalS d
          case OS.shapeL t of
            [_rows, cols] -> return $! LA.reshape cols $ OS.toVector t
            _ -> error "eval2: wrong tensor dimensions"

        Flipud2 d -> LA.flipud <$> eval2 d
        Fliprl2 d -> LA.fliprl <$> eval2 d
        Reshape2 cols d -> LA.reshape cols <$> eval1 d
        Conv2 m md -> LA.conv2 m <$> eval2 md
        Build2 (rows, cols) f -> do
          l <- mapM (eval0 . f)
               $ [(i1, j1) | i1 <- [0 .. rows - 1], j1 <- [0 .. cols - 1]]
          return $! (rows LA.>< cols) l

      evalX :: DeltaX r -> ST s (OT.Array r)
      evalX = \case
        ZeroX -> return 0
        InputX (InputId i) ->
          if i < dimX
          then return $! domainsX V.! i
          else error "derivativeFromDelta.eval': wrong index for an input"
        ScaleX k d -> (k *) <$> evalX d
        AddX d e -> liftM2 (+) (evalX d) (evalX e)
        LetX n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBindingX (DeltaId i) _) -> do
              dm <- readSTRef dMapX
              VM.read dm i
            Nothing -> do
              c <- evalX d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMapX
              did@(DeltaId i) <- readSTRefU didCurX
              writeSTRefU didCurX $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBindingX did d) nmNew
              len <- readSTRefU lenX
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i c
                writeSTRef dMapX dmG
                writeSTRefU lenX $ 2 * len
              else
                VM.write dm i c
              return c
            _ -> error "buildDerivative: corrupted nMap"

        FromListX sh lsd -> do
          l <- mapM eval0 lsd
          return $! OT.fromList sh l
        FromVectorX sh lsd -> do
          v <- V.mapM eval0 lsd
          return $! OT.fromVector sh $ V.convert v
        KonstX d sh -> OT.constant sh <$> eval0 d
        AppendX d _k e -> liftM2 OT.append (evalX d) (evalX e)
        SliceX i n d _len -> OT.slice [(i, n)] <$> evalX d
        IndexX d ix _len -> flip OT.index ix <$> evalX d
        RavelFromListX ld -> do
          la <- mapM evalX ld
          let sh = case la of
                a : _ -> length la : OT.shapeL a
                [] -> []
          return $! OT.ravel $ OTB.fromList sh la
        ReshapeX _sh sh' d -> OT.reshape sh' <$> evalX d

        From0X d -> OT.scalar <$> eval0 d
        From1X d -> do
          v <- eval1 d
          return $! OT.fromVector [V.length v] v
        From2X d cols -> do
          l <- eval2 d
          return $! OT.fromVector [LA.rows l, cols] $ LA.flatten l
        FromSX d -> Data.Array.Convert.convert <$> evalS d

        BuildX sh f -> do
          -- Copied from Data.Array.Internal.
          let getStridesT :: OT.ShapeL -> [Int]
              getStridesT = scanr (*) 1
              (s, ss) = case getStridesT sh of
                s2 : ss2 -> (s2, ss2)
                [] -> error "scanr in buildDerivative"
              toIx [] _ = []
              toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
          l <- mapM (eval0 . f)
               $ [toIx ss i | i <- [0 .. s - 1]]
          return $! OT.fromList sh l

      evalS :: forall sh. OS.Shape sh => DeltaS sh r -> ST s (OS.Array sh r)
      evalS = \case
        ZeroS -> return 0
        InputS (InputId i) ->
          if i < dimX
          then return $! Data.Array.Convert.convert $ domainsX V.! i
          else error "derivativeFromDelta.eval': wrong index for an input"
        ScaleS k d -> (k *) <$> evalS d
        AddS d e -> liftM2 (+) (evalS d) (evalS e)
        LetS n d -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBindingS (DeltaId i) _) -> do
              dm <- readSTRef dMapX
              Data.Array.Convert.convert <$> VM.read dm i
            Nothing -> do
              c <- evalS d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMapX
              did@(DeltaId i) <- readSTRefU didCurX
              writeSTRefU didCurX $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBindingS did d) nmNew
              len <- readSTRefU lenX
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i (Data.Array.Convert.convert c)
                writeSTRef dMapX dmG
                writeSTRefU lenX $ 2 * len
              else
                VM.write dm i (Data.Array.Convert.convert c)
              return c
            _ -> error "buildDerivative: corrupted nMap"

#if defined(VERSION_ghc_typelits_natnormalise)
        FromListS lsd -> do
          l <- mapM eval0 lsd
          return $! OS.fromList l
        FromVectorS lsd -> do
          v <- V.mapM eval0 lsd
          return $! OS.fromVector $ V.convert v
        KonstS d -> OS.constant <$> eval0 d
        AppendS d e -> liftM2 OS.append (evalS d) (evalS e)
        SliceS (_ :: Proxy i) (_ :: Proxy n) d ->
          OS.slice @'[ '(i, n) ] <$> evalS d
        IndexS d proxyIx ->
          flip OS.index (fromInteger $ natVal proxyIx) <$> evalS d
        RavelFromListS ld -> do
          la <- mapM evalS ld
          return $! OS.ravel $ OSB.fromList la
        ReshapeS d -> OS.reshape <$> evalS d

        From0S d -> OS.scalar <$> eval0 d
        From1S d -> OS.fromVector <$> eval1 d
        From2S _ d -> OS.fromVector . LA.flatten <$> eval2 d
        FromXS d -> Data.Array.Convert.convert <$> evalX d

        BuildS f -> do
          -- Copied from Data.Array.Internal.
          let getStridesT :: OS.ShapeL -> [Int]
              getStridesT = scanr (*) 1
              (s, ss) = case getStridesT sh of
                s2 : ss2 -> (s2, ss2)
                [] -> error "scanr in buildDerivative"
              toIx [] _ = []
              toIx (n:ns) i = q : toIx ns r where (q, r) = quotRem i n
              sh = OS.shapeP (Proxy :: Proxy sh)
          l <- mapM (eval0 . f)
               $ [toIx ss i | i <- [0 .. s - 1]]
          return $! OS.fromList l
#endif

  eval0 deltaTopLevel

{- Note [SumElements10]
~~~~~~~~~~~~~~~~~~~~~~

The second argument of SumElements10 is the length of the vector
to be summed. Given that we sum a delta-expression representing
a vector, we can't call Vector.length on it, so the length needs
to be recorded in the constructor. Alternatively, it could be
recorded in the Delta1 argument to SumElements10. This is what
shaped tensors do at the type level, so for DeltaS the argument
would not be needed.

Sum of vector elements can be implemented using a delta-expression
primitive SumElements10 as well as without this primitive, referring
only to the primitive Index10:

https://github.com/Mikolaj/horde-ad/blob/d069a45773ed849913b5ebd0345153072f304fd9/src/HordeAd.Core.DualNumber.hs#L125-L143

which is confirmed by tests to be equivalent in three different
implementations:

https://github.com/Mikolaj/horde-ad/blob/d069a45773ed849913b5ebd0345153072f304fd9/test/TestSingleGradient.hs#L116-L128

and proved to be prohibitively slow in the two implementations
that don't use the SumElements10 primitive in benchmarks (despite
an ingenious optimization of the common case of Index10 applied to a input):

https://github.com/Mikolaj/horde-ad/blob/d069a45773ed849913b5ebd0345153072f304fd9/bench/BenchProdTools.hs#L178-L193
-}

dummyTensor :: Numeric r => OT.Array r
dummyTensor =  -- an inconsistent tensor array
  Data.Array.Internal.DynamicS.A
  $ Data.Array.Internal.DynamicG.A []
  $ Data.Array.Internal.T [] (-1) V.empty

isTensorDummy :: OT.Array r -> Bool
isTensorDummy (Data.Array.Internal.DynamicS.A
                 (Data.Array.Internal.DynamicG.A _
                    (Data.Array.Internal.T _ (-1) _))) = True
isTensorDummy _ = False

toVectorOrDummy :: Numeric r
                => Int -> Vector r -> Vector r
toVectorOrDummy size x = if V.null x
                         then LA.konst 0 size
                         else x

toMatrixOrDummy :: Numeric r
                => (Int, Int) -> Matrix r -> Matrix r
toMatrixOrDummy size x = if LA.size x == (0, 0)
                         then LA.konst 0 size
                         else x

toShapedOrDummy :: (Numeric r, OS.Shape sh)
                => OT.Array r -> OS.Array sh r
toShapedOrDummy x = if isTensorDummy x
                    then OS.constant 0
                    else Data.Array.Convert.convert x

toDynamicOrDummy :: Numeric r
                 => OT.ShapeL -> OT.Array r -> OT.Array r
toDynamicOrDummy sh x = if isTensorDummy x
                        then OT.constant sh 0
                        else x

atIndexInTensor :: Numeric r => OT.Array r -> [Int] -> r
atIndexInTensor (Data.Array.Internal.DynamicS.A
                   (Data.Array.Internal.DynamicG.A _
                      Data.Array.Internal.T{..})) is =
  values V.! (offset + sum (zipWith (*) is strides))
    -- TODO: tests are needed to verify if order of dimensions is right
