{-# LANGUAGE CPP, DataKinds, GADTs, GeneralizedNewtypeDeriving, KindSignatures,
             RankNTypes, StandaloneDeriving, UnboxedTuples #-}
#if !MIN_VERSION_base(4,16,0)
{-# LANGUAGE IncoherentInstances #-}
#endif
#if defined(VERSION_ghc_typelits_natnormalise)
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
#endif
-- | The second component of our rendition of dual numbers,
-- delta expressions, with its semantics.
-- Neel Krishnaswami calls it \"sparse vector expressions\",
-- and indeed even in the simplest case of an objective function
-- defined on scalars only, the codomain of the function that computes
-- gradients from such delta expressions is a set of vectors, because
-- the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
--
-- The \'sparsity\' is less obvious when the domain of the function consists
-- of multiple vectors, matrices and tensors and when the expressions themselves
-- contain vectors, matrices and tensors. However, a single tiny delta
-- expression (e.g., a sum of two inputs) may denote a vector of matrices.
-- Even a delta expression containing a big matrix denotes something much
-- bigger: a whole vector of such matrices and more.
--
-- The algebraic structure here is an extension of vector space.
-- The crucial extra constructor of an input replaces the one-hot
-- access to parameters with something cheaper and more uniform.
-- A lot of the remaining additional structure is for introducing
-- and reducing dimensions (ranks).
--
-- This is an internal low-level API, while the module @DualClass@
-- is an intermediate mid-level API that generates 'NodeId' identifiers,
-- wraps delta-expression datatype constructors in smart constructors
-- and provides a generalization to other kinds of second components
-- of dual numbers, e.g., the same as primal component, for fast computation
-- of forward derivatives (because @derivativeFromDelta@ below,
-- computing derivatives from delta-expressions, is slow once
-- the expressions grow large enough to affect cache misses).
module HordeAd.Internal.Delta
  ( -- * Abstract syntax trees of the delta expressions
    Delta0 (..), Delta1 (..), Delta2 (..), DeltaX (..), DeltaS (..)
  , -- * Delta expression identifiers
    NodeId(..), InputId, toInputId
  , -- * Evaluation of the delta expressions
    DeltaDt (..), Domain0, Domain1, Domain2, DomainX, Domains
  , gradientFromDelta, derivativeFromDelta
  , isTensorDummy, toShapedOrDummy, toDynamicOrDummy
  ) where

import Prelude

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
import           GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector, (<.>))
import qualified Numeric.LinearAlgebra as LA
import qualified Numeric.LinearAlgebra.Devel
import           Text.Show.Functions ()

import qualified HordeAd.Internal.MatrixOuter as MO
import           HordeAd.Internal.OrthotopeOrphanInstances (liftVS2, liftVT2)

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
-- The `NodeId` identifier, which is the first argument of the @Let0@
-- constructor, marks the unique identity of a subterm among
-- all subtrees of all top level delta expression terms.
-- The uniqueness of the identity is used to avoid processing
-- shared subterm repeatedly in gradient and derivative computations.
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
-- directly or indirectly, the data accumulated for each node, in the form of
-- cotangents, that is partial derivatives of the objective function
-- with respect to the position of the node in the whole term,
-- as if the node was replaced by a variable over which we differentiate
-- (and, more generally, a collection of such positions if the term
-- is shared between them, as marked by an identical node identifier).
-- The exception are the @Input@ nodes of all ranks that fill the role
-- of such variables and that have a separate data storage.
-- The per-rank `InputId` identifiers in the @Input@ term constructors
-- are indexes into contiguous vectors of contangents of exclusively @Input@
-- subterms of the whole term. The value at that index is the partial
-- derivative of the objective function (represented by the whole term)
-- with respect to the input parameter component at that index
-- in the objective function domain. The collection of all such
-- vectors of partial derivatives across all ranks is the gradient.
data Delta0 r =
    Zero0
  | Input0 (InputId r)
  | Scale0 r (Delta0 r)
  | Add0 (Delta0 r) (Delta0 r)
  | Let0 NodeId (Delta0 r)

  | SumElements0 (Delta1 r) Int  -- ^ see Note [SumElements0]
  | Index0 (Delta1 r) Int Int  -- ^ second integer is the length of the vector

  | Dot0 (Vector r) (Delta1 r)  -- ^ Dot0 v vd == SumElements0 (Scale1 v vd) n

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

  | FromRows2 (Data.Vector.Vector (Delta1 r))  -- ^ "unboxing" conversion again
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
  deriving (Enum, Prim)
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
  deriving (Show, Prim)
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

type Domains r = (Domain0 r, Domain1 r, Domain2 r, DomainX r)

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

-- | Node identifiers left to be processed, with their corresponding
-- index into @dMap@ finite map and delta expression.
-- We can't process them at once, because their other shared copies
-- may still not be processed, so we'd not take advantage of the sharing.
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
-- of fininte maps or vectors) of type @Domains r@ and produces
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
    v0 <- V.unsafeFreeze iMap0
    v1 <- V.unsafeFreeze iMap1
    v2 <- V.unsafeFreeze iMap2
    vX <- V.unsafeFreeze iMapX
    return (v0, v1, v2, vX)
{-# SPECIALIZE gradientFromDelta
  :: Int -> Int -> Int -> Int -> DeltaDt Double
  -> Domains Double #-}

-- | Create vectors (representing finite maps) and an intmap
-- that store the state of evaluation.
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
-- (allocating big matrices filled with zeros is too costly,
-- especially if never used in an iteration, and adding to such matrices
-- and especially using them as scaling factors is wasteful; additionally,
-- it may not be easy to deduce the sizes of the matrices).
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
  -- Node identifiers left to be processed, with their corresponding
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
      addToVector r = \v -> if V.null v then r else v + r
      addToMatrix :: Matrix r -> Matrix r -> Matrix r
      addToMatrix r = \v -> if LA.rows v <= 0 then r else v + r
      addToArray :: OT.Array r -> OT.Array r -> OT.Array r
      addToArray r = \v -> if isTensorDummy v then r else liftVT2 (+) v r
      addToArrayS :: OS.Shape sh => OS.Array sh r -> OT.Array r -> OT.Array r
      addToArrayS r = \v -> let rs = Data.Array.Convert.convert r
                            in if isTensorDummy v
                               then rs
                               else liftVT2 (+) v rs

      -- This function modifies state comprising of vectors and a map.
      -- Its second argument is a delta expression tree node and the first
      -- is the cotangent contribution for this term tree, see below
      -- for an explanation.
      eval0 :: r -> Delta0 r -> ST s ()
      eval0 !r = \case
        Zero0 -> return ()
        Input0 (InputId i) ->
          VM.modify iMap0 (+ r) i
        Scale0 k d -> eval0 (k * r) d
        Add0 d e -> eval0 r d >> eval0 r e
        Let0 n d -> assert (case d of
                      Zero0 -> False
                      Input0{} -> False
                      Let0{} -> False  -- wasteful and nonsensical
                      _ -> True)
                    $ do
          -- In this context, by construction, @d@ is the dual component
          -- of a dual number. Let's say that, at this point, evaluation
          -- considers position (node) p out of possibly multiple positions
          -- at which that dual number resides in the term tree
          -- of the dual number representation of the objective function.
          -- If so, the @r@ argument of @eval0@, called cotangent
          -- contribution, is the partial derivative of the objective
          -- function with respect to position p.
          --
          -- If there are indeed multiple such positions (the term is shared)
          -- then, over the course of evaluation, cotangent contributions
          -- of them all are gradually accumulated in the finite
          -- maps and eventually their total sum represents the total
          -- influence of the shared term @Let0 n d@ on the objective
          -- function's behaviour. This total influence is called
          -- the cotangent of @Let0 n d@ (or, in short, the cotangent
          -- of the node identifier @n@). In other words, a cotangent of @n@
          -- is the partial derivative of the objective function with respect
          -- to the collection of all positions (subterm nodes) containing
          -- @Let0 n d@, as if the same differentiation variable was placed
          -- in all of these nodes.
          --
          -- For input terms, the eventual lists of cotangents end up
          -- in the cells of the gradient vectors that are the final
          -- result of the evaluation.
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding0 (DeltaId i) _) -> do
              dm <- readSTRef dMap0
              VM.modify dm (+ r) i
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
                VM.write dmG i r
                writeSTRef dMap0 dmG
                writeSTRefU len0 $ 2 * len
              else
                VM.write dm i r
            _ -> error "buildFinMaps: corrupted nMap"

        SumElements0 vd n -> eval1 (LA.konst r n) vd
        Index0 Zero1 _ _ -> return ()  -- shortcut
        Index0 (Input1 (InputId i)) ix k -> do
          let f v = if V.null v
                    then LA.konst 0 k V.// [(ix, r)]
                    else v V.// [(ix, v V.! ix + r)]
          VM.modify iMap1 f i
        Index0 (Let1 n d) ix k -> do
          nm <- readSTRef nMap
          case EM.lookup n nm of
            Just (DeltaBinding1 (DeltaId i) _) -> do
              dm <- readSTRef dMap1
              let f v = v V.// [(ix, v V.! ix + r)]
              VM.modify dm f i
                -- This would be an asymptotic optimization compared to
                -- the general case below, if not for the non-mutable update,
                --  which implies copying the whole @v@ vector,
                -- so it's only several times faster (same allocation,
                -- but not adding to each cell of @v@).
                -- TODO: test, benchmark, improve and extend to higher ranks
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCur1
              writeSTRefU didCur1 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding1 did d) nm
              len <- readSTRefU len1
              dm <- readSTRef dMap1
              let v = LA.konst 0 k V.// [(ix, r)]
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i v
                writeSTRef dMap1 dmG
                writeSTRefU len1 $ 2 * len
              else
                VM.write dm i v
            _ -> error "buildFinMaps: corrupted nMap"
        Index0 d ix k -> eval1 (LA.konst 0 k V.// [(ix, r)]) d

        Dot0 v vd -> eval1 (LA.scale r v) vd

        FromX0 d -> evalX (OT.scalar r) d
        FromS0 d -> evalS (OS.scalar r) d

      eval1 :: Vector r -> Delta1 r -> ST s ()
      eval1 !r = \case
        Zero1 -> return ()
        Input1 (InputId i) ->
          VM.modify iMap1 (addToVector r) i
        Scale1 k d -> eval1 (k * r) d
        Add1 d e -> eval1 r d >> eval1 r e
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
              VM.modify dm (+ r) i
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCur1
              writeSTRefU didCur1 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding1 did d) nm
              len <- readSTRefU len1
              dm <- readSTRef dMap1
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i r
                writeSTRef dMap1 dmG
                writeSTRefU len1 $ 2 * len
              else
                VM.write dm i r
            _ -> error "buildFinMaps: corrupted nMap"

        FromList1 lsd -> imapM_ (\i d -> eval0 (r V.! i) d) lsd
          -- lsd is a list (boxed vector) of scalar delta expressions
        FromVector1 lsd -> V.imapM_ (\i d -> eval0 (r V.! i) d) lsd
          -- lsd is a list (boxed vector) of scalar delta expressions
        Konst1 d _n -> V.mapM_ (`eval0` d) r
        Append1 d k e -> eval1 (V.take k r) d >> eval1 (V.drop k r) e
        Slice1 i n d len ->
          eval1 (LA.konst 0 i V.++ r V.++ LA.konst 0 (len - i - n)) d
        SumRows1 dm cols -> eval2 (MO.asColumn r cols) dm
        SumColumns1 dm rows -> eval2 (MO.asRow r rows) dm

        M_VD1 m dRow ->
          mapM_ (`eval1` dRow)
                (MO.toRows (MO.MatrixOuter (Just m) (Just r) Nothing))
        MD_V1 md row -> eval2 (MO.MatrixOuter Nothing (Just r) (Just row)) md

        FromX1 d -> evalX (OT.fromVector [V.length r] r) d
        FromS1 d -> evalS (OS.fromVector r) d

        Reverse1 d -> eval1 (V.reverse r) d
        Flatten1 rows cols d ->
          eval2 (MO.MatrixOuter (Just $ rows LA.>< cols $ V.toList r)
                                Nothing Nothing)
                d
        FlattenX1 sh d -> evalX (OT.fromVector sh r) d
        FlattenS1 d -> evalS (OS.fromVector r) d
        Build1 _n f -> V.imapM_ (\i r0 -> eval0 r0 (f i)) r

      eval2 :: MO.MatrixOuter r -> Delta2 r -> ST s ()
      eval2 !r = \case
        Zero2 -> return ()
        Input2 (InputId i) ->
          VM.modify iMap2 (addToMatrix $ MO.convertMatrixOuter r) i
        Scale2 k d -> eval2 (MO.multiplyWithOuter k r) d
        Add2 d e -> eval2 r d >> eval2 r e
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
              VM.modify dm (MO.plus r) i
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCur2
              writeSTRefU didCur2 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding2 did d) nm
              len <- readSTRefU len2
              dm <- readSTRef dMap2
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i r
                writeSTRef dMap2 dmG
                writeSTRefU len2 $ 2 * len
              else
                VM.write dm i r
            _ -> error "buildFinMaps: corrupted nMap"

        FromRows2 lvd -> zipWithM_ eval1 (MO.toRows r) (V.toList lvd)
        FromColumns2 lvd -> zipWithM_ eval1 (MO.toColumns r) (V.toList lvd)
        Konst2 d _sz -> mapM_ (V.mapM_ (`eval0` d)) $ MO.toRows r
        Transpose2 md -> eval2 (MO.transpose r) md  -- TODO: test!
        M_MD2 m md ->
          let mo = MO.MatrixOuter (Just $ LA.tr' m) Nothing Nothing
          in eval2 (MO.matMul mo r) md
        MD_M2 md m ->
          let mo = MO.MatrixOuter (Just $ LA.tr' m) Nothing Nothing
          in eval2 (MO.matMul r mo) md
        RowAppend2 d k e -> eval2 (MO.takeRows k r) d
                            >> eval2 (MO.dropRows k r) e
        ColumnAppend2 d k e -> eval2 (MO.takeColumns k r) d
                               >> eval2 (MO.dropColumns k r) e
        RowSlice2 i n d rows ->
          assert (MO.rows r == n) $
          let cols = MO.cols r
          in eval2 (MO.konst 0 i cols
                    `MO.rowAppend` r
                    `MO.rowAppend` MO.konst 0 (rows - i - n) cols)
                   d
        ColumnSlice2 i n d cols ->
          assert (MO.cols r == n) $
          let rows = MO.rows r
          in eval2 (MO.konst 0 rows i
                    `MO.columnAppend` r
                    `MO.columnAppend` MO.konst 0 rows (cols - i - n))
                   d

        AsRow2 dRow -> mapM_ (`eval1` dRow) (MO.toRows r)
        AsColumn2 dCol -> mapM_ (`eval1` dCol) (MO.toColumns r)

        FromX2 d -> evalX (OT.fromVector [MO.rows r, MO.cols r]
                                         (V.concat $ MO.toRows r)) d
        FromS2 d -> evalS (OS.fromVector $ V.concat $ MO.toRows r) d

        Flipud2 d -> eval2 (MO.flipud r) d
        Fliprl2 d -> eval2 (MO.fliprl r) d
        Reshape2 _cols d -> eval1 (V.concat $ MO.toRows r) d
        Conv2 m md ->
          let mor = MO.convertMatrixOuter r
              convolved = LA.corr2 m mor
              moc = MO.MatrixOuter (Just convolved) Nothing Nothing
          in eval2 moc md
        Build2 _ij f -> do
          let mor = MO.convertMatrixOuter r
          Numeric.LinearAlgebra.Devel.mapMatrixWithIndexM_
            (\ij r0 -> eval0 r0 (f ij)) mor

      evalX :: OT.Array r -> DeltaX r -> ST s ()
      evalX !r = \case
        ZeroX -> return ()
        InputX (InputId i) ->
          VM.modify iMapX (addToArray r) i
        ScaleX k d -> evalX (liftVT2 (*) k r) d
        AddX d e -> evalX r d >> evalX r e
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
              VM.modify dm (liftVT2 (+) r) i
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCurX
              writeSTRefU didCurX $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBindingX did d) nm
              len <- readSTRefU lenX
              dm <- readSTRef dMapX
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i r
                writeSTRef dMapX dmG
                writeSTRefU lenX $ 2 * len
              else
                VM.write dm i r
            _ -> error "buildFinMaps: corrupted nMap"

        KonstX d _sz -> mapM_ (`eval0` d) $ OT.toList r
        AppendX d k e -> case OT.shapeL r of
          n : _ -> evalX (OT.slice [(0, k)] r) d
                   >> evalX (OT.slice [(k, n - k)] r) e
          [] -> error "evalX: appending a 0-dimensional tensor"
        SliceX i n d len -> case OT.shapeL r of
          n' : rest ->
            assert (n' == n) $
            evalX (OT.concatOuter [ OT.constant (i : rest) 0
                                  , r
                                  , OT.constant (len - i - n : rest) 0 ])
                  d
          [] -> error "evalX: slicing a 0-dimensional tensor"
        IndexX d ix len ->
          let rest = OT.shapeL r
          in evalX (OT.concatOuter [ OT.constant (ix : rest) 0
                                   , OT.reshape (1 : rest) r
                                   , OT.constant (len - ix - 1 : rest) 0 ])
                   d  -- TODO: optimize for input case
        RavelFromListX ld -> do
          let lr = OTB.toList $ OT.unravel r
          mapM_ (uncurry evalX) (zip lr ld)
        ReshapeX sh _sh' d -> evalX (OT.reshape sh r) d

        From0X d -> eval0 (OT.unScalar r) d
        From1X d -> eval1 (OT.toVector r) d
        From2X d cols ->
          eval2 (MO.MatrixOuter (Just $ LA.reshape cols $ OT.toVector r)
                                Nothing Nothing)
                d
        FromSX d -> evalS (Data.Array.Convert.convert r) d

        BuildX sh f -> do
          -- Copied from Data.Array.Internal.
          let getStridesT :: OT.ShapeL -> [Int]
              getStridesT = scanr (*) 1
              ss = case getStridesT sh of
                _ : ss2 -> ss2
                [] -> error "scanr in buildDerivative"
              toIx [] _ = []
              toIx (n:ns) i = q : toIx ns r2 where (q, r2) = quotRem i n
          V.imapM_ (\i r0 -> eval0 r0 (f $ toIx ss i)) $ OT.toVector r

      evalS :: OS.Shape sh
            => OS.Array sh r -> DeltaS sh r -> ST s ()
      evalS !r = \case
        ZeroS -> return ()
        InputS (InputId i) ->
         VM.modify iMapX (addToArrayS r) i
        ScaleS k d -> evalS (liftVS2 (*) k r) d
        AddS d e -> evalS r d >> evalS r e
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
              let rs = Data.Array.Convert.convert r
              VM.modify dm (liftVT2 (+) rs) i
            Nothing -> do
              did@(DeltaId i) <- readSTRefU didCurX
              writeSTRefU didCurX $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBindingS did d) nm
              len <- readSTRefU lenX
              dm <- readSTRef dMapX
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i (Data.Array.Convert.convert r)
                writeSTRef dMapX dmG
                writeSTRefU lenX $ 2 * len
              else
                VM.write dm i (Data.Array.Convert.convert r)
            _ -> error "buildFinMaps: corrupted nMap"

#if defined(VERSION_ghc_typelits_natnormalise)
        KonstS d -> mapM_ (`eval0` d) $ OS.toList r
        AppendS (d :: DeltaS (k ': rest) r) (e :: DeltaS (l ': rest) r) ->
          evalS (OS.slice @'[ '(0, k) ] r) d
          >> evalS (OS.slice @'[ '(k, l) ] r) e
        SliceS (_ :: Proxy i) _ (d :: DeltaS (i_plus_n_plus_k ': rest) r) ->
          evalS (OS.constant @(i ': rest) 0
                 `OS.append` r
                 `OS.append` OS.constant 0)
                d
        IndexS (d :: DeltaS (ix_plus_1_plus_k ': rest) r) (_ :: Proxy ix) ->
          evalS (OS.constant @(ix ': rest) 0
                 `OS.append` OS.reshape r
                 `OS.append` OS.constant 0)
                d  -- TODO: optimize for input case
        RavelFromListS ld -> do
          let lr = OSB.toList $ OS.unravel r
          mapM_ (uncurry evalS) (zip lr ld)
        ReshapeS d -> evalS (OS.reshape r) d

        From0S d -> eval0 (OS.unScalar r) d
        From1S d -> eval1 (OS.toVector r) d
        From2S proxyCols d ->
          eval2 (MO.MatrixOuter
                   (Just $ LA.reshape (fromInteger $ natVal proxyCols)
                         $ OS.toVector r)
                   Nothing Nothing)
                d
        FromXS d -> evalX (Data.Array.Convert.convert r) d

        BuildS f -> do
          -- Copied from Data.Array.Internal.
          let getStridesT :: OS.ShapeL -> [Int]
              getStridesT = scanr (*) 1
              ss = case getStridesT sh of
                _ : ss2 -> ss2
                [] -> error "scanr in buildDerivative"
              toIx [] _ = []
              toIx (n:ns) i = q : toIx ns r2 where (q, r2) = quotRem i n
              sh = OS.shapeL r
          V.imapM_ (\i r0 -> eval0 r0 (f $ toIx ss i)) $ OS.toVector r
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
        r <- dm `VM.read` i
        unless (r == 0) $  -- a cheap optimization in case of scalars
          eval0 r d
      evalUnlessZero (DeltaBinding1 (DeltaId i) d) = do
        dm <- readSTRef dMap1
        r <- dm `VM.read` i
        eval1 r d
      evalUnlessZero (DeltaBinding2 (DeltaId i) d) = do
        dm <- readSTRef dMap2
        r <- dm `VM.read` i
        eval2 r d
      evalUnlessZero (DeltaBindingX (DeltaId i) d) = do
        dm <- readSTRef dMapX
        r <- dm `VM.read` i
        evalX r d
      evalUnlessZero (DeltaBindingS (DeltaId i) d) = do
        dm <- readSTRef dMapX
        r <- dm `VM.read` i
        evalS (Data.Array.Convert.convert r) d
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
  :: forall r. (Numeric r, Num (Vector r))
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
                (params0Init, params1Init, params2Init, paramsXInit) = do
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
          then return $! params0Init V.! i
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
              r <- eval0 d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMap0
              did@(DeltaId i) <- readSTRefU didCur0
              writeSTRefU didCur0 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding0 did d) nmNew
              len <- readSTRefU len0
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i r
                writeSTRef dMap0 dmG
                writeSTRefU len0 $ 2 * len
              else
                VM.write dm i r
              return r
            _ -> error "buildDerivative: corrupted nMap"

        SumElements0 vd _n -> LA.sumElements <$> eval1 vd
        Index0 d ix _k -> flip (V.!) ix <$> eval1 d

        Dot0 vr vd -> (<.>) vr <$> eval1 vd

        FromX0 d -> OT.unScalar <$> evalX d
        FromS0 d -> OS.unScalar <$> evalS d

      eval1 :: Delta1 r -> ST s (Vector r)
      eval1 = \case
        Zero1 -> return 0
        Input1 (InputId i) ->
          if i < dim1
          then return $! params1Init V.! i
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
              r <- eval1 d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMap1
              did@(DeltaId i) <- readSTRefU didCur1
              writeSTRefU didCur1 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding1 did d) nmNew
              len <- readSTRefU len1
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i r
                writeSTRef dMap1 dmG
                writeSTRefU len1 $ 2 * len
              else
                VM.write dm i r
              return r
            _ -> error "buildDerivative: corrupted nMap"

        FromList1 lsd -> do
          v <- mapM eval0 lsd
          return $! V.fromList v
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
          then return $! params2Init V.! i
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
              r <- eval2 d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMap2
              did@(DeltaId i) <- readSTRefU didCur2
              writeSTRefU didCur2 $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBinding2 did d) nmNew
              len <- readSTRefU len2
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i r
                writeSTRef dMap2 dmG
                writeSTRefU len2 $ 2 * len
              else
                VM.write dm i r
              return r
            _ -> error "buildDerivative: corrupted nMap"

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
        Build2 (i, j) f -> do
          l <- mapM (eval0 . f)
               $ [(i1, j1) | i1 <- [0 .. i - 1], j1 <- [0 .. j - 1]]
          return $! (j LA.>< i) l

      evalX :: DeltaX r -> ST s (OT.Array r)
      evalX = \case
        ZeroX -> return 0
        InputX (InputId i) ->
          if i < dimX
          then return $! paramsXInit V.! i
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
              r <- evalX d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMapX
              did@(DeltaId i) <- readSTRefU didCurX
              writeSTRefU didCurX $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBindingX did d) nmNew
              len <- readSTRefU lenX
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i r
                writeSTRef dMapX dmG
                writeSTRefU lenX $ 2 * len
              else
                VM.write dm i r
              return r
            _ -> error "buildDerivative: corrupted nMap"

        KonstX d sz -> OT.constant sz <$> eval0 d
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
          then return $! Data.Array.Convert.convert $ paramsXInit V.! i
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
              r <- evalS d
              nmNew <- readSTRef nMap
              dm <- readSTRef dMapX
              did@(DeltaId i) <- readSTRefU didCurX
              writeSTRefU didCurX $ succDeltaId did
              writeSTRef nMap $! EM.insert n (DeltaBindingS did d) nmNew
              len <- readSTRefU lenX
              if i >= len then do
                dmG <- VM.unsafeGrow dm len
                VM.write dmG i (Data.Array.Convert.convert r)
                writeSTRef dMapX dmG
                writeSTRefU lenX $ 2 * len
              else
                VM.write dm i (Data.Array.Convert.convert r)
              return r
            _ -> error "buildDerivative: corrupted nMap"

#if defined(VERSION_ghc_typelits_natnormalise)
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

{- Note [SumElements0]
~~~~~~~~~~~~~~~~~~~~~~

The second argument of SumElements0 is the length of the vector
to be summed. Given that we sum a delta-expression representing
a vector, we can't call Vector.length on it, so the length needs
to be recorded in the constructor. Alternatively, it could be
recorded in the Delta1 argument to SumElements0. This is what
shaped tensors do at the type level, so for DeltaS the argument
would not be needed.

Sum of vector elements can be implemented using a delta-expression
primitive SumElements0 as well as without this primitive, referring
only to the primitive Index0:

https://github.com/Mikolaj/horde-ad/blob/d069a45773ed849913b5ebd0345153072f304fd9/src/HordeAd.Core.DualNumber.hs#L125-L143

which is confirmed by tests to be equivalent in three different
implementations:

https://github.com/Mikolaj/horde-ad/blob/d069a45773ed849913b5ebd0345153072f304fd9/test/TestSingleGradient.hs#L116-L128

and proved to be prohibitively slow in the two implementations
that don't use the SumElements0 primitive in benchmarks (despite
an ingenious optimization of the common case of Index0 applied to a input):

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
