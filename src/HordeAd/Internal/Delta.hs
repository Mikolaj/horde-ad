{-# LANGUAGE CPP, DataKinds, GADTs, GeneralizedNewtypeDeriving, KindSignatures,
             RankNTypes, StandaloneDeriving, TypeOperators, UnboxedTuples #-}
#if !MIN_VERSION_base(4,16,0)
{-# LANGUAGE IncoherentInstances #-}
#endif
#if defined(VERSION_ghc_typelits_natnormalise)
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
#endif
-- | The second component of dual numbers, @Delta@, with its semantics.
-- Neel Krishnaswami calls it \"sparse vector expressions\",
-- and indeed even in the simplest case of an objective function
-- defined on scalars only, the codomain of the function that computes
-- gradients from such delta expressions is a set of vectors, because
-- the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
--
-- The \'sparsity\' is less obvious when the domain of the function consists
-- of multiple vectors, matrices and tensors and when the expressions themselves
-- contain vectors, matrices and tensors. However, a single tiny delta
-- expression (e.g., a sum of two variables) may denote a vector of matrices.
-- Even a delta expression containing a big matrix denotes something much
-- bigger: a whole vector of such matrices and more.
--
-- The algebraic structure here is an extension of vector space.
-- The crucial extra constructor of a variable is used both to represent
-- sharing in order to avoid exponential blowup and to replace the one-hot
-- access to parameters with something cheaper and more uniform.
-- A lot of the remaining additional structure is for introducing
-- and reducing dimensions (ranks).
--
-- This is an internal API now, superseded by "HordeAd.Core.DualClass"
-- that permits other kinds of second component of dual numbers,
-- e.g., the same as primal component, for fast computation
-- of forward derivatives (because @derivativeFromDelta@ below,
-- computing derivatives from delta-expressions, is slow once the expressions
-- grow large enough to affect cache misses).
module HordeAd.Internal.Delta
  ( -- * Abstract syntax trees of the delta expressions
    Delta0 (..), Delta0' (..)
  , Delta1 (..), Delta1' (..)
  , Delta2 (..), Delta2' (..)
  , DeltaX (..), DeltaX' (..)
  , DeltaS (..), DeltaS' (..)
  , -- * Delta expression identifiers
    DeltaId, toDeltaId, convertDeltaId
  , -- * Evaluation of the delta expressions
    Domain0, Domain1, Domain2, DomainX, Domains
  , gradientFromDelta, derivativeFromDelta
  , isTensorDummy
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
import qualified Data.IntMap.Strict as IM
import           Data.Kind (Type)
import           Data.Primitive (Prim)
import           Data.Proxy (Proxy)
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import           Data.STRef.Unboxed (STRefU, newSTRefU, readSTRefU, writeSTRefU)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector, ( #> ), (<.>))
import qualified Numeric.LinearAlgebra as HM

import qualified HordeAd.Internal.MatrixOuter as MO
import           HordeAd.Internal.OrthotopeOrphanInstances (liftVS2, liftVT2)

-- * Abstract syntax trees of the delta expressions

-- | This is the grammar of delta-expressions at tensor rank 0, that is,
-- at scalar level. The first few operations have analogues
-- at the level of vectors, matrices and arbitrary tensors.
--
-- For each choice of the underlying scalar type @r@,
-- we have several primitive differentiable types based on the scalar:
-- the scalar type @r@ itself, @Vector r@, @Matrix r@ and tensors.
-- Many operations span the ranks and so span the datatypes, which makes
-- the datatypes mutually recursive.
--
-- The identifier that is the first argument of @Delta0@ marks
-- the identity of a subterm as part of the whole global term tree.
--
-- The per-rank identifier that is the second argument of @Delta0@
-- is an index into a contigous vector of gradient or derivative components
-- (partial gradients/derivatives wrt that term's position?) corresponding
-- to subterms of that rank. There is no corresponding argument to the
-- @Zero0@ constructor, because the term not only does not contribute
-- to the derivative (similarly as @Input0@), but we are not even interested
-- in what the (partial) gradient for that subterm position would be.
data Delta0 r =
    Delta0 Int (Delta0' r)
  | Zero0
  | Input0 (DeltaId r)
data Delta0' r =
    Scale0 r (Delta0 r)
  | Add0 (Delta0 r) (Delta0 r)

  | SumElements0 (Delta1 r) Int  -- ^ see Note [SumElements0]
  | Index0 (Delta1 r) Int Int  -- ^ second integer is the length of the vector

  | Dot0 (Vector r) (Delta1 r)  -- ^ Dot0 v vd == SumElements0 (Scale1 v vd) n

  | FromX0 (DeltaX r)  -- ^ one of many conversions
  | FromS0 (DeltaS '[] r)

deriving instance (Show r, Numeric r) => Show (Delta0 r)
deriving instance (Show r, Numeric r) => Show (Delta0' r)

-- | This is the grammar of delta-expressions at tensor rank 1, that is,
-- at vector level.
data Delta1 r =
    Delta1 Int (Delta1' r)
  | Zero1
  | Input1 (DeltaId (Vector r))
data Delta1' r =
    Scale1 (Vector r) (Delta1 r)
  | Add1 (Delta1 r) (Delta1 r)

  | Seq1 (Data.Vector.Vector (Delta0 r))  -- ^ "unboxing" conversion
  | Konst1 (Delta0 r) Int  -- ^ length; needed only for forward derivative
  | Append1 (Delta1 r) Int (Delta1 r)  -- ^ the length of the first argument
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

deriving instance (Show r, Numeric r) => Show (Delta1 r)
deriving instance (Show r, Numeric r) => Show (Delta1' r)

-- | This is the grammar of delta-expressions at tensor rank 2, that is,
-- at matrix level.
data Delta2 r =
    Delta2 Int (Delta2' r)
  | Zero2
  | Input2 (DeltaId (Matrix r))
data Delta2' r =
    Scale2 (Matrix r) (Delta2 r)
  | Add2 (Delta2 r) (Delta2 r)

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

deriving instance (Show r, Numeric r) => Show (Delta2 r)
deriving instance (Show r, Numeric r) => Show (Delta2' r)

-- | This is the grammar of delta-expressions at arbitrary tensor rank.
--
-- Warning: not tested enough nor benchmarked.
data DeltaX r =
    DeltaX Int (DeltaX' r)
  | ZeroX
  | InputX (DeltaId (OT.Array r))
data DeltaX' r =
    ScaleX (OT.Array r) (DeltaX r)
  | AddX (DeltaX r) (DeltaX r)

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

deriving instance (Show r, Numeric r) => Show (DeltaX r)
deriving instance (Show r, Numeric r) => Show (DeltaX' r)

-- | This is the grammar of delta-expressions at arbitrary tensor rank,
-- the fully typed Shaped version.
--
-- Warning: not tested enough nor benchmarked.
data DeltaS :: [Nat] -> Type -> Type where
  DeltaS :: Int -> DeltaS' sh r -> DeltaS sh r
  ZeroS :: DeltaS sh r
  InputS :: DeltaId (OS.Array sh r) -> DeltaS sh r
data DeltaS' :: [Nat] -> Type -> Type where
  ScaleS :: OS.Array sh r -> DeltaS sh r -> DeltaS' sh r
  AddS :: DeltaS sh r -> DeltaS sh r -> DeltaS' sh r

  KonstS :: Delta0 r -> DeltaS' sh r
  AppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
          => DeltaS (m ': sh) r -> DeltaS (n ': sh) r
          -> DeltaS' ((m + n) ': sh) r
    -- ^ Append two arrays along the outermost dimension.
  SliceS :: (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
         => Proxy i -> Proxy n -> DeltaS (i + n + k ': rest) r
         -> DeltaS' (n ': rest) r
    -- ^ Extract a slice of an array along the outermost dimension.
  IndexS :: (KnownNat ix, KnownNat k, OS.Shape rest)
         => DeltaS (ix + 1 + k ': rest) r -> Proxy ix -> DeltaS' rest r
    -- ^ The sub-tensors at the given index of the outermost dimension.
  RavelFromListS :: (KnownNat k, OS.Shape rest)
                 => [DeltaS rest r] -> DeltaS' (k : rest) r
    -- ^ Create a tensor from a list treated as the outermost dimension.
  ReshapeS :: (OS.Shape sh, OS.Shape sh', OS.Size sh ~ OS.Size sh')
           => DeltaS sh r -> DeltaS' sh' r
    -- ^ Change the shape of the tensor.

  From0S :: Delta0 r -> DeltaS' '[] r
  From1S :: Delta1 r -> DeltaS' '[n] r
  From2S :: KnownNat cols
         => Proxy cols -> Delta2 r -> DeltaS' '[rows, cols] r
  FromXS :: DeltaX r -> DeltaS' sh r

instance Show (DeltaS sh r) where
  show _ = "a DeltaS delta expression"
instance Show (DeltaS' sh r) where
  show _ = "a DeltaS' delta expression"


-- * Delta expression identifiers

newtype DeltaId a = DeltaId Int
  deriving (Show, Prim)
    -- no Eq instance to limit hacks outside this module

-- | Wrap non-negative (only!) integers in the `DeltaId` newtype.
toDeltaId :: Int -> DeltaId a
toDeltaId i = assert (i >= 0) $ DeltaId i

convertDeltaId :: DeltaId (OT.Array r) -> DeltaId (OS.Array sh r)
convertDeltaId (DeltaId i) = DeltaId i

-- The key property is that it preserves the phantom type.
succDeltaId :: DeltaId a -> DeltaId a
succDeltaId (DeltaId i) = DeltaId (succ i)


-- * Evaluation of the delta expressions

data DeltaBinding r =
    DeltaBinding0 (DeltaId r) (Delta0' r)
  | DeltaBinding1 (DeltaId (Vector r)) (Delta1' r)
  | DeltaBinding2 (DeltaId (Matrix r)) (Delta2' r)
  | DeltaBindingX (DeltaId (OT.Array r)) (DeltaX' r)
  | forall sh. OS.Shape sh
    => DeltaBindingS (DeltaId (OT.Array r)) (DeltaS' sh r)

-- | Helper definitions to shorten type signatures.
type Domain0 r = Vector r

type Domain1 r = Data.Vector.Vector (Vector r)

type Domain2 r = Data.Vector.Vector (Matrix r)

type DomainX r = Data.Vector.Vector (OT.Array r)

type Domains r = (Domain0 r, Domain1 r, Domain2 r, DomainX r)

-- | Delta expressions naturally denote forward derivatives,
-- as encoded in function 'derivativeFromDelta'. However, we are more
-- interested in computing gradients, which is what @gradientFromDelta@ does.
-- The two functions are bound by the equation from Lemma 5 from the paper
-- "Provably correct, asymptotically efficient, higher-order reverse-mode
-- automatic differentiation":
--
-- > dt <.> derivativeFromDelta ct d ds = gradientFromDelta ct d dt <.> ds
--
-- where @\<.\>@ denotes generalized dot product (multiplying
-- all tensors element-wise and summing the results),
-- @st@ contains bindings of delta variables and @d@ is the top level
-- delta expression from translation of the objective function @f@ to dual
-- numbers, @ds@ belongs to the domain of @f@ and @dt@ to the codomain.
-- We omitted for clarity the @dim0@, @dim1@, @dim2@ and @dimX@ arguments
-- that are the lengths of vectors of the tensors in the domain of @f@.
--
-- Intuitively, @ds@ is a tiny perturbation of the arguments of @f@,
-- for which we compute the derivative, that is, the induced change
-- in the result of @f@. Similarly, @dt@ is a tiny perturbation of the
-- result of @f@, for which we compute the gradient, that is, the change
-- of arguments of @f@ sufficient to cause the perturbation.
-- Note that the scaling factor @r@ in functions @eval*@ in @gradientFromDelta@
-- locally plays the role of @dt@, just as the argument @parameters@
-- in @eval*@ in @derivativeFromDelta@ corresponds to @ds@.
--
-- Let's first discuss in detail the semantics of delta-expressions
-- in terms of forward derivatives, since it's more straightforward.
-- Let @r@ be the type of underlying scalars. Let @f@ be a mathematical
-- differentiable function that takes a collection of type @C@
-- of arguments and produces a single result of type @r@.
-- Let a dual number counterpart of @f@ applied to a collection
-- of parameters @P@ of type @C@ be represented as a Haskell value @b@.
-- Let @d :: Delta0 r@ be the closed delta expression that is the second
-- component of @b@, let @ds@ belong to @C@. The semantics of @d@ is a linear
-- function from @C@ to @r@ that is the derivative of @f@ at point @P@
-- with respect to the perturbation @ds@. The mathematical formula
-- for the derivative follows straightforwardly the syntactic form
-- of the delta expression @d@ (see 'derivativeFromDelta').
--
-- Let's now describe the semantics of closed delta expression @d@
-- as the gradient of @f@ at point @P@ with respect to a @dt@ that belongs
-- to @r@. Here the semantics of @d@ is a collection of four finite maps
-- (vectors) @v0@, @v1@, @v2@, @vX@, corresponding to @C@,
-- each map @vi@ taking indexes of type @DeltaId ai@ to values of type @ai@,
-- where @a0@ is @r@, @a1@ is @Vector r@, @a2@ is @Matrix r@
-- and @aX@ is the type of tensors of @r@.
-- The value of @vi@ at index @DeltaId k@ is the partial derivative
-- of function @f@ at @P@ with respect to its parameter of type @ai@.
-- The position of the @ai@ parameter is represented by @DeltaId k@
-- (in other words, the partial derivative is with respect to a variable
-- quantity tagged with @DeltaId k@) and its value comes from @dt@.
--
-- The semantics of a delta expression that is not closed but contains
-- occurrences of variables that do not correspond to parameters of @f@ is only
-- defined in the context of four vectors that contain values associated
-- to its free variables or, alternatively, of bindings from which the values
-- can be computed, or of a mixture of both. This semantics does not change
-- if a bound expression is substituted for a variable instead of being used
-- to compute a value. (Note however that a computed value can't be
-- substituted for all occurrences of the variable in an expression,
-- because the "computing backwards" trick, needed to get gradients
-- from derivative expressions, computes a value for each occurrence
-- of a variable separately and sums over all occurrences instead
-- of substituting a single value into each occurrence.)
--
-- Function @gradientFromDelta@ computes the four vectors described above.
-- Requested lengths of the vectors are given in the first few arguments.
-- The delta state contains a list of mutually-referencing delta bindings
-- that are to be evaluated, in the given order, starting with the top-level
-- binding of a scalar type provided in the next argument and with respect
-- to perturbation @dt@ (usually set to @1@) in the last argument.
gradientFromDelta
  :: (Eq r, Numeric r, Num (Vector r))
  => Int -> Int -> Int -> Int -> Delta0 r -> r
  -> Domains r
gradientFromDelta dim0 dim1 dim2 dimX deltaTopLevel dt =
-- traceShow (dim0, dim1, dim2, dimX) $
  -- This is morally @V.create@ and so totally safe,
  -- but we can't just call @V.create@ thrice, because it would run
  -- the @ST@ action thrice, so we inline and extend @V.create@ here.
  runST $ do
    (iMap0, iMap1, iMap2, iMapX)
      <- buildFinMaps dim0 dim1 dim2 dimX deltaTopLevel dt
    v0 <- V.unsafeFreeze iMap0
    v1 <- V.unsafeFreeze iMap1
    v2 <- V.unsafeFreeze iMap2
    vX <- V.unsafeFreeze iMapX
    -- Convert to normal matrices, but only the portion of vector
    -- that is not discarded.
    return (v0, v1, v2, vX)
{-# SPECIALIZE gradientFromDelta
  :: Int -> Int -> Int -> Int -> Delta0 Double -> Double
  -> Domains Double #-}

-- | Create vectors (representing finite maps) that hold delta-variable
-- values. They are initialized with dummy values so that it's cheap to check
-- if any update has already been performed to a cell (allocating big matrices
-- filled with zeros is too costly, especially if never used in an iteration,
-- and adding to such matrices and especially using them as scaling factors
-- is wasteful). The vectors are longer than those representing objective
-- function parameters (e.g., @deltaCounter0@ vs @dim0@), because variables
-- represent not only parameters, but also the bindings that prevent blowup
-- via delta-expression duplication.
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
          , STRef s (IM.IntMap (DeltaBinding r)) )
initializeFinMaps dim0 dim1 dim2 dimX = do
  iMap0 <- VM.replicate dim0 0
  iMap1 <- VM.replicate dim1 (V.empty :: Vector r)
  iMap2 <- VM.replicate dim2 (HM.fromRows [])
  iMapX <- VM.replicate dimX dummyTensor
  -- These index into the respective four vectors below.
  ref0 <- newSTRefU (DeltaId 0)
  ref1 <- newSTRefU (DeltaId 0)
  ref2 <- newSTRefU (DeltaId 0)
  refX <- newSTRefU (DeltaId 0)
  rMap0' <- VM.replicate (max 1000 dim0) 0  -- correct value; below are dummy
  rMap1' <- VM.replicate (max 1000 dim1) (V.empty :: Vector r)
  rMap2' <- VM.replicate (max 1000 dim2) MO.emptyMatrixOuter
  rMapX' <- VM.replicate (max 1000 dimX) dummyTensor
  rMap0 <- newSTRef rMap0'
  rMap1 <- newSTRef rMap1'
  rMap2 <- newSTRef rMap2'
  rMapX <- newSTRef rMapX'
  -- These keep current lengths of the vectors above.
  len0 <- newSTRefU (VM.length rMap0')
  len1 <- newSTRefU (VM.length rMap1')
  len2 <- newSTRefU (VM.length rMap2')
  lenX <- newSTRefU (VM.length rMapX')
  dMap <- newSTRef IM.empty
  return ( iMap0, iMap1, iMap2, iMapX
         , ref0, ref1, ref2, refX
         , rMap0, rMap1, rMap2, rMapX
         , len0, len1, len2, lenX
         , dMap )

buildFinMaps :: forall s r. (Eq r, Numeric r, Num (Vector r))
             => Int -> Int -> Int -> Int -> Delta0 r -> r
             -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                     , Data.Vector.Mutable.MVector s (Vector r)
                     , Data.Vector.Mutable.MVector s (Matrix r)
                     , Data.Vector.Mutable.MVector s (OT.Array r) )
buildFinMaps dim0 dim1 dim2 dimX deltaTopLevel dt = do
  ( iMap0, iMap1, iMap2, iMapX
   ,ref0, ref1, ref2, refX
   ,rMap0, rMap1, rMap2, rMapX
   ,len0, len1, len2, lenX
   ,dMap )
    <- initializeFinMaps dim0 dim1 dim2 dimX
  let addToVector :: Vector r -> Vector r -> Vector r
      addToVector r = \v -> if V.null v then r else v + r
      addToMatrix :: Matrix r -> Matrix r -> Matrix r
      addToMatrix r = \v -> if HM.rows v <= 0 then r else v + r
      addToArray :: OT.Array r -> OT.Array r -> OT.Array r
      addToArray r = \v -> if isTensorDummy v then r else liftVT2 (+) v r
      addToArrayS :: OS.Shape sh => OS.Array sh r -> OT.Array r -> OT.Array r
      addToArrayS r = \v -> let rs = Data.Array.Convert.convert r
                            in if isTensorDummy v
                               then rs
                               else liftVT2 (+) v rs
      eval0 :: r -> Delta0 r -> ST s ()
      eval0 _ Zero0 = return ()
      eval0 !r (Input0 (DeltaId i)) =
        VM.modify iMap0 (+ r) i
      eval0 !r (Delta0 n d) = do
        rm <- readSTRef rMap0
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBinding0 (DeltaId i) _) ->
            VM.modify rm (+ r) i
          Nothing -> do
            did@(DeltaId i) <- readSTRefU ref0
            writeSTRefU ref0 $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBinding0 did d) im
            len <- readSTRefU len0
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i r
              writeSTRef rMap0 rmG
              writeSTRefU len0 $ 2 * len
            else
              VM.write rm i r
          _ -> error "buildFinMaps: corrupted dMap"
      eval0' :: r -> Delta0' r -> ST s ()
      eval0' !r = \case
        Scale0 k d -> eval0 (k * r) d
        Add0 d e -> eval0 r d >> eval0 r e

        SumElements0 vd n -> eval1 (HM.konst r n) vd
        Index0 (Input1 (DeltaId i)) ix k | i >= 0 -> do
          let f v = if V.null v
                    then HM.konst 0 k V.// [(ix, r)]
                    else v V.// [(ix, v V.! ix + r)]
          VM.modify iMap1 f i
            -- This would be an asymptotic optimization compared to
            -- the general case below, if not for the non-mutable update,
            -- which involves copying the whole vector, so it's just
            -- several times faster (same allocation, but not adding vectors).
            -- TODO: does it make sense to extend this beyond @Input1@?
        Index0 d ix k -> eval1 (HM.konst 0 k V.// [(ix, r)]) d

        Dot0 v vd -> eval1 (HM.scale r v) vd

        FromX0 d -> evalX (OT.scalar r) d
        FromS0 d -> evalS (OS.scalar r) d

      eval1 :: Vector r -> Delta1 r -> ST s ()
      eval1 _ Zero1 = return ()
      eval1 !r (Input1 (DeltaId i)) =
        VM.modify iMap1 (addToVector r) i
      eval1 !r (Delta1 n d) = do
        rm <- readSTRef rMap1
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBinding1 (DeltaId i) _) ->
            VM.modify rm (+ r) i
          Nothing -> do
            did@(DeltaId i) <- readSTRefU ref1
            writeSTRefU ref1 $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBinding1 did d) im
            len <- readSTRefU len1
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i r
              writeSTRef rMap1 rmG
              writeSTRefU len1 $ 2 * len
            else
              VM.write rm i r
          _ -> error "buildFinMaps: corrupted dMap"
      eval1' :: Vector r -> Delta1' r -> ST s ()
      eval1' !r = \case
        Scale1 k d -> eval1 (k * r) d
        Add1 d e -> eval1 r d >> eval1 r e

        Seq1 lsd -> V.imapM_ (\i d -> eval0 (r V.! i) d) lsd
        Konst1 d _n -> V.mapM_ (`eval0` d) r
        Append1 d k e -> eval1 (V.take k r) d >> eval1 (V.drop k r) e
        Slice1 i n d len ->
          eval1 (HM.konst 0 i V.++ r V.++ HM.konst 0 (len - i - n)) d
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
          eval2 (MO.MatrixOuter (Just $ rows HM.>< cols $ V.toList r)
                                Nothing Nothing)
                d
        FlattenX1 sh d -> evalX (OT.fromVector sh r) d
        FlattenS1 d -> evalS (OS.fromVector r) d

      eval2 :: MO.MatrixOuter r -> Delta2 r -> ST s ()
      eval2 _ Zero2 = return ()
      eval2 !r (Input2 (DeltaId i)) =
        VM.modify iMap2 (addToMatrix $ MO.convertMatrixOuter r) i
      eval2 !r (Delta2 n d) = do
        rm <- readSTRef rMap2
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBinding2 (DeltaId i) _) ->
            VM.modify rm (MO.plus r) i
          Nothing -> do
            did@(DeltaId i) <- readSTRefU ref2
            writeSTRefU ref2 $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBinding2 did d) im
            len <- readSTRefU len2
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i r
              writeSTRef rMap2 rmG
              writeSTRefU len2 $ 2 * len
            else
              VM.write rm i r
          _ -> error "buildFinMaps: corrupted dMap"
      eval2' :: MO.MatrixOuter r -> Delta2' r -> ST s ()
      eval2' !r = \case
        Scale2 k d -> eval2 (MO.multiplyWithOuter k r) d
        Add2 d e -> eval2 r d >> eval2 r e

        FromRows2 lvd -> zipWithM_ eval1 (MO.toRows r) (V.toList lvd)
        FromColumns2 lvd -> zipWithM_ eval1 (MO.toColumns r) (V.toList lvd)
        Konst2 d _sz -> mapM_ (V.mapM_ (`eval0` d)) $ MO.toRows r
        Transpose2 md -> eval2 (MO.transpose r) md  -- TODO: test!
        M_MD2 m md ->
          let mo = MO.MatrixOuter (Just $ HM.tr' m) Nothing Nothing
          in eval2 (MO.matMul mo r) md
        MD_M2 md m ->
          let mo = MO.MatrixOuter (Just $ HM.tr' m) Nothing Nothing
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
              convolved = HM.corr2 m mor
              moc = MO.MatrixOuter (Just convolved) Nothing Nothing
          in eval2 moc md

      evalX :: OT.Array r -> DeltaX r -> ST s ()
      evalX _ ZeroX = return ()
      evalX !r (InputX (DeltaId i)) =
        VM.modify iMapX (addToArray r) i
      evalX !r (DeltaX n d) = do
        rm <- readSTRef rMapX
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBindingX (DeltaId i) _) ->
            VM.modify rm (liftVT2 (+) r) i
          Nothing -> do
            did@(DeltaId i) <- readSTRefU refX
            writeSTRefU refX $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBindingX did d) im
            len <- readSTRefU lenX
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i r
              writeSTRef rMapX rmG
              writeSTRefU lenX $ 2 * len
            else
              VM.write rm i r
          _ -> error "buildFinMaps: corrupted dMap"
      evalX' :: OT.Array r -> DeltaX' r -> ST s ()
      evalX' !r = \case
        ScaleX k d -> evalX (liftVT2 (*) k r) d
        AddX d e -> evalX r d >> evalX r e

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
          eval2 (MO.MatrixOuter (Just $ HM.reshape cols $ OT.toVector r)
                                Nothing Nothing)
                d
        FromSX d -> evalS (Data.Array.Convert.convert r) d

      evalS :: OS.Shape sh
            => OS.Array sh r -> DeltaS sh r -> ST s ()
      evalS _ ZeroS = return ()
      evalS !r (InputS (DeltaId i)) =
        VM.modify iMapX (addToArrayS r) i
      evalS !r (DeltaS n d) = do
        rm <- readSTRef rMapX
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBindingS (DeltaId i) _) -> do
            let rs = Data.Array.Convert.convert r
            VM.modify rm (liftVT2 (+) rs) i
          Nothing -> do
            did@(DeltaId i) <- readSTRefU refX
            writeSTRefU refX $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBindingS did d) im
            len <- readSTRefU lenX
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i (Data.Array.Convert.convert r)
              writeSTRef rMapX rmG
              writeSTRefU lenX $ 2 * len
            else
              VM.write rm i (Data.Array.Convert.convert r)
          _ -> error "buildFinMaps: corrupted dMap"
      evalS' :: OS.Shape sh
             => OS.Array sh r -> DeltaS' sh r -> ST s ()
      evalS' !r = \case
        ScaleS k d -> evalS (liftVS2 (*) k r) d
        AddS d e -> evalS r d >> evalS r e

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
                   (Just $ HM.reshape (fromInteger $ natVal proxyCols)
                         $ OS.toVector r)
                   Nothing Nothing)
                d
        FromXS d -> evalX (Data.Array.Convert.convert r) d
#endif

  eval0 dt deltaTopLevel

  let evalUnlessZero :: DeltaBinding r -> ST s ()
      evalUnlessZero (DeltaBinding0 (DeltaId i) d) = do
        rm <- readSTRef rMap0
        r <- rm `VM.read` i
        unless (r == 0) $  -- a cheap optimization in case of scalars
          eval0' r d
      evalUnlessZero (DeltaBinding1 (DeltaId i) d) = do
        rm <- readSTRef rMap1
        r <- rm `VM.read` i
        eval1' r d
      evalUnlessZero (DeltaBinding2 (DeltaId i) d) = do
        rm <- readSTRef rMap2
        r <- rm `VM.read` i
        eval2' r d
      evalUnlessZero (DeltaBindingX (DeltaId i) d) = do
        rm <- readSTRef rMapX
        r <- rm `VM.read` i
        evalX' r d
      evalUnlessZero (DeltaBindingS (DeltaId i) d) = do
        rm <- readSTRef rMapX
        r <- rm `VM.read` i
        evalS' (Data.Array.Convert.convert r) d
      evalFromdMap :: ST s ()
      evalFromdMap = do
        im <- readSTRef dMap
        case IM.maxView im of
          Just (b, im2) -> do
            writeSTRef dMap $! im2
            evalUnlessZero b
            evalFromdMap
          Nothing -> return ()  -- loop ends
  evalFromdMap

  return (iMap0, iMap1, iMap2, iMapX)
{-# SPECIALIZE buildFinMaps
  :: Int -> Int -> Int -> Int -> Delta0 Double -> Double
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

-- | This mimics 'initializeFinMaps', but in reverse. Perhaps this can be
-- simplified, but at least the simplest formulation does not honour sharing,
-- evaluating shared subexpressions repeatedly.
buildDerivative
  :: forall s r. (Numeric r, Num (Vector r))
  => Int -> Int -> Int -> Int -> Delta0 r -> Domains r
  -> ST s r
buildDerivative dim0 dim1 dim2 dimX deltaTopLevel
                (params0Init, params1Init, params2Init, paramsXInit) = do
  ( _, _, _, _
   ,ref0, ref1, ref2, refX
   ,rMap0, rMap1, _, rMapX
   ,len0, len1, len2, lenX
   ,dMap )
   <- initializeFinMaps dim0 dim1 dim2 dimX
  -- We use normal hmatrix matrices rather than the sparse replacement.
  lenOuter <- readSTRefU len2
  rMap2' :: Data.Vector.Mutable.MVector s (Matrix r)
    <- VM.replicate lenOuter (HM.fromRows [])
  rMap2 <- newSTRef rMap2'
  let eval0 :: Delta0 r -> ST s r
      eval0 Zero0 = return 0
      eval0 (Input0 (DeltaId i)) =
        if i < dim0
        then return $! params0Init V.! i
        else error "derivativeFromDelta.eval': wrong index for an input"
      eval0 (Delta0 n d) = do
        -- This is too complex, but uses components already defined
        -- for initializeFinMaps and some of a similar code.
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBinding0 (DeltaId i) _) -> do
            rm <- readSTRef rMap0
            VM.read rm i
          Nothing -> do
            r <- eval0' d
            imNew <- readSTRef dMap
            rm <- readSTRef rMap0
            did@(DeltaId i) <- readSTRefU ref0
            writeSTRefU ref0 $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBinding0 did d) imNew
            len <- readSTRefU len0
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i r
              writeSTRef rMap0 rmG
              writeSTRefU len0 $ 2 * len
            else
              VM.write rm i r
            return r
          _ -> error "buildDerivative: corrupted dMap"
      eval0' :: Delta0' r -> ST s r
      eval0' = \case
        Scale0 k d -> (k *) <$> eval0 d
        Add0 d e -> liftM2 (+) (eval0 d) (eval0 e)

        SumElements0 vd _n -> HM.sumElements <$> eval1 vd
        Index0 d ix _k -> flip (V.!) ix <$> eval1 d

        Dot0 vr vd -> (<.>) vr <$> eval1 vd

        FromX0 d -> OT.unScalar <$> evalX d
        FromS0 d -> OS.unScalar <$> evalS d

      eval1 :: Delta1 r -> ST s (Vector r)
      eval1 Zero1 = return 0
      eval1 (Input1 (DeltaId i)) =
        if i < dim1
        then return $! params1Init V.! i
        else error "derivativeFromDelta.eval': wrong index for an input"
      eval1 (Delta1 n d) = do
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBinding1 (DeltaId i) _) -> do
            rm <- readSTRef rMap1
            VM.read rm i
          Nothing -> do
            r <- eval1' d
            imNew <- readSTRef dMap
            rm <- readSTRef rMap1
            did@(DeltaId i) <- readSTRefU ref1
            writeSTRefU ref1 $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBinding1 did d) imNew
            len <- readSTRefU len1
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i r
              writeSTRef rMap1 rmG
              writeSTRefU len1 $ 2 * len
            else
              VM.write rm i r
            return r
          _ -> error "buildDerivative: corrupted dMap"
      eval1' :: Delta1' r -> ST s (Vector r)
      eval1' = \case
        Scale1 k d -> (k *) <$> eval1 d
        Add1 d e -> liftM2 (+) (eval1 d) (eval1 e)

        Seq1 lsd -> do
          v <- V.mapM eval0 lsd
          return $! V.convert v
        Konst1 d n -> flip HM.konst n <$> eval0 d
        Append1 d _k e -> liftM2 (V.++) (eval1 d) (eval1 e)
        Slice1 i n d _len -> V.slice i n <$> eval1 d
        SumRows1 dm _cols ->
          V.fromList <$> map HM.sumElements <$> HM.toRows <$> eval2 dm
        SumColumns1 dm _rows ->
          V.fromList <$> map HM.sumElements <$> HM.toColumns <$> eval2 dm

        M_VD1 m dRow -> ( #> ) m <$> eval1 dRow
        MD_V1 md row -> flip ( #> ) row <$> eval2 md

        FromX1 d -> OT.toVector <$> evalX d
        FromS1 d -> OS.toVector <$> evalS d

        Reverse1 d -> V.reverse <$> eval1 d
        Flatten1 _rows _cols d -> HM.flatten <$> eval2 d
        FlattenX1 _sh d -> OT.toVector <$> evalX d
        FlattenS1 d -> OS.toVector <$> evalS d

      eval2 :: Delta2 r -> ST s (Matrix r)
      eval2 Zero2 = return 0
      eval2 (Input2 (DeltaId i)) =
        if i < dim2
        then return $! params2Init V.! i
        else error "derivativeFromDelta.eval': wrong index for an input"
      eval2 (Delta2 n d) = do
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBinding2 (DeltaId i) _) -> do
            rm <- readSTRef rMap2
            VM.read rm i
          Nothing -> do
            r <- eval2' d
            imNew <- readSTRef dMap
            rm <- readSTRef rMap2
            did@(DeltaId i) <- readSTRefU ref2
            writeSTRefU ref2 $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBinding2 did d) imNew
            len <- readSTRefU len2
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i r
              writeSTRef rMap2 rmG
              writeSTRefU len2 $ 2 * len
            else
              VM.write rm i r
            return r
          _ -> error "buildDerivative: corrupted dMap"
      eval2' :: Delta2' r -> ST s (Matrix r)
      eval2' = \case
        Scale2 k d -> (k *) <$> eval2 d
        Add2 d e -> liftM2 (+) (eval2 d) (eval2 e)

        FromRows2 lvd -> do
          l <- mapM eval1 $ V.toList lvd
          return $! HM.fromRows l
        FromColumns2 lvd -> do
          l <- mapM eval1 $ V.toList lvd
          return $! HM.fromColumns l
        Konst2 d sz -> flip HM.konst sz <$> eval0 d
        Transpose2 md -> HM.tr' <$> eval2 md
        M_MD2 m md -> (HM.<>) m <$> eval2 md
        MD_M2 md m -> flip (HM.<>) m <$> eval2 md
        RowAppend2 d _k e -> liftM2 (HM.===) (eval2 d) (eval2 e)
        ColumnAppend2 d _k e -> liftM2 (HM.|||) (eval2 d) (eval2 e)
        RowSlice2 i n d _rows ->
          HM.takeRows n <$> HM.dropRows i <$> eval2 d
        ColumnSlice2 i n d _cols ->
          HM.takeColumns n <$> HM.dropColumns i <$> eval2 d

        AsRow2 dRow -> HM.asRow <$> eval1 dRow  -- TODO: risky
        AsColumn2 dCol -> HM.asColumn <$> eval1 dCol  -- TODO: risky

        FromX2 d -> do
          t <- evalX d
          case OT.shapeL t of
            [_rows, cols] -> return $! HM.reshape cols $ OT.toVector t
            _ -> error "eval2: wrong tensor dimensions"
        FromS2 d -> do
          t <- evalS d
          case OS.shapeL t of
            [_rows, cols] -> return $! HM.reshape cols $ OS.toVector t
            _ -> error "eval2: wrong tensor dimensions"

        Flipud2 d -> HM.flipud <$> eval2 d
        Fliprl2 d -> HM.fliprl <$> eval2 d
        Reshape2 cols d -> HM.reshape cols <$> eval1 d
        Conv2 m md -> HM.conv2 m <$> eval2 md

      evalX :: DeltaX r -> ST s (OT.Array r)
      evalX ZeroX = return 0
      evalX (InputX (DeltaId i)) =
        if i < dimX
        then return $! paramsXInit V.! i
        else error "derivativeFromDelta.eval': wrong index for an input"
      evalX (DeltaX n d) = do
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBindingX (DeltaId i) _) -> do
            rm <- readSTRef rMapX
            VM.read rm i
          Nothing -> do
            r <- evalX' d
            imNew <- readSTRef dMap
            rm <- readSTRef rMapX
            did@(DeltaId i) <- readSTRefU refX
            writeSTRefU refX $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBindingX did d) imNew
            len <- readSTRefU lenX
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i r
              writeSTRef rMapX rmG
              writeSTRefU lenX $ 2 * len
            else
              VM.write rm i r
            return r
          _ -> error "buildDerivative: corrupted dMap"
      evalX' :: DeltaX' r -> ST s (OT.Array r)
      evalX' = \case
        ScaleX k d -> (k *) <$> evalX d
        AddX d e -> liftM2 (+) (evalX d) (evalX e)

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
          return $! OT.fromVector [HM.rows l, cols] $ HM.flatten l
        FromSX d -> Data.Array.Convert.convert <$> evalS d

      evalS :: OS.Shape sh => DeltaS sh r -> ST s (OS.Array sh r)
      evalS ZeroS = return 0
      evalS (InputS (DeltaId i)) =
        if i < dimX
        then return $! Data.Array.Convert.convert $ paramsXInit V.! i
        else error "derivativeFromDelta.eval': wrong index for an input"
      evalS (DeltaS n d) = do
        im <- readSTRef dMap
        case IM.lookup n im of
          Just (DeltaBindingS (DeltaId i) _) -> do
            rm <- readSTRef rMapX
            Data.Array.Convert.convert <$> VM.read rm i
          Nothing -> do
            r <- evalS' d
            imNew <- readSTRef dMap
            rm <- readSTRef rMapX
            did@(DeltaId i) <- readSTRefU refX
            writeSTRefU refX $ succDeltaId did
            writeSTRef dMap $! IM.insert n (DeltaBindingS did d) imNew
            len <- readSTRefU lenX
            if i >= len then do
              rmG <- VM.unsafeGrow rm len
              VM.write rmG i (Data.Array.Convert.convert r)
              writeSTRef rMapX rmG
              writeSTRefU lenX $ 2 * len
            else
              VM.write rm i (Data.Array.Convert.convert r)
            return r
          _ -> error "buildDerivative: corrupted dMap"
      evalS' :: OS.Shape sh => DeltaS' sh r -> ST s (OS.Array sh r)
      evalS' = \case
        ScaleS k d -> (k *) <$> evalS d
        AddS d e -> liftM2 (+) (evalS d) (evalS e)

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
        From2S _ d -> OS.fromVector <$> HM.flatten <$> eval2 d
        FromXS d -> Data.Array.Convert.convert <$> evalX d
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

https://github.com/Mikolaj/horde-ad/blob/d069a45773ed849913b5ebd0345153072f304fd9/src/HordeAd/Core/DualNumber.hs#L125-L143

which is confirmed by tests to be equivalent in three different
implementations:

https://github.com/Mikolaj/horde-ad/blob/d069a45773ed849913b5ebd0345153072f304fd9/test/TestSingleGradient.hs#L116-L128

and proved to be prohibitively slow in the two implementations
that don't use the SumElements0 primitive in benchmarks (despite
an ingenious optimization of the common case of Index0 applied to a variable):

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
