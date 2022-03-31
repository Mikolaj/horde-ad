{-# LANGUAGE AllowAmbiguousTypes, CPP, DataKinds, GADTs, KindSignatures,
             StandaloneDeriving, TypeOperators #-}
#if !MIN_VERSION_base(4,16,0)
{-# LANGUAGE IncoherentInstances #-}
#endif
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The second component of dual numbers, @Delta@, with it's evaluation
-- function. Neel Krishnaswami calls them "sparse vector expressions",
-- and indeed they denote vectors, because even in the simplest
-- case of an objective function defined on scalars only,
-- the codomain of the evaluation function is a set of vectors,
-- because the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
--
-- The 'sparsity' is less obvious when the domain of the function consists
-- of multiple vectors and matrices and when the expressions themselves
-- contain vectors and matrices. However, a single tiny delta
-- expression (e.g., a sum of two variables) may denote a vector of matrices.
-- Even a delta expression containing a big matrix denotes something much
-- bigger: a whole vector of such matrices (and vectors and scalars).
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
-- e.g., the same as primal components, for fast computation
-- of forward derivatives (@evalBindingsForward@ below, using delta-expressions,
-- is slow once the expressions grow large enough to affect cache misses).
module HordeAd.Internal.Delta
  ( -- * Abstract syntax trees of the delta expressions
    Delta0 (..), Delta1 (..), Delta2 (..), DeltaX (..), DeltaS (..)
  , -- * Delta expression identifiers
    DeltaId, toDeltaId, covertDeltaId
  , -- * Evaluation of the delta expressions
    DeltaBinding
  , DeltaState (..)
  , evalBindings, evalBindingsForward, ppBindings
  , bindInState0, bindInState1, bindInState2, bindInStateX
  ) where

import Prelude

import           Control.Exception (assert)
import           Control.Monad (unless, zipWithM_)
import           Control.Monad.ST.Strict (ST, runST)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Internal
import qualified Data.Array.Internal.DynamicG
import qualified Data.Array.Internal.DynamicS
import qualified Data.Array.ShapedS as OS
import           Data.Kind (Type)
import           Data.List (foldl')
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector, (#>), (<.>))
import qualified Numeric.LinearAlgebra as HM
import           Text.Show.Pretty (ppShow)

import qualified HordeAd.Internal.MatrixOuter as MO
import           HordeAd.Internal.OrthotopeOrphanInstances ()

-- * Abstract syntax trees of the delta expressions

-- | This is the grammar of delta-expressions at tensor rank 0, that is,
-- at scalar level. The first few operations have analogues
-- at the level of vectors, matrices and arbitrary tensors.
--
-- For each choice of the underlying scalar type @r@,
-- we have several primitive differentiable types based on the scalar:
-- the scalar type @r@ itself, @Vector r@, @Matrix r@ and tensors.
-- Many operations span the ranks and so the datatypes, which makes
-- the datatypes mutually recursive.
data Delta0 r =
    Zero0
  | Scale0 r (Delta0 r)
  | Add0 (Delta0 r) (Delta0 r)
  | Var0 (DeltaId r)

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
  | Scale1 (Vector r) (Delta1 r)
  | Add1 (Delta1 r) (Delta1 r)
  | Var1 (DeltaId (Vector r))

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

  | Reverse1 (Delta1 r)
  | Flatten1 Int Int (Delta2 r)

deriving instance (Show r, Numeric r) => Show (Delta1 r)

-- | This is the grammar of delta-expressions at tensor rank 2, that is,
-- at matrix level.
data Delta2 r =
    Zero2
  | Scale2 (Matrix r) (Delta2 r)
  | Add2 (Delta2 r) (Delta2 r)
  | Var2 (DeltaId (Matrix r))

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

  | Flipud2 (Delta2 r)
  | Fliprl2 (Delta2 r)
  | Reshape2 Int (Delta1 r)
  | Conv2 (Matrix r) (Delta2 r)

deriving instance (Show r, Numeric r) => Show (Delta2 r)

-- | This is the grammar of delta-expressions at arbitrary tensor rank.
--
-- Warning: not tested nor benchmarked.
data DeltaX r =
    ZeroX
  | ScaleX (OT.Array r) (DeltaX r)
  | AddX (DeltaX r) (DeltaX r)
  | VarX (DeltaId (OT.Array r))

  | AppendX (DeltaX r) Int (DeltaX r)
      -- ^ Append two arrays along the outermost dimension.
      -- All dimensions, except the outermost, must be the same.
      -- The integer argument is the outermost size of the first array.
  | SliceX Int Int (DeltaX r) Int
      -- ^ Extract a slice of an array along the outermost dimension.
      -- The extracted slice must fall within the dimension.
      -- The last argument is the outermost size of the argument array.

  | From0X (Delta0 r)
  | From1X (Delta1 r)
  | From2X (Delta2 r) Int
  | forall sh. OS.Shape sh
    => FromSX (DeltaS sh r)

deriving instance (Show r, Numeric r) => Show (DeltaX r)

-- | This is the grammar of delta-expressions at arbitrary tensor rank,
-- the fully typed Shaped version.
--
-- Warning: not tested nor benchmarked.
data DeltaS :: [Nat] -> Type -> Type where
  ZeroS :: DeltaS sh r
  ScaleS :: OS.Array sh r -> DeltaS sh r -> DeltaS sh r
  AddS :: DeltaS sh r -> DeltaS sh r -> DeltaS sh r
  VarS :: DeltaId (OS.Array sh r) -> DeltaS sh r

  AppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
          => DeltaS (m ': sh) r -> DeltaS (n ': sh) r
          -> DeltaS ((m + n) ': sh) r
    -- ^ Append two arrays along the outermost dimension.
  SliceS :: (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
         => Proxy i -> Proxy n -> DeltaS (i + n + k ': rest) r
         -> DeltaS (n ': rest) r
    -- ^ Extract a slice of an array along the outermost dimension.

  From0S :: Delta0 r -> DeltaS '[] r
  From1S :: Delta1 r -> DeltaS '[n] r
  From2S :: KnownNat cols
         => Proxy cols -> Delta2 r -> DeltaS '[rows, cols] r
  FromXS :: DeltaX r -> DeltaS sh r

instance Show (DeltaS sh r) where
  show _ = "a DeltaS delta expression"


-- * Delta expression identifiers

newtype DeltaId a = DeltaId Int
  deriving Show

toDeltaId :: Int -> DeltaId a
toDeltaId = DeltaId

covertDeltaId :: DeltaId (OT.Array r) -> DeltaId (OS.Array sh r)
covertDeltaId (DeltaId i) = DeltaId i

-- The key property is that it preserves the phantom type.
succDeltaId :: DeltaId a -> DeltaId a
succDeltaId (DeltaId i) = DeltaId (succ i)


-- * Evaluation of the delta expressions

-- | Binding at one of the ranks, with a given underlying scalar.
--
-- The 'DeltaId' components could be re-computed on the fly in 'buildFinMaps',
-- but it costs more (they are boxed, so re-allocation is expensive)
-- than storing them here at the time of binding creation and accessing
-- in `buildFinMaps`.
data DeltaBinding r =
    DeltaBinding0 (DeltaId r) (Delta0 r)
  | DeltaBinding1 (DeltaId (Vector r)) (Delta1 r)
  | DeltaBinding2 (DeltaId (Matrix r)) (Delta2 r)
  | DeltaBindingX (DeltaId (OT.Array r)) (DeltaX r)

data DeltaState r = DeltaState
  { deltaCounter0 :: DeltaId r
  , deltaCounter1 :: DeltaId (Vector r)
  , deltaCounter2 :: DeltaId (Matrix r)
  , deltaCounterX :: DeltaId (OT.Array r)
  , deltaBindings :: [DeltaBinding r]
  }

-- | Helper definitions to shorten type signatures. Note that these
-- differ from their counterparts in all other modules, because the type
-- argument here is the underlying scalar (e.g., @Double),
-- while elsewhere it's the dual component of dual numbers from
-- rank 0 (scalar) level (e.g., @Delta0 Double@).
-- By chance, these definitions and definitions from other modules
-- coincide in case of "forward derivatives computed on the spot"
-- where @r@ is @Double@ and @Double@ is the dual component.
--
-- More generally, @r@ in this module tends to refert to the underlying
-- scalar type, while in all other modules it's the rank 0 dual component
-- type, in this module often denoted by @d@ both on type and value level.
type Domain0 r = Vector r

type Domain1 r = Data.Vector.Vector (Vector r)

type Domain2 r = Data.Vector.Vector (Matrix r)

type DomainX r = Data.Vector.Vector (OT.Array r)

type Domains r = (Domain0 r, Domain1 r, Domain2 r, DomainX r)

-- | Delta expressions naturally denote forward derivatives.
-- However, we use the delta expressions to compute gradients instead.
-- Let's first discuss the semantics in terms of forward derivatives,
-- because it's simpler (as evidenced by the simple implementation
-- in 'evalBindingsForward' below).
--
-- Let @r@ be the type of underlying scalars. Let @f@ be a mathematical
-- differentiable function that takes a collection of arguments
-- of type @C@ and produces a single result of type @r@.
-- Let a dual number counterpart of @f@, applied to a collection
-- of parameters @P@ of type @C@, be represented as a Haskell value @b@.
-- Let @d :: Delta0 r@ be the closed delta expression that is the second
-- component of @b@. Then @d@ denotes a linear function from @C@ to @r@
-- that is the derivative of @f@ at point @P@. The mathematical formula
-- for the derivative follows straightforwardly the syntactic form
-- of the delta expression @d@ (see 'evalBindingsForward').
--
-- Let's now describe the semantics of @d@ as the gradient of @f@
-- at point @P@, assuming that @dt@, the given perturbation of the result
-- of the function, is a scalar of type @r@ equal to @1@.
-- Here @d@ denotes a collection of four finite maps (vectors)
-- @v0@, @v1@, @v2@, @vX@, corresponding to @C@,
-- each map @vi@ taking indexes of type @DeltaId ai@ to values @ai@,
-- where @a0@ is @r@, @a1@ is @Vector r@, @a2@ is @Matrix r@
-- and @aX@ is the type of tensors of @r@.
--
-- The value of @vi@ at index @DeltaId k@ is the partial derivative
-- of function @f@ with respect to its parameter of type @ai@ at position
-- represented by @DeltaId k@ (in other words, with respect to a variable
-- quantity tagged with @DeltaId k@), given that @dt@ is @1@.
--
-- The semantics of @Delta_j r@ that is not closed but contains occurrences
-- of variables that do not correspond to parameters of @f@ is only
-- defined in the context of four vectors that contain values associated
-- to its free variables or, alternatively, of bindings from which the values
-- can be computed, or of a mixture of both. This semantics does not change
-- if a bound expression is substituted for a variable instead of being used
-- to compute a value. (Note however that a computed value can't be
-- substituted for the variable in an expression, because the "computing
-- backwards" trick, needed to get gradients from derivative expressions,
-- computes a value for each occurrence of a variable separately
-- and sums over all occurrences instead of substituting a single value
-- into each occurrence.)
--
-- Function @evalBindings@ computes the four vectors described above.
-- Requested lengths of the vectors are given in the first few arguments.
-- The delta state contains a list of mutually-referencing delta bindings
-- that are to be evaluated, in the given order, starting with the top-level
-- binding of a scalar type provided in the remaining argument.
evalBindings :: (Eq r, Numeric r, Num (Vector r))
             => Int -> Int -> Int -> Int -> DeltaState r -> Delta0 r
             -> Domains r
evalBindings dim0 dim1 dim2 dimX st deltaTopLevel =
  -- This is morally @V.create@ and so totally safe,
  -- but we can't just call @V.create@ thrice, because it would run
  -- the @ST@ action thrice, so we inline and extend @V.create@ here.
  runST $ do
    (finMap0, finMap1, finMap2, finMapX) <- buildFinMaps st deltaTopLevel
    v0 <- V.unsafeFreeze $ VM.take dim0 finMap0
    v1 <- V.unsafeFreeze $ VM.take dim1 finMap1
    v2 <- V.unsafeFreeze $ VM.take dim2 finMap2
    vX <- V.unsafeFreeze $ VM.take dimX finMapX
    -- Convert to normal matrices, but only the portion of vector
    -- that is not discarded.
    return (v0, v1, V.map MO.convertMatrixOuterOrNull v2, vX)

-- | Create vectors (representing finite maps) that hold delta-variable
-- values. They are initialized with dummy values so that it's cheap to check
-- if any update has already been performed to a cell (allocating big matrices
-- filled with zeros is too costly, especially if never used in an iteration,
-- and adding to such matrices and especially using them as scaling factors
-- is wasteful). The vectors are longer than those representing objective
-- function parameters (e.g., @deltaCounter0@ vs @dim0@), because variables
-- represent not only parameters, but also the bindings that prevent blowup
-- via delta-expression duplication.
initializeFinMaps :: forall s r. Numeric r
                  => DeltaState r
                  -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                          , Data.Vector.Mutable.MVector s (Vector r)
                          , Data.Vector.Mutable.MVector s (MO.MatrixOuter r)
                          , Data.Vector.Mutable.MVector s (OT.Array r) )
initializeFinMaps st = do
  let emptyArray =
        Data.Array.Internal.DynamicS.A
        $ Data.Array.Internal.DynamicG.A []
        $ Data.Array.Internal.T [] 0 V.empty
      DeltaId counter0 = deltaCounter0 st
      DeltaId counter1 = deltaCounter1 st
      DeltaId counter2 = deltaCounter2 st
      DeltaId counterX = deltaCounterX st
  finMap0 <- VM.replicate counter0 0  -- correct value
  finMap1 <- VM.replicate counter1 (V.empty :: Vector r)  -- dummy value
  finMap2 <- VM.replicate counter2 MO.emptyMatrixOuter  -- dummy value
  finMapX <- VM.replicate counterX emptyArray  -- dummy value
  return (finMap0, finMap1, finMap2, finMapX)

buildFinMaps :: forall s r. (Eq r, Numeric r, Num (Vector r))
             => DeltaState r -> Delta0 r
             -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                     , Data.Vector.Mutable.MVector s (Vector r)
                     , Data.Vector.Mutable.MVector s (MO.MatrixOuter r)
                     , Data.Vector.Mutable.MVector s (OT.Array r) )
buildFinMaps st deltaTopLevel = do
  (finMap0, finMap1, finMap2, finMapX) <- initializeFinMaps st
  let addToVector :: Vector r -> Vector r -> Vector r
      addToVector r = \v -> if V.null v then r else v + r
      addToMatrix :: MO.MatrixOuter r -> MO.MatrixOuter r -> MO.MatrixOuter r
      addToMatrix r = \v -> if MO.nullMatrixOuter v then r else MO.plus v r
      addToArray :: OT.Array r -> OT.Array r -> OT.Array r
      addToArray r = \v -> if null (OT.shapeL v) then r else OT.zipWithA (+) v r
      addToArrayS :: OS.Shape sh => OS.Array sh r -> OT.Array r -> OT.Array r
      addToArrayS r = \v -> let rs = Data.Array.Convert.convert r
                            in if null (OT.shapeL v)
                               then rs
                               else OT.zipWithA (+) v rs
      eval0 :: r -> Delta0 r -> ST s ()
      eval0 !r = \case
        Zero0 -> return ()
        Scale0 k d -> eval0 (k * r) d
        Add0 d e -> eval0 r d >> eval0 r e
        Var0 (DeltaId i) -> VM.modify finMap0 (+ r) i

        SumElements0 vd n -> eval1 (HM.konst r n) vd
        Index0 (Var1 (DeltaId i)) ix k -> do
          let f v = if V.null v
                    then HM.konst 0 k V.// [(ix, r)]
                    else v V.// [(ix, v V.! ix + r)]
          VM.modify finMap1 f i
            -- this would be an asymptotic optimization compared to
            -- the general case below, if not for the non-mutable update,
            -- which involves copying the whole vector, so it's just
            -- several times faster (same allocation, but not adding vectors)
        Index0 d ix k -> eval1 (HM.konst 0 k V.// [(ix, r)]) d

        Dot0 v vd -> eval1 (HM.scale r v) vd

        FromX0 d -> evalX (OT.scalar r) d
        FromS0 d -> evalS (OS.scalar r) d
      eval1 :: Vector r -> Delta1 r -> ST s ()
      eval1 !r = \case
        Zero1 -> return ()
        Scale1 k d -> eval1 (k * r) d
        Add1 d e -> eval1 r d >> eval1 r e
        Var1 (DeltaId i) -> VM.modify finMap1 (addToVector r) i

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
      eval2 :: MO.MatrixOuter r -> Delta2 r -> ST s ()
      eval2 !r = \case
        Zero2 -> return ()
        Scale2 k d -> eval2 (MO.multiplyWithOuter k r) d
        Add2 d e -> eval2 r d >> eval2 r e
        Var2 (DeltaId i) -> VM.modify finMap2 (addToMatrix r) i

        FromRows2 lvd -> zipWithM_ eval1 (MO.toRows r) (V.toList lvd)
        FromColumns2 lvd -> zipWithM_ eval1 (MO.toColumns r) (V.toList lvd)
        Konst2 d _sz -> mapM_ (V.mapM_ (`eval0` d)) $ MO.toRows r
        Transpose2 md -> eval2 (MO.transpose r) md  -- TODO: test!
        M_MD2 m md -> zipWithM_ (\rRow row -> eval1 rRow (MD_V1 md row))
                                (HM.toRows m) (MO.toRows r)
--      inlining eval1 to demonstrate the calls to eval2 with outer products:
--      M_MD2 m md ->
--        zipWithM_ (\rRow row ->
--                     eval2 (MO.MatrixOuter Nothing (Just rRow) (Just row)) md)
--                  (HM.toRows m) (MO.toRows r)
        MD_M2 md m -> zipWithM_ (\rCol col -> eval1 rCol (MD_V1 md col))
                                (MO.toColumns r) (HM.toColumns m)
--      inlining eval1 to demonstrate the calls to eval2 with outer products:
--      MD_M2 md m ->
--        zipWithM_ (\rCol col ->
--                     eval2 (MO.MatrixOuter Nothing (Just rCol) (Just col)) md)
--                  (MO.toColumns r) (HM.toColumns m)
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
      evalX !r = \case
        ZeroX -> return ()
        ScaleX k d -> evalX (OT.zipWithA (*) k r) d
        AddX d e -> evalX r d >> evalX r e
        VarX (DeltaId i) -> VM.modify finMapX (addToArray r) i

        AppendX d k e -> case OT.shapeL r of
          n : _ -> evalX (OT.slice [(0, k)] r) d
                   >> evalX (OT.slice [(k, n - k)] r) e
          [] -> error "evalX: appending a 0-dimensional tensor"
        SliceX i n d len -> case OT.shapeL r of
          n' : rest ->
            assert (n' == n) $
            evalX (OT.constant (i : rest) 0
                   `OT.append` r
                   `OT.append` OT.constant (len - i - n : rest) 0)
                  d
          [] -> error "evalX: slicing a 0-dimensional tensor"

        From0X d -> eval0 (OT.unScalar r) d
        From1X d -> eval1 (OT.toVector r) d
        From2X d cols ->
          eval2 (MO.MatrixOuter (Just $ HM.reshape cols $ OT.toVector r)
                                Nothing Nothing)
                d
        FromSX d -> evalS (Data.Array.Convert.convert r) d
      evalS :: OS.Shape sh
            => OS.Array sh r -> DeltaS sh r -> ST s ()
      evalS !r = \case
        ZeroS -> return ()
        ScaleS k d -> evalS (OS.zipWithA (*) k r) d
        AddS d e -> evalS r d >> evalS r e
        VarS (DeltaId i) -> VM.modify finMapX (addToArrayS r) i

        AppendS (d :: DeltaS (k ': rest) r) (e :: DeltaS (l ': rest) r) ->
          evalS (OS.slice @'[ '(0, k) ] r) d
          >> evalS (OS.slice @'[ '(k, l) ] r) e
        SliceS (_ :: Proxy i) _ (d :: DeltaS (i_plus_n_plus_k ': rest) r) ->
          evalS (OS.constant @(i ': rest) 0
                 `OS.append` r
                 `OS.append` OS.constant 0)
                d

        From0S d -> eval0 (OS.unScalar r) d
        From1S d -> eval1 (OS.toVector r) d
        From2S proxyCols d ->
          eval2 (MO.MatrixOuter
                   (Just $ HM.reshape (fromInteger $ natVal proxyCols)
                         $ OS.toVector r)
                   Nothing Nothing)
                d
        FromXS d -> evalX (Data.Array.Convert.convert r) d

  eval0 1 deltaTopLevel  -- dt is 1; can be overriden in the objective function

  let evalUnlessZero :: DeltaBinding r -> ST s ()
      evalUnlessZero (DeltaBinding0 (DeltaId i) d) = do
        r <- finMap0 `VM.read` i
        unless (r == 0) $  -- we init with exactly 0.0 so the comparison works
          eval0 r d
      evalUnlessZero (DeltaBinding1 (DeltaId i) d) = do
        r <- finMap1 `VM.read` i
        unless (V.null r) $
          eval1 r d
      evalUnlessZero (DeltaBinding2 (DeltaId i) d) = do
        r <- finMap2 `VM.read` i
        unless (MO.nullMatrixOuter r) $
          eval2 r d
      evalUnlessZero (DeltaBindingX (DeltaId i) d) = do
        r <- finMapX `VM.read` i
        unless (null (OT.shapeL r)) $
          evalX r d
  mapM_ evalUnlessZero (deltaBindings st)
  return (finMap0, finMap1, finMap2, finMapX)

-- | Forward derivative computation via forward-evaluation of delta-expressions
-- (which is surprisingly competitive to the direct forward method,
-- until the RAM taken by deltas gets large enough to affect cache hits).
-- This is the directional derivative, calculated for the point,
-- at which the delta expression was computed (which is the point
-- represented by the parameters of the objective function and used
-- to compute it's dual number result) and along the direction vector(s)
-- given in the last parameter of @evalBindingsForward@.
--
-- Warning: the tensor part is not tested at all.
evalBindingsForward :: forall r. (Numeric r, Num (Vector r))
                    => DeltaState r -> Delta0 r -> Domains r -> r
evalBindingsForward st deltaTopLevel
                    (params0Init, params1Init, params2Init, paramsXInit) =
  let eval0 :: Domains r -> Delta0 r -> r
      eval0 parameters@(params0, _, _, _) = \case
        Zero0 -> 0
        Scale0 k d -> k * eval0 parameters d
        Add0 d e -> eval0 parameters d + eval0 parameters e
        Var0 (DeltaId i) -> params0 V.! i

        SumElements0 vd _n -> HM.sumElements $ eval1 parameters vd
        Index0 d ix _k -> eval1 parameters d V.! ix

        Dot0 vr vd -> vr <.> eval1 parameters vd

        FromX0 d -> OT.unScalar $ evalX parameters d
        FromS0 d -> OS.unScalar $ evalS parameters d
      eval1 :: Domains r -> Delta1 r -> Vector r
      eval1 parameters@(_, params1, _, _) = \case
        Zero1 -> 0
        Scale1 k d -> k * eval1 parameters d
        Add1 d e -> eval1 parameters d + eval1 parameters e
        Var1 (DeltaId i) -> params1 V.! i

        Seq1 lsd -> V.convert $ V.map (eval0 parameters) lsd
        Konst1 d n -> HM.konst (eval0 parameters d) n
        Append1 d _k e -> eval1 parameters d V.++ eval1 parameters e
        Slice1 i n d _len -> V.slice i n $ eval1 parameters d
        SumRows1 dm _cols ->
          V.fromList $ map HM.sumElements $ HM.toRows $ eval2 parameters dm
        SumColumns1 dm _rows ->
          V.fromList $ map HM.sumElements $ HM.toColumns $ eval2 parameters dm

        M_VD1 m dRow -> m #> eval1 parameters dRow
        MD_V1 md row -> eval2 parameters md #> row

        FromX1 d -> OT.toVector $ evalX parameters d
        FromS1 d -> OS.toVector $ evalS parameters d

        Reverse1 d -> V.reverse $ eval1 parameters d
        Flatten1 _rows _cols d -> HM.flatten $ eval2 parameters d
      eval2 :: Domains r -> Delta2 r -> Matrix r
      eval2 parameters@( _, _, params2, _) = \case
        Zero2 -> 0
        Scale2 k d -> k * eval2 parameters d
        Add2 d e -> eval2 parameters d + eval2 parameters e
        Var2 (DeltaId i) -> params2 V.! i

        FromRows2 lvd ->
          HM.fromRows $ map (eval1 parameters) $ V.toList lvd
        FromColumns2 lvd ->
          HM.fromColumns $ map (eval1 parameters) $ V.toList lvd
        Konst2 d sz -> HM.konst (eval0 parameters d) sz
        Transpose2 md -> HM.tr' $ eval2 parameters md
        M_MD2 m md -> m HM.<> eval2 parameters md
        MD_M2 md m -> eval2 parameters md HM.<> m
        RowAppend2 d _k e -> eval2 parameters d HM.=== eval2 parameters e
        ColumnAppend2 d _k e -> eval2 parameters d HM.||| eval2 parameters e
        RowSlice2 i n d _rows ->
          HM.takeRows n $ HM.dropRows i $ eval2 parameters d
        ColumnSlice2 i n d _cols ->
          HM.takeColumns n $ HM.dropColumns i $ eval2 parameters d

        AsRow2 dRow -> HM.asRow $ eval1 parameters dRow  -- TODO: risky
        AsColumn2 dCol -> HM.asColumn $ eval1 parameters dCol  -- TODO: risky

        FromX2 d ->
          let t = evalX parameters d
          in case OT.shapeL t of
            [_rows, cols] -> HM.reshape cols $ OT.toVector t
            _ -> error "eval2: wrong tensor dimensions"
        FromS2 d ->
          let t = evalS parameters d
          in case OS.shapeL t of
            [_rows, cols] -> HM.reshape cols $ OS.toVector t
            _ -> error "eval2: wrong tensor dimensions"

        Flipud2 d -> HM.flipud $ eval2 parameters d
        Fliprl2 d -> HM.fliprl $ eval2 parameters d
        Reshape2 cols d -> HM.reshape cols $ eval1 parameters d
        Conv2 m md -> HM.conv2 m $ eval2 parameters md
      evalX :: Domains r -> DeltaX r -> OT.Array r
      evalX parameters@( _, _, _, paramsX) = \case
        ZeroX -> 0
        ScaleX k d -> k * evalX parameters d
        AddX d e -> evalX parameters d + evalX parameters e
        VarX (DeltaId i) -> paramsX V.! i

        AppendX d _k e -> evalX parameters d `OT.append` evalX parameters e
        SliceX i n d _len -> OT.slice [(i, n)] $ evalX parameters d

        From0X d -> OT.scalar $ eval0 parameters d
        From1X d -> let v = eval1 parameters d
                    in OT.fromVector [V.length v] v
        From2X d cols -> let l = eval2 parameters d
                         in OT.fromVector [HM.rows l, cols] $ HM.flatten l
        FromSX d -> Data.Array.Convert.convert $ evalS parameters d
      evalS :: OS.Shape sh => Domains r -> DeltaS sh r -> OS.Array sh r
      evalS parameters@( _, _, _, paramsX) = \case
        ZeroS -> 0
        ScaleS k d -> k * evalS parameters d
        AddS d e -> evalS parameters d + evalS parameters e
        VarS (DeltaId i) -> Data.Array.Convert.convert $ paramsX V.! i

        AppendS d e -> evalS parameters d `OS.append` evalS parameters e
        SliceS (_ :: Proxy i) (_ :: Proxy n) d ->
          OS.slice @'[ '(i, n) ] $ evalS parameters d
        From0S d -> OS.scalar $ eval0 parameters d
        From1S d -> OS.fromVector $ eval1 parameters d
        From2S _ d -> OS.fromVector $ HM.flatten $ eval2 parameters d
        FromXS d -> Data.Array.Convert.convert $ evalX parameters d
      evalUnlessZero :: Domains r -> DeltaBinding r -> Domains r
      evalUnlessZero parameters@(!params0, !params1, !params2, !paramsX) = \case
        DeltaBinding0 (DeltaId i) d ->
          let v = eval0 parameters d
          in (params0 V.// [(i, v)], params1, params2, paramsX)
        DeltaBinding1 (DeltaId i) d ->
          let v = eval1 parameters d
          in (params0, params1 V.// [(i, v)], params2, paramsX)
        DeltaBinding2 (DeltaId i) d ->
          let v = eval2 parameters d
          in (params0, params1, params2 V.// [(i, v)], paramsX)
        DeltaBindingX (DeltaId i) d ->
          let v = evalX parameters d
          in (params0, params1, params2, paramsX V.// [(i, v)])
      parameters1 = runST $ do
        (finMap0, finMap1, outerFinMap2, finMapX) <- initializeFinMaps st
        -- We use normal hmatrix matrices rather than the sparse replacement.
        finMap2 <- VM.replicate (VM.length outerFinMap2) (HM.fromRows [])
        -- TODO: the following coredumps without the @VM.take@; it's a shame
        -- there's no copying of a smaller vector into a larger one in the API.
        -- Perhaps use https://hackage.haskell.org/package/base-4.16.0.0/docs/Foreign-Marshal-Array.html#v:copyArray?
        V.unsafeCopy (VM.take (V.length params0Init) finMap0) params0Init
        V.unsafeCopy (VM.take (V.length params1Init) finMap1) params1Init
        V.unsafeCopy (VM.take (V.length params2Init) finMap2) params2Init
        V.unsafeCopy (VM.take (V.length paramsXInit) finMapX) paramsXInit
        v0 <- V.unsafeFreeze finMap0
        v1 <- V.unsafeFreeze finMap1
        v2 <- V.unsafeFreeze finMap2
        vX <- V.unsafeFreeze finMapX
        return (v0, v1, v2, vX)
      parametersB = foldl' evalUnlessZero parameters1
                           (reverse $ deltaBindings st)
  in eval0 parametersB deltaTopLevel

-- | This is yet another semantics of delta-expressions and their
-- bindings --- by pretty-printing as texts.
ppBindings :: (Show r, Numeric r) => Bool -> DeltaState r -> Delta0 r -> String
ppBindings reversed st deltaTopLevel =
  let pp = if reversed
           then foldl' (\ !l b -> l ++ ppBinding "where" b)
                       ["COMPUTE " ++ ppShow deltaTopLevel ++ "\n"]
           else foldl' (\ !l b -> ppBinding "let" b ++ l)
                       ["in " ++ ppShow deltaTopLevel ++ "\n"]
  in concat $ pp $ deltaBindings st

ppBinding :: (Show r, Numeric r) => String -> DeltaBinding r -> [String]
ppBinding prefix = \case
  DeltaBinding0 (DeltaId i) d ->
    [prefix ++ "0 DeltaId_", show i, " = ", ppShow d, "\n"]
  DeltaBinding1 (DeltaId i) d ->
    [prefix ++ "1 DeltaId_", show i, " = ", ppShow d, "\n"]
  DeltaBinding2 (DeltaId i) d ->
    [prefix ++ "2 DeltaId_", show i, " = ", ppShow d, "\n"]
  DeltaBindingX (DeltaId i) d ->
    [prefix ++ "X DeltaId_", show i, " = ", ppShow d, "\n"]

bindInState0 :: Delta0 r -> DeltaState r -> (DeltaState r, DeltaId r)
{-# INLINE bindInState0 #-}
bindInState0 u' st =
  let dId = deltaCounter0 st
      !binding = DeltaBinding0 dId u'
  in ( st { deltaCounter0 = succDeltaId dId
          , deltaBindings = binding : deltaBindings st
          }
     , dId )

bindInState1 :: Delta1 r -> DeltaState r -> (DeltaState r, DeltaId (Vector r))
{-# INLINE bindInState1 #-}
bindInState1 u' st =
  let dId = deltaCounter1 st
      !binding = DeltaBinding1 dId u'
  in ( st { deltaCounter1 = succDeltaId dId
          , deltaBindings = binding : deltaBindings st
          }
     , dId )

bindInState2 :: Delta2 r -> DeltaState r -> (DeltaState r, DeltaId (Matrix r))
{-# INLINE bindInState2 #-}
bindInState2 u' st =
  let dId = deltaCounter2 st
      !binding = DeltaBinding2 dId u'
  in ( st { deltaCounter2 = succDeltaId dId
          , deltaBindings = binding : deltaBindings st
          }
     , dId )

bindInStateX :: DeltaX r -> DeltaState r -> (DeltaState r, DeltaId (OT.Array r))
{-# INLINE bindInStateX #-}
bindInStateX u' st =
  let dId = deltaCounterX st
      !binding = DeltaBindingX dId u'
  in ( st { deltaCounterX = succDeltaId dId
          , deltaBindings = binding : deltaBindings st
          }
     , dId )

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
