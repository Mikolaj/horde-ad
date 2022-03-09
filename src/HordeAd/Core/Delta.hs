{-# LANGUAGE AllowAmbiguousTypes, DataKinds, GADTs, KindSignatures,
             StandaloneDeriving, TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | The second component of dual numbers, @Delta@, with it's evaluation
-- function. Neel Krishnaswami calls that "sparse vector expressions",
-- and indeed even in the simplest case of a function defined on scalars only,
-- the non-empty portion of the codomain of the evaluation function is a vector,
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
-- The crucial extra constructor for variables is used both to represent
-- sharing in order to avoid exponential blowup and to replace the one-hot
-- access to parameters with something cheaper and more uniform.
-- A lot of the remaining additional structure is for introducing
-- and reducing dimensions.
module HordeAd.Core.Delta
  ( -- * Abstract syntax trees of the delta expressions
    Delta0 (..), Delta1 (..), Delta2 (..), DeltaX (..), DeltaS (..)
  , -- * Delta expression identifiers
    DeltaId, toDeltaId, covertDeltaId
  , -- * Evaluation of the delta expressions
    DeltaBinding
  , DeltaState (..)
  , Domain, DomainV, DomainL, DomainX, Domains
  , evalBindings, evalBindingsForward, ppBinding
  , bindInState0, bindInState1, bindInState2, bindInStateX
  ) where

import Prelude

import           Control.Exception (assert)
import           Control.Monad (unless, zipWithM_)
import           Control.Monad.ST.Strict (ST, runST)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
import           Data.Array.Internal (valueOf)
import qualified Data.Array.Internal
import qualified Data.Array.Internal.DynamicG
import qualified Data.Array.Internal.DynamicS
import qualified Data.Array.ShapedS as OS
import           Data.Kind (Type)
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           GHC.TypeLits (KnownNat, Nat, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector, (#>), (<.>))
import qualified Numeric.LinearAlgebra as HM
import           Text.Show.Pretty (ppShow)

import qualified HordeAd.Internal.MatrixOuter as MO

-- * Abstract syntax trees of the delta expressions

-- | This is the grammar of delta-expressions at tensor rank 0, that is,
-- at scalar level. Some of these operations have different but inter-related
-- semantics at the level of vectors and matrices (WIP: and arbitrary tensors).
--
-- In other words, for each choice of the underlying scalar type @r@,
-- we have three primitive differentiable types based on the scalar:
-- the scalar type @r@ itself, @Vector r@ and @Matrix r@.
data Delta0 r =
    Zero0
  | Scale0 r (Delta0 r)
  | Add0 (Delta0 r) (Delta0 r)
  | Var0 (DeltaId r)

  | SumElements0 (Delta1 r) Int
  | Index0 (Delta1 r) Int Int

  | Dot0 (Vector r) (Delta1 r)  -- Dot0 v sd == SumElements0 (Scale1 v sd) n

  | FromX0 (DeltaX r)
  | FromS0 (DeltaS '[] r)

deriving instance (Show r, Numeric r) => Show (Delta0 r)

-- | This is the grammar of delta-expressions at tensor rank 1, that is,
-- at vector level.
data Delta1 r =
    Zero1
  | Scale1 (Vector r) (Delta1 r)
  | Add1 (Delta1 r) (Delta1 r)
  | Var1 (DeltaId (Vector r))

  | Seq1 (Data.Vector.Vector (Delta0 r))
  | Konst1 (Delta0 r) Int  -- second argument needed only for forward derivative
  | Append1 (Delta1 r) Int (Delta1 r)
  | Slice1 Int Int (Delta1 r) Int
  | SumRows1 (Delta2 r) Int
  | SumColumns1 (Delta2 r) Int

  | M_VD1 (Matrix r) (Delta1 r)  -- M_VD1 m vd == SumRows1 (M_MD2 m (AsRow2 vd))
  | MD_V1 (Delta2 r) (Vector r)  -- MD_V1 md v == SumRows1 (MD_M2 md (asRow v))

  | FromX1 (DeltaX r)
  | forall len. KnownNat len
    => FromS1 (DeltaS '[len] r)

deriving instance (Show r, Numeric r) => Show (Delta1 r)

-- | This is the grammar of delta-expressions at tensor rank 2, that is,
-- at matrix level.
data Delta2 r =
    Zero2
  | Scale2 (Matrix r) (Delta2 r)
  | Add2 (Delta2 r) (Delta2 r)
  | Var2 (DeltaId (Matrix r))

  | FromRows2 (Data.Vector.Vector (Delta1 r))
  | FromColumns2 (Data.Vector.Vector (Delta1 r))
  | Transpose2 (Delta2 r)
  | M_MD2 (Matrix r) (Delta2 r)
  | MD_M2 (Delta2 r) (Matrix r)
  | RowAppend2 (Delta2 r) Int (Delta2 r)
  | ColumnAppend2 (Delta2 r) Int (Delta2 r)
  | RowSlice2 Int Int (Delta2 r) Int
  | ColumnSlice2 Int Int (Delta2 r) Int

  | AsRow2 (Delta1 r)  -- AsRow2 vd == FromRows2 (V.replicate n vd)
  | AsColumn2 (Delta1 r)  -- AsColumn2 vd == FromColumns2 (V.replicate n vd)

  | FromX2 (DeltaX r)
  | forall rows cols. (KnownNat rows, KnownNat cols)
    => FromS2 (DeltaS '[rows, cols] r)

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
-- Warning: not tested nor benchmarked. To see any typing problems and decide
-- whether `DeltaX` can be replaced or kept in addition or neither,
-- we need to implement something that really needs tensors or at least
-- some heavy matrix stuff using exclusively tensors.
data DeltaS :: [Nat] -> Type -> Type where
  ZeroS :: DeltaS sh r
  ScaleS :: OS.Array sh r -> DeltaS sh r -> DeltaS sh r
  AddS :: DeltaS sh r -> DeltaS sh r -> DeltaS sh r
  VarS :: DeltaId (OS.Array sh r) -> DeltaS sh r

  AppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
          => DeltaS (m ': sh) r -> DeltaS (n ': sh) r
          -> DeltaS ((m + n) ': sh) r
    -- ^ Append two arrays along the outermost dimension.
  SliceS :: forall i n k rest r.
            (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
         => DeltaS (i + n + k ': rest) r -> DeltaS (n ': rest) r
    -- ^ Extract a slice of an array along the outermost dimension.

  From0S :: Delta0 r -> DeltaS '[] r
  From1S :: Delta1 r -> DeltaS '[n] r
  From2S :: forall rows cols r. KnownNat cols
         => Delta2 r -> DeltaS '[rows, cols] r
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

-- The key is that it preserves the phantom type.
succDeltaId :: DeltaId a -> DeltaId a
succDeltaId (DeltaId i) = DeltaId (succ i)

-- * Evaluation of the delta expressions

-- The @DeltaId@ components could be computed on the fly when evaluating,
-- but it costs more (they are boxed) than storing them here at the time
-- of binding creation.
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

type Domain r = Vector r

type DomainV r = Data.Vector.Vector (Vector r)

type DomainL r = Data.Vector.Vector (Matrix r)

type DomainX r = Data.Vector.Vector (OT.Array r)

type Domains r = (Domain r, DomainV r, DomainL r, DomainX r)

-- | Delta expressions are originally meant to denote (forward) derivatives.
-- However, we use the delta expressions to compute gradients instead.
-- Let's first discuss the semantics in terms of derivatives,
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
-- of the delta expression @d@.
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
    (finiteMap0, finiteMap1, finiteMap2, finiteMapX)
      <- buildVectors st deltaTopLevel
    v0 <- V.unsafeFreeze $ VM.take dim0 finiteMap0
    v1 <- V.unsafeFreeze $ VM.take dim1 finiteMap1
    v2 <- V.unsafeFreeze $ VM.take dim2 finiteMap2
    vX <- V.unsafeFreeze $ VM.take dimX finiteMapX
    -- Convert to normal matrices, but only the portion of vector
    -- that is not discarded.
    return (v0, v1, V.map MO.convertMatrixOuterOrNull v2, vX)

buildVectors :: forall s r. (Eq r, Numeric r, Num (Vector r))
             => DeltaState r -> Delta0 r
             -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                     , Data.Vector.Mutable.MVector s (Vector r)
                     , Data.Vector.Mutable.MVector s (MO.MatrixOuter r)
                     , Data.Vector.Mutable.MVector s (OT.Array r) )
buildVectors st deltaTopLevel = do
  let emptyArray =
        Data.Array.Internal.DynamicS.A
        $ Data.Array.Internal.DynamicG.A []
        $ Data.Array.Internal.T [] 0 V.empty
      DeltaId counter0 = deltaCounter0 st
      DeltaId counter1 = deltaCounter1 st
      DeltaId counter2 = deltaCounter2 st
      DeltaId counterX = deltaCounterX st
  store0 <- VM.replicate counter0 0  -- correct value
  store1 <- VM.replicate counter1 (V.empty :: Vector r)  -- dummy value
  store2 <- VM.replicate counter2 MO.emptyMatrixOuter  -- dummy value
  storeX <- VM.replicate counterX emptyArray  -- dummy value
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
        Var0 (DeltaId i) -> VM.modify store0 (+ r) i

        Dot0 vr vd -> eval1 (HM.scale r vr) vd
        SumElements0 vd n -> eval1 (HM.konst r n) vd
        Index0 d ix k -> eval1 (HM.konst 0 k V.// [(ix, r)]) d

        FromX0 d -> evalX (OT.scalar r) d
        FromS0 d -> evalS (OS.scalar r) d
      eval1 :: Vector r -> Delta1 r -> ST s ()
      eval1 !r = \case
        Zero1 -> return ()
        Scale1 k d -> eval1 (k * r) d
        Add1 d e -> eval1 r d >> eval1 r e
        Var1 (DeltaId i) -> VM.modify store1 (addToVector r) i

        Seq1 lsd -> V.imapM_ (\i d -> eval0 (r V.! i) d) lsd
        Konst1 d _n -> V.mapM_ (`eval0` d) r
        Append1 d k e -> eval1 (V.take k r) d >> eval1 (V.drop k r) e
        Slice1 i n d len ->
          eval1 (HM.konst 0 i V.++ r V.++ HM.konst 0 (len - i - n)) d
        M_VD1 m dRow ->
          mapM_ (`eval1` dRow)
                (MO.toRows (MO.MatrixOuter (Just m) (Just r) Nothing))
        MD_V1 md row -> eval2 (MO.MatrixOuter Nothing (Just r) (Just row)) md
        SumRows1 dm cols -> eval2 (MO.asColumn r cols) dm
        SumColumns1 dm rows -> eval2 (MO.asRow r rows) dm

        FromX1 d -> evalX (OT.fromVector [V.length r] r) d
        FromS1 d -> evalS (OS.fromVector r) d
      eval2 :: MO.MatrixOuter r -> Delta2 r -> ST s ()
      eval2 !r = \case
        Zero2 -> return ()
        Scale2 k d -> eval2 (MO.multiplyWithOuter k r) d
        Add2 d e -> eval2 r d >> eval2 r e
        Var2 (DeltaId i) -> VM.modify store2 (addToMatrix r) i

        FromRows2 lvd -> zipWithM_ eval1 (MO.toRows r) (V.toList lvd)
        FromColumns2 lvd -> zipWithM_ eval1 (MO.toColumns r) (V.toList lvd)
        Transpose2 md -> eval2 (MO.transpose r) md  -- TODO: test!
        M_MD2 m md -> zipWithM_ (\rRow row -> eval1 rRow (MD_V1 md row))
                                (HM.toRows m) (MO.toRows r)
--      M_MD2 m md ->
--        zipWithM_ (\rRow row ->
--                     eval2 (MO.MatrixOuter Nothing (Just rRow) (Just row)) md)
--                  (HM.toRows m) (MO.toRows r)
        MD_M2 md m -> zipWithM_ (\rCol col -> eval1 rCol (MD_V1 md col))
                                (MO.toColumns r) (HM.toColumns m)
--      MD_M2 md m ->
--        zipWithM_ (\rCol col ->
--                     eval2 (MO.MatrixOuter Nothing (Just rCol) (Just col)) md)
--                  (MO.toColumns r) (HM.toColumns m)
        AsRow2 dRow -> mapM_ (`eval1` dRow) (MO.toRows r)
        AsColumn2 dCol -> mapM_ (`eval1` dCol) (MO.toColumns r)
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

        FromX2 d -> evalX (OT.fromVector [MO.rows r, MO.cols r]
                                         (V.concat $ MO.toRows r)) d
        FromS2 d -> evalS (OS.fromVector $ V.concat $ MO.toRows r) d
      evalX :: OT.Array r -> DeltaX r -> ST s ()
      evalX !r = \case
        ZeroX -> return ()
        ScaleX k d -> evalX (OT.zipWithA (*) k r) d
        AddX d e -> evalX r d >> evalX r e
        VarX (DeltaId i) -> VM.modify storeX (addToArray r) i

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
        VarS (DeltaId i) -> VM.modify storeX (addToArrayS r) i

        AppendS d e -> appendS r d e
        SliceS @i d -> sliceS @i r d
          -- is it possible to do that without type patterns and so GHC >= 9.2?

        From0S d -> eval0 (OS.unScalar r) d
        From1S d -> eval1 (OS.toVector r) d
        From2S @_ @cols d ->
          eval2 (MO.MatrixOuter
                   (Just $ HM.reshape (valueOf @cols) $ OS.toVector r)
                   Nothing Nothing)
                d
        FromXS d -> evalX (Data.Array.Convert.convert r) d
      -- These auxiliary functions are only required to set up the type-level
      -- machinery. This hinders readability, sadly.
      appendS :: forall k l rest. (KnownNat k, KnownNat l, OS.Shape rest)
              => OS.Array (k + l ': rest) r
              -> DeltaS (k ': rest) r -> DeltaS (l ': rest) r
              -> ST s ()
      appendS r d e = evalS (OS.slice @'[ '(0, k) ] r) d
                      >> evalS (OS.slice @'[ '(k, l) ] r) e
      sliceS :: forall i n k rest.
                (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
             => OS.Array (n ': rest) r -> DeltaS (i + n + k ': rest) r
             -> ST s ()
      sliceS r = evalS (OS.constant @(i ': rest) 0
                        `OS.append` r
                        `OS.append` OS.constant @(k ': rest) 0)
  eval0 1 deltaTopLevel  -- dt is 1 or hardwired in f
  let evalUnlessZero :: DeltaBinding r -> ST s ()
      evalUnlessZero (DeltaBinding0 (DeltaId i) d) = do
        r <- store0 `VM.read` i
        unless (r == 0) $  -- we init with exactly 0 so the comparison is OK
          eval0 r d
      evalUnlessZero (DeltaBinding1 (DeltaId i) d) = do
        r <- store1 `VM.read` i
        unless (V.null r) $
          eval1 r d
      evalUnlessZero (DeltaBinding2 (DeltaId i) d) = do
        r <- store2 `VM.read` i
        unless (MO.nullMatrixOuter r) $
          eval2 r d
      evalUnlessZero (DeltaBindingX (DeltaId i) d) = do
        r <- storeX `VM.read` i
        unless (null (OT.shapeL r)) $
          evalX r d
  mapM_ evalUnlessZero (deltaBindings st)
  return (store0, store1, store2, storeX)

-- | Forward derivative computation via forward-evaluation of delta-expressions
-- (which most probably makes it inefficient compared to the direct
-- forward method). [TODO: I'm not sure about the following point:]
-- This is the directional derivative, calculated for the point,
-- at which the delta expression was computed (which is the point
-- represented by the parameters of the objective function and used
-- to compute it's dual number result) and along the direction vector(s)
-- given in the last parameter of @evalBindingsForward@.
--
-- Warning: the tensor part is not fully implemented and not tested at all.
evalBindingsForward :: forall r. (Numeric r, Num (Vector r))
                    => DeltaState r -> Delta0 r -> Domains r -> r
evalBindingsForward st deltaTopLevel (params0, paramsV0, paramsL0, paramsX0) =
  let eval0 :: Domains r -> Delta0 r -> r
      eval0 parameters@(params, _, _, _) = \case
        Zero0 -> 0
        Scale0 k d -> k * eval0 parameters d
        Add0 d e -> eval0 parameters d + eval0 parameters e
        Var0 (DeltaId i) -> params V.! i

        Dot0 vr vd -> vr <.> eval1 parameters vd
        SumElements0 vd _n -> HM.sumElements $ eval1 parameters vd
        Index0 d ix _k -> eval1 parameters d V.! ix

        FromX0 d -> OT.unScalar $ evalX parameters d
        FromS0 d -> OS.unScalar $ evalS parameters d
      eval1 :: Domains r -> Delta1 r -> Vector r
      eval1 parameters@(_, paramsV, _, _) = \case
        Zero1 -> 0
        Scale1 k d -> k * eval1 parameters d
        Add1 d e -> eval1 parameters d + eval1 parameters e
        Var1 (DeltaId i) -> paramsV V.! i

        Seq1 lsd -> V.convert $ V.map (eval0 parameters) lsd
        Konst1 d n -> HM.konst (eval0 parameters d) n
        Append1 d _k e -> eval1 parameters d V.++ eval1 parameters e
        Slice1 i n d _len -> V.slice i n $ eval1 parameters d
        M_VD1 m dRow -> m #> eval1 parameters dRow
        MD_V1 md row -> eval2 parameters md #> row
        SumRows1 dm _cols ->
          V.fromList $ map HM.sumElements $ HM.toRows $ eval2 parameters dm
        SumColumns1 dm _rows ->
          V.fromList $ map HM.sumElements $ HM.toColumns $ eval2 parameters dm

        FromX1 d -> OT.toVector $ evalX parameters d
        FromS1 d -> OS.toVector $ evalS parameters d
      eval2 :: Domains r -> Delta2 r -> Matrix r
      eval2 parameters@( _, _,paramsL, _) = \case
        Zero2 -> 0
        Scale2 k d -> k * eval2 parameters d
        Add2 d e -> eval2 parameters d + eval2 parameters e
        Var2 (DeltaId i) -> paramsL V.! i

        FromRows2 lvd ->
          HM.fromRows $ map (eval1 parameters) $ V.toList lvd
        FromColumns2 lvd ->
          HM.fromColumns $ map (eval1 parameters) $ V.toList lvd
        Transpose2 md -> HM.tr' $ eval2 parameters md
        M_MD2 m md -> m HM.<> eval2 parameters md
        MD_M2 md m -> eval2 parameters md HM.<> m
        AsRow2 dRow -> HM.asRow $ eval1 parameters dRow  -- TODO: risky
        AsColumn2 dCol -> HM.asColumn $ eval1 parameters dCol  -- TODO: risky
        RowAppend2 d _k e -> eval2 parameters d HM.=== eval2 parameters e
        ColumnAppend2 d _k e -> eval2 parameters d HM.||| eval2 parameters e
        RowSlice2 i n d _rows ->
          HM.takeRows n $ HM.dropRows i $ eval2 parameters d
        ColumnSlice2 i n d _cols ->
          HM.takeColumns n $ HM.dropColumns i $ eval2 parameters d

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
        SliceS @i @n d -> OS.slice @'[ '(i, n) ] $ evalS parameters d

        From0S d -> OS.scalar $ eval0 parameters d
        From1S d -> OS.fromVector $ eval1 parameters d
        From2S d -> OS.fromVector $ HM.flatten $ eval2 parameters d
        FromXS d -> Data.Array.Convert.convert $ evalX parameters d
      evalUnlessZero :: Domains r -> DeltaBinding r -> Domains r
      evalUnlessZero parameters@(!params, !paramsV, !paramsL, !paramsX) = \case
        DeltaBinding0 (DeltaId i) d ->
          let v = eval0 parameters d
          in (params V.// [(i, v)], paramsV, paramsL, paramsX)
        DeltaBinding1 (DeltaId i) d ->
          let v = eval1 parameters d
          in (params, paramsV V.// [(i, v)], paramsL, paramsX)
        DeltaBinding2 (DeltaId i) d ->
          let v = eval2 parameters d
          in (params, paramsV, paramsL V.// [(i, v)], paramsX)
        DeltaBindingX (DeltaId i) d ->
          let v = evalX parameters d
          in (params, paramsV, paramsL, paramsX V.// [(i, v)])
      emptyArray =
        Data.Array.Internal.DynamicS.A
        $ Data.Array.Internal.DynamicG.A []
        $ Data.Array.Internal.T [] 0 V.empty
      DeltaId counter0 = deltaCounter0 st
      DeltaId counter1 = deltaCounter1 st
      DeltaId counter2 = deltaCounter2 st
      DeltaId counterX = deltaCounterX st
      parameters1 = runST $ do
        store0 <- VM.replicate counter0 0  -- correct value
        store1 <- VM.replicate counter1 (V.empty :: Vector r)  -- dummy value
        store2 <- VM.replicate counter2 (HM.fromRows [])  -- dummy value
        storeX <- VM.replicate counterX emptyArray  -- dummy value
        let dim0 = V.length params0
            dim1 = V.length paramsV0
            dim2 = V.length paramsL0
            dimX = V.length paramsX0
        -- TODO: this coredumps without the @VM.take@; it's a shame
        -- there's no copying of a smaller vector into a larger one in the API.
        -- Perhaps use https://hackage.haskell.org/package/base-4.16.0.0/docs/Foreign-Marshal-Array.html#v:copyArray?
        V.basicUnsafeCopy (VM.take dim0 store0) params0
        V.basicUnsafeCopy (VM.take dim1 store1) paramsV0
        V.basicUnsafeCopy (VM.take dim2 store2) paramsL0
        V.basicUnsafeCopy (VM.take dimX storeX) paramsX0
        v0 <- V.unsafeFreeze store0
        v1 <- V.unsafeFreeze store1
        v2 <- V.unsafeFreeze store2
        vX <- V.unsafeFreeze storeX
        return (v0, v1, v2, vX)
      parametersB = foldl' evalUnlessZero parameters1
                           (reverse $ deltaBindings st)
  in eval0 parametersB deltaTopLevel

instance Numeric r => Num (OT.Array r) where
  (+) = OT.zipWithA (+)
  (-) = OT.zipWithA (-)
  (*) = OT.zipWithA (*)
  negate = OT.mapA negate
  abs = OT.mapA abs
  signum = OT.mapA signum
  fromInteger = OT.constant [] . fromInteger

instance (OS.Shape sh, Numeric r) => Num (OS.Array sh r) where
  (+) = OS.zipWithA (+)
  (-) = OS.zipWithA (-)
  (*) = OS.zipWithA (*)
  negate = OS.mapA negate
  abs = OS.mapA abs
  signum = OS.mapA signum
  fromInteger = OS.constant . fromInteger

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
