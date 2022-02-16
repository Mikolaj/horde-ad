{-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving #-}
-- | The second component of dual numbers, @Delta@, with it's evaluation
-- function. Neel Krishnaswami calls that "sparse vector expressions",
-- and indeed even in the simplest case of a function defined on scalars only,
-- the non-empty portion of the codomain of the evaluation function is a vector,
-- because the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
--
-- This gets muddled when the domain of the function may consist
-- of multiple vectors and matrices and when the expressions themselves
-- start containing vectors and matrices. However, a single tiny delta
-- expression (e.g., a sum of two variables) may denote a vector of matrices.
-- Even a delta expression containing a big matrix denotes something much
-- bigger: a whole vector of such matrices (and vectors and scalars).
--
-- The algebraic structure here is an extension of vector space.
-- The crucial extra constructor for variables is used both to represent
-- sharing in order to avoid exponential blowup and to replace the one-hot
-- functionality with something cheaper and more uniform.
-- A lot of the remaining additional structure is for introducing
-- and reducing dimensions.
module HordeAd.Core.Delta
  ( Delta (..)
  , DeltaId (..)
  , DeltaBinding (..)
  , DeltaState (..)
  , evalBindings
  ) where

import Prelude

import           Control.Monad (unless, zipWithM_)
import           Control.Monad.ST.Strict (ST, runST)
import           Data.Kind (Type)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import qualified HordeAd.Internal.MatrixOuter as MO

-- | This is the grammar of delta-expressions.
-- They have different but inter-related semantics at the level
-- of scalars, vectors and matrices (WIP: and arbitrary tensors).
-- Some make sense only on one of the levels, as expressed by the GADT
-- type constraints (WIP: currently this is broken by conflating
-- level-polymorphism and the polymorphism wrt the underlying scalar type
-- (Float, Double, etc.)).
--
-- In other words, for each choice of the underlying scalar type @r@,
-- we have three primitive differentiable types based on the scalar:
-- the scalar type @r@ itself, @Vector r@ and @Matrix r@.
data Delta :: Type -> Type where
  -- These constructors make sense at all levels: scalars, vectors, matrices,
  -- tensors. All constructors focusing on scalars belong to this group,
  -- that is, they make sense also for vectors, etc., and have more or less
  -- analogous semantics at the non-scalar levels.
  Zero :: Delta a
  Scale :: a -> Delta a -> Delta a
  Add :: Delta a -> Delta a -> Delta a
  Var :: DeltaId a -> Delta a

  Dot1 :: Vector r -> Delta (Vector r) -> Delta r
  SumElements1 :: Delta (Vector r) -> Int -> Delta r
  Index1 :: Delta (Vector r) -> Int -> Int -> Delta r

  Seq1 :: Data.Vector.Vector (Delta r) -> Delta (Vector r)
  Konst1 :: Delta r -> Delta (Vector r)
  Append1 :: Delta (Vector r) -> Int -> Delta (Vector r) -> Delta (Vector r)
  Slice1 :: Int -> Int -> Delta (Vector r) -> Int -> Delta (Vector r)
  M_VD2 :: Matrix r -> Delta (Vector r) -> Delta (Vector r)
  MD_V2 :: Delta (Matrix r) -> Vector r -> Delta (Vector r)
  SumRows2 :: Delta (Matrix r) -> Int -> Delta (Vector r)
  SumColumns2 :: Delta (Matrix r) -> Int -> Delta (Vector r)

  Seq2 :: Data.Vector.Vector (Delta (Vector r)) -> Delta (Matrix r)
  Transpose2 :: Delta (Matrix r) -> Delta (Matrix r)
  M_MD2 :: Matrix r -> Delta (Matrix r) -> Delta (Matrix r)
  MD_M2 :: Delta (Matrix r) -> Matrix r -> Delta (Matrix r)
  AsRow2 :: Delta (Vector r) -> Delta (Matrix r)
  AsColumn2 :: Delta (Vector r) -> Delta (Matrix r)
  RowAppend2 :: Delta (Matrix r) -> Int -> Delta (Matrix r) -> Delta (Matrix r)
  ColumnAppend2
    :: Delta (Matrix r) -> Int -> Delta (Matrix r) -> Delta (Matrix r)
  RowSlice2 :: Int -> Int -> Delta (Matrix r) -> Int -> Int -> Delta (Matrix r)
  ColumnSlice2
    :: Int -> Int -> Delta (Matrix r) -> Int -> Int -> Delta (Matrix r)

newtype DeltaId a = DeltaId Int
  deriving (Show, Eq)

-- The @DeltaId@ components could be computed on the fly when evaluating,
-- but it costs more (they are boxed) than storing them here at the time
-- of binding creation.
data DeltaBinding r =
    DScalar (DeltaId r) (Delta r)
  | DVector (DeltaId (Vector r)) (Delta (Vector r))
  | DMatrix (DeltaId (Matrix r)) (Delta (Matrix r))

data DeltaState r = DeltaState
  { deltaCounter0 :: DeltaId r
  , deltaCounter1 :: DeltaId (Vector r)
  , deltaCounter2 :: DeltaId (Matrix r)
  , deltaBindings :: [DeltaBinding r]
  }

-- | This is the semantics of delta expressions. An expression of type @Delta a@
-- denotes a collection of finite maps from @DeltaId xi@ to @xi@, where
-- @xi@ belong to a finite set of types with the same underlying scalar type
-- as @a@. Each map is represented as a vector, small examples of which
-- are those in the result type of @evalBindings@. Requested lengths
-- of the vectors in the result type are given in the first few arguments.
-- The delta state contains a list of mutually-referencing delta bindings
-- that are to be evaluated, in the given order, starting with the top-level
-- binding of a scalar type provided in the remaining argument.
evalBindings :: (Eq r, Numeric r, Num (Vector r))
             => Int -> Int -> Int -> DeltaState r -> Delta r
             -> ( Vector r
                , Data.Vector.Vector (Vector r)
                , Data.Vector.Vector (Matrix r) )
evalBindings dim0 dim1 dim2 st dTopLevel =
  -- This is morally @V.create@ and so totally safe,
  -- but we can't just call @V.create@ thrice, because it would run
  -- the @ST@ action thrice, so we inline and extend @V.create@ here.
  runST $ do
    (finiteMap0, finiteMap1, finiteMap2) <- buildVectors st dTopLevel
    v0 <- V.unsafeFreeze $ VM.take dim0 finiteMap0
    v1 <- V.unsafeFreeze $ VM.take dim1 finiteMap1
    v2 <- V.unsafeFreeze $ VM.take dim2 finiteMap2
    -- Convert to normal matrices, but only the portion of vector
    -- that is not discarded.
    return (v0, v1, V.map MO.convertMatrixOuterOrNull v2)

buildVectors :: forall s r. (Eq r, Numeric r, Num (Vector r))
             => DeltaState r -> Delta r
             -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                     , Data.Vector.Mutable.MVector s (Vector r)
                     , Data.Vector.Mutable.MVector s (MO.MatrixOuter r) )
buildVectors st dTopLevel = do
  let DeltaId counter0 = deltaCounter0 st
      DeltaId counter1 = deltaCounter1 st
      DeltaId counter2 = deltaCounter2 st
  store0 <- VM.replicate counter0 0  -- correct value
  store1 <- VM.replicate counter1 (V.empty :: Vector r)  -- dummy value
  store2 <- VM.replicate counter2 MO.emptyMatrixOuter  -- dummy value
  let addToVector :: Vector r -> Vector r -> Vector r
      addToVector r = \v -> if V.null v then r else v + r
      addToMatrix :: MO.MatrixOuter r -> MO.MatrixOuter r -> MO.MatrixOuter r
      addToMatrix r = \v -> if MO.nullMatrixOuter v then r else MO.plus v r
      eval0 :: r -> Delta r -> ST s ()
      eval0 !r = \case
        Zero -> return ()
        Scale k d -> eval0 (k * r) d
        Add d e -> eval0 r d >> eval0 r e
        Var (DeltaId i) -> VM.modify store0 (+ r) i
        Dot1 vr vd -> eval1 (HM.scale r vr) vd
        SumElements1 vd n -> eval1 (HM.konst r n) vd
        Index1 d i k -> eval1 (HM.konst 0 k V.// [(i, r)]) d

        -- Most of the impossible cases will be ruled out by GADT
        -- once the conflation fo parameterizations is cleared.
        Seq1{} -> error "buildVectors: Seq1 can't result in a scalar"
        Konst1{} -> error "buildVectors: Konst1 can't result in a scalar"
        Append1{} -> error "buildVectors: Append1 can't result in a scalar"
        Slice1{} -> error "buildVectors: Slice1 can't result in a scalar"
        Seq2{} -> error "buildVectors: Seq2 can't result in a scalar"
        Transpose2{} ->
          error "buildVectors: Transpose2 can't result in a scalar"
        M_VD2{} -> error "buildVectors: MxVD2 can't result in a scalar"
        MD_V2{} -> error "buildVectors: MDxV2 can't result in a scalar"
        M_MD2{} -> error "buildVectors: MxMD2 can't result in a scalar"
        MD_M2{} -> error "buildVectors: MDxM2 can't result in a scalar"
        SumRows2{} -> error "buildVectors: SumRows2 can't result in a scalar"
        SumColumns2{} ->
          error "buildVectors: SumColumns2 can't result in a scalar"
        AsRow2{} -> error "buildVectors: AsRow2 can't result in a scalar"
        AsColumn2{} -> error "buildVectors: AsColumn2 can't result in a scalar"
        RowAppend2{} ->
          error "buildVectors: RowAppend2 can't result in a scalar"
        ColumnAppend2{} ->
          error "buildVectors: ColumnAppend2 can't result in a scalar"
        RowSlice2{} -> error "buildVectors: RowSlice2 can't result in a scalar"
        ColumnSlice2{} ->
          error "buildVectors: ColumnSlice2 can't result in a scalar"
      eval1 :: Vector r -> Delta (Vector r) -> ST s ()
      eval1 !r = \case
        Zero -> return ()
        Scale k d -> eval1 (k * r) d
        Add d e -> eval1 r d >> eval1 r e
        Var (DeltaId i) -> VM.modify store1 (addToVector r) i
        Seq1 vd -> V.imapM_ (\i d -> eval0 (r V.! i) d) vd
        Konst1 d -> V.mapM_ (`eval0` d) r
        Append1 d k e -> eval1 (V.take k r) d >> eval1 (V.drop k r) e
        Slice1 i n d len ->
          eval1 (HM.konst 0 i V.++ r V.++ HM.konst 0 (len - i - n)) d
        M_VD2 m dRow ->
          mapM_ (`eval1` dRow)
                (MO.toRows (MO.MatrixOuter (Just m) (Just r) Nothing))
        MD_V2 md row -> eval2 (MO.MatrixOuter Nothing (Just r) (Just row)) md
        SumRows2 dm ncols -> eval2 (MO.asColumn r ncols) dm
        SumColumns2 dm nrows -> eval2 (MO.asRow r nrows) dm

        Dot1{} -> error "buildVectors: unboxed vectors of vectors not possible"
        SumElements1{} ->
          error "buildVectors: unboxed vectors of vectors not possible"
        Index1{} ->
          error "buildVectors: unboxed vectors of vectors not possible"
      eval2 :: MO.MatrixOuter r -> Delta (Matrix r) -> ST s ()
      eval2 !r = \case
        Zero -> return ()
        Scale k d -> eval2 (MO.multiplyWithOuter k r) d
        Add d e -> eval2 r d >> eval2 r e
        Var (DeltaId i) -> VM.modify store2 (addToMatrix r) i
        Seq2 md -> zipWithM_ eval1 (MO.toRows r) (V.toList md)
        Transpose2 md -> eval2 (MO.transpose r) md  -- TODO: test!
        M_MD2 m md -> zipWithM_ (\rRow row -> eval1 rRow (MD_V2 md row))
                                (HM.toRows m) (MO.toRows r)
--      M_MD2 m md ->
--        zipWithM_ (\rRow row ->
--                     eval2 (MO.MatrixOuter Nothing (Just rRow) (Just row)) md)
--                  (HM.toRows m) (MO.toRows r)
        MD_M2 md m -> zipWithM_ (\rCol col -> eval1 rCol (MD_V2 md col))
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
        RowSlice2 i n d nrows ncols ->
          eval2 (MO.konst 0 i ncols `MO.rowAppend` r
                `MO.rowAppend`
                MO.konst 0 (nrows - i - n) ncols)
                d
        ColumnSlice2 i n d nrows ncols ->
          eval2 (MO.konst 0 nrows i `MO.columnAppend` r
                `MO.columnAppend`
                MO.konst 0 nrows (ncols - i - n))
                d

        Dot1{} -> error "buildVectors: unboxed vectors of vectors not possible"
        SumElements1{} ->
          error "buildVectors: unboxed vectors of vectors not possible"
        Index1{} ->
          error "buildVectors: unboxed vectors of vectors not possible"
  eval0 1 dTopLevel  -- dt is 1 or hardwired in f
  let evalUnlessZero :: DeltaBinding r -> ST s ()
      evalUnlessZero (DScalar (DeltaId i) d) = do
        r <- store0 `VM.read` i
        unless (r == 0) $  -- we init with exactly 0 so the comparison is OK
          eval0 r d
      evalUnlessZero (DVector (DeltaId i) d) = do
        r <- store1 `VM.read` i
        unless (V.null r) $
          eval1 r d
      evalUnlessZero (DMatrix (DeltaId i) d) = do
        r <- store2 `VM.read` i
        unless (MO.nullMatrixOuter r) $
          eval2 r d
  mapM_ evalUnlessZero (deltaBindings st)
  return (store0, store1, store2)
