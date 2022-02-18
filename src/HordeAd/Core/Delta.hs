-- | The second component of dual numbers, @Delta@, with it's evaluation
-- function. Neel Krishnaswami calls that "sparse vector expressions",
-- and indeed even in the simplest case of a function defined on scalars only,
-- the non-empty portion of the codomain of the evaluation function is a vector,
-- because the gradient of an @R^n@ to @R@ function is an @R^n@ vector.
--
-- The 'sparcity' is less obvious when the domain of the function consists
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
    Delta0 (..), Delta1 (..), Delta2 (..)
  , -- * Delta expression identifiers
    DeltaId, toDeltaId
  , -- * Evaluation of the delta expressions
    DeltaBinding
  , DeltaState (..)
  , evalBindings, ppBinding
  , bindInState0, bindInState1, bindInState2
  ) where

import Prelude

import           Control.Monad (unless, zipWithM_)
import           Control.Monad.ST.Strict (ST, runST)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Strict.Vector.Autogen.Mutable as Data.Vector.Mutable
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.Vector.Storable.Mutable
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
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
  deriving Show

-- | This is the grammar of delta-expressions at tensor rank 1, that is,
-- at vector level.
data Delta1 r =
    Zero1
  | Scale1 (Vector r) (Delta1 r)
  | Add1 (Delta1 r) (Delta1 r)
  | Var1 (DeltaId (Vector r))

  | Seq1 (Data.Vector.Vector (Delta0 r))
  | Konst1 (Delta0 r)
  | Append1 (Delta1 r) Int (Delta1 r)
  | Slice1 Int Int (Delta1 r) Int
  | SumRows1 (Delta2 r) Int
  | SumColumns1 (Delta2 r) Int

  | M_VD1 (Matrix r) (Delta1 r)  -- M_VD1 m vd == SumRows1 (M_MD2 m (AsRow2 vd))
  | MD_V1 (Delta2 r) (Vector r)  -- MD_V1 md v == SumRows1 (MD_M2 md (asRow v))
  deriving Show

-- | This is the grammar of delta-expressions at tensor rank 1, that is,
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
  | RowSlice2 Int Int (Delta2 r) Int Int
  | ColumnSlice2 Int Int (Delta2 r) Int Int

  | AsRow2 (Delta1 r)  -- AsRow2 vd == FromRows2 (V.replicate n vd)
  | AsColumn2 (Delta1 r)  -- AsColumn2 vd == FromColumns2 (V.replicate n vd)
  deriving Show


-- * Delta expression identifiers

newtype DeltaId a = DeltaId Int
  deriving Show

toDeltaId :: Int -> DeltaId a
toDeltaId = DeltaId

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
             => Int -> Int -> Int -> DeltaState r -> Delta0 r
             -> ( Vector r
                , Data.Vector.Vector (Vector r)
                , Data.Vector.Vector (Matrix r) )
evalBindings dim0 dim1 dim2 st deltaTopLevel =
  -- This is morally @V.create@ and so totally safe,
  -- but we can't just call @V.create@ thrice, because it would run
  -- the @ST@ action thrice, so we inline and extend @V.create@ here.
  runST $ do
    (finiteMap0, finiteMap1, finiteMap2) <- buildVectors st deltaTopLevel
    v0 <- V.unsafeFreeze $ VM.take dim0 finiteMap0
    v1 <- V.unsafeFreeze $ VM.take dim1 finiteMap1
    v2 <- V.unsafeFreeze $ VM.take dim2 finiteMap2
    -- Convert to normal matrices, but only the portion of vector
    -- that is not discarded.
    return (v0, v1, V.map MO.convertMatrixOuterOrNull v2)

buildVectors :: forall s r. (Eq r, Numeric r, Num (Vector r))
             => DeltaState r -> Delta0 r
             -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                     , Data.Vector.Mutable.MVector s (Vector r)
                     , Data.Vector.Mutable.MVector s (MO.MatrixOuter r) )
buildVectors st deltaTopLevel = do
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
      eval0 :: r -> Delta0 r -> ST s ()
      eval0 !r = \case
        Zero0 -> return ()
        Scale0 k d -> eval0 (k * r) d
        Add0 d e -> eval0 r d >> eval0 r e
        Var0 (DeltaId i) -> VM.modify store0 (+ r) i

        Dot0 vr vd -> eval1 (HM.scale r vr) vd
        SumElements0 vd n -> eval1 (HM.konst r n) vd
        Index0 d i k -> eval1 (HM.konst 0 k V.// [(i, r)]) d
      eval1 :: Vector r -> Delta1 r -> ST s ()
      eval1 !r = \case
        Zero1 -> return ()
        Scale1 k d -> eval1 (k * r) d
        Add1 d e -> eval1 r d >> eval1 r e
        Var1 (DeltaId i) -> VM.modify store1 (addToVector r) i

        Seq1 lsd -> V.imapM_ (\i d -> eval0 (r V.! i) d) lsd
        Konst1 d -> V.mapM_ (`eval0` d) r
        Append1 d k e -> eval1 (V.take k r) d >> eval1 (V.drop k r) e
        Slice1 i n d len ->
          eval1 (HM.konst 0 i V.++ r V.++ HM.konst 0 (len - i - n)) d
        M_VD1 m dRow ->
          mapM_ (`eval1` dRow)
                (MO.toRows (MO.MatrixOuter (Just m) (Just r) Nothing))
        MD_V1 md row -> eval2 (MO.MatrixOuter Nothing (Just r) (Just row)) md
        SumRows1 dm ncols -> eval2 (MO.asColumn r ncols) dm
        SumColumns1 dm nrows -> eval2 (MO.asRow r nrows) dm
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
  mapM_ evalUnlessZero (deltaBindings st)
  return (store0, store1, store2)

ppBinding :: (Show r, Numeric r) => DeltaBinding r -> [String]
ppBinding = \case
  DeltaBinding0 (DeltaId i) d ->
    ["letS DeltaId_", show i, " = ", ppShow d, "\n"]
  DeltaBinding1 (DeltaId i) d ->
    ["letV DeltaId_", show i, " = ", ppShow d, "\n"]
  DeltaBinding2 (DeltaId i) d ->
    ["letM DeltaId_", show i, " = ", ppShow d, "\n"]

bindInState0 :: Delta0 r -> DeltaState r -> (DeltaState r, DeltaId r)
{-# INLINE bindInState0 #-}
bindInState0 u' st =
  let dId = deltaCounter0 st
  in ( st { deltaCounter0 = succDeltaId dId
          , deltaBindings = DeltaBinding0 dId u' : deltaBindings st
          }
     , dId )

bindInState1 :: Delta1 r -> DeltaState r -> (DeltaState r, DeltaId (Vector r))
{-# INLINE bindInState1 #-}
bindInState1 u' st =
  let dId = deltaCounter1 st
  in ( st { deltaCounter1 = succDeltaId dId
          , deltaBindings = DeltaBinding1 dId u' : deltaBindings st
          }
     , dId )

bindInState2 :: Delta2 r -> DeltaState r -> (DeltaState r, DeltaId (Matrix r))
{-# INLINE bindInState2 #-}
bindInState2 u' st =
  let dId = deltaCounter2 st
  in ( st { deltaCounter2 = succDeltaId dId
          , deltaBindings = DeltaBinding2 dId u' : deltaBindings st
          }
     , dId )
