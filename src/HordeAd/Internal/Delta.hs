{-# LANGUAGE AllowAmbiguousTypes, CPP, DataKinds, GADTs, KindSignatures,
             StandaloneDeriving, TypeOperators #-}
#if !MIN_VERSION_base(4,16,0)
{-# LANGUAGE IncoherentInstances #-}
#endif
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
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
    Delta (..), Delta0, Delta1, Delta2, DeltaX, DeltaS (..)
  , Delta0Others (..), Delta1Others (..), Delta2Others (..), DeltaXOthers (..)
  , -- * Delta expression identifiers
    DeltaId, toDeltaId
  , -- * Evaluation of the delta expressions
    DeltaBinding
  , DeltaState (..)
  , DeltaLevel (..)
  , SDeltaLevel (..)
  , Domain0, Domain1, Domain2, DomainX, Domains
  , gradientFromDelta, derivativeFromDelta, ppBindings
  , bindInState0, bindInState1, bindInState2, bindInStateX
  , isTensorDummy
  ) where

import Prelude

import           Control.Exception (assert)
import           Control.Monad (unless, zipWithM_)
import           Control.Monad.ST.Strict (ST, runST)
import qualified Data.Array.Convert
import qualified Data.Array.Dynamic as OTB
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Internal
import qualified Data.Array.Internal.DynamicG
import qualified Data.Array.Internal.DynamicS
import qualified Data.Array.Shaped as OSB
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
-- Many operations span the ranks and so span the datatypes, which makes
-- the datatypes mutually recursive.
data Delta0Others v t1 tX tS =
    SumElements0 t1 Int  -- ^ see Note [SumElements0]
  | Index0 t1 Int Int  -- ^ second integer is the length of the vector

  | Dot0 v t1  -- ^ Dot0 v vd == SumElements0 (Scale1 v vd) n

  | FromX0 tX  -- ^ one of many conversions
  | FromS0 tS

deriving instance (Show v, Show t1, Show tX, Show tS)
  => Show (Delta0Others v t1 tX tS)

-- | This is the grammar of delta-expressions at tensor rank 1, that is,
-- at vector level.
data Delta1Others m v d0 d1 d2 dX =
    Seq1 (Data.Vector.Vector d0)  -- ^ "unboxing" conversion
  | Konst1 d0 Int  -- ^ length; needed only for forward derivative
  | Append1 d1 Int d1  -- ^ the length of the first argument
  | Slice1 Int Int d1 Int  -- ^ last integer is the length of argument
  | SumRows1 d2 Int  -- ^ the integer is the number of columns
  | SumColumns1 d2 Int  -- ^ the integer is the number of rows

  | M_VD1 m
          d1  -- ^ M_VD1 m vd == SumRows1 (M_MD2 m (AsRow2 vd))
  | MD_V1 d2
          v  -- ^ MD_V1 md v == SumRows1 (MD_M2 md (asRow v))

  | FromX1 dX

  | Reverse1 d1
  | Flatten1 Int Int d2
  | FlattenX1 OT.ShapeL dX

deriving instance (Show v, Show m, Show d0, Show d1, Show d2, Show dX)
    => Show (Delta1Others m v d0 d1 d2 dX)

-- | This is the grammar of delta-expressions at tensor rank 2, that is,
-- at matrix level.
data Delta2Others m d0 d1 d2 dX =
    FromRows2 (Data.Vector.Vector d1)  -- ^ "unboxing" conversion again
  | FromColumns2 (Data.Vector.Vector d1)
  | Konst2 d0 (Int, Int)  -- ^ size; needed only for forward derivative
  | Transpose2 d2
  | M_MD2 m d2  -- ^ matrix-(matrix-expression) multiplication
  | MD_M2 d2 m  -- ^ (matrix-expression)-matrix multiplication
  | RowAppend2 d2 Int d2  -- ^ row-length of first argument
  | ColumnAppend2 d2 Int d2  -- ^ col-length of first argument
  | RowSlice2 Int Int d2 Int  -- ^ last arg is row-length of the matrix
  | ColumnSlice2 Int Int d2 Int  -- ^ column-length of the matrix

  | AsRow2 d1  -- ^ AsRow2 vd == FromRows2 (V.replicate n vd)
  | AsColumn2 d1  -- ^ AsColumn2 vd == FromColumns2 (V.replicate n vd)

  | FromX2 dX

  | Flipud2 d2
  | Fliprl2 d2
  | Reshape2 Int d1
  | Conv2 m d2

deriving instance (Show m, Show d0, Show d1, Show d2, Show dX)
    => Show (Delta2Others m d0 d1 d2 dX)

-- | This is the grammar of delta-expressions at arbitrary tensor rank.
--
-- Warning: not tested enough nor benchmarked.
data DeltaXOthers d0 d1 d2 dX =
    KonstX d0 OT.ShapeL  -- ^ size; needed only for forward derivative
  | AppendX dX Int dX
      -- ^ Append two arrays along the outermost dimension.
      -- All dimensions, except the outermost, must be the same.
      -- The integer argument is the outermost size of the first array.
  | SliceX Int Int dX Int
      -- ^ Extract a slice of an array along the outermost dimension.
      -- The extracted slice must fall within the dimension.
      -- The last argument is the outermost size of the argument array.
  | IndexX dX Int Int
      -- ^ The sub-tensors at the given index of the outermost dimension.
      -- The second integer is the length of the dimension.
  | RavelFromListX [dX]
      -- ^ Create a tensor from a list treated as the outermost dimension.
  | ReshapeX OT.ShapeL OT.ShapeL dX
      -- ^ Change the shape of the tensor from the first to the second.

  | From0X d0
  | From1X d1
  | From2X d2 Int

deriving instance (Show d0, Show d1, Show d2, Show dX)
    => Show (DeltaXOthers d0 d1 d2 dX)

-- | This is the grammar of delta-expressions at arbitrary tensor rank,
-- the fully typed Shaped version.
--
-- Warning: not tested enough nor benchmarked.
data DeltaS :: Type -> [Nat] -> Type where
  ZeroS :: DeltaS r sh
  ScaleS :: OS.Array sh r -> DeltaS r sh -> DeltaS r sh
  AddS :: DeltaS r sh -> DeltaS r sh -> DeltaS r sh
  VarS :: DeltaId 'DX -> DeltaS r sh

  KonstS :: Delta0 r -> DeltaS r sh
  AppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
          => DeltaS r (m ': sh) -> DeltaS r (n ': sh)
          -> DeltaS r ((m + n) ': sh)
    -- ^ Append two arrays along the outermost dimension.
  SliceS :: (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
         => Proxy i -> Proxy n -> DeltaS r (i + n + k ': rest)
         -> DeltaS r (n ': rest)
    -- ^ Extract a slice of an array along the outermost dimension.
  IndexS :: (KnownNat ix, KnownNat k, OS.Shape rest)
         => DeltaS r (ix + 1 + k ': rest) -> Proxy ix -> DeltaS r rest
    -- ^ The sub-tensors at the given index of the outermost dimension.
  RavelFromListS :: (KnownNat k, OS.Shape rest)
                 => [DeltaS r rest] -> DeltaS r (k : rest)
    -- ^ Create a tensor from a list treated as the outermost dimension.
  ReshapeS :: (OS.Shape sh, OS.Shape sh', OS.Size sh ~ OS.Size sh')
           => DeltaS r sh -> DeltaS r sh'
    -- ^ Change the shape of the tensor.

  From0S :: Delta0 r -> DeltaS r '[]
  From1S :: Delta1 r -> DeltaS r '[n]
  From2S :: KnownNat cols
         => Proxy cols -> Delta2 r -> DeltaS r '[rows, cols]
  FromXS :: DeltaX r -> DeltaS r sh

instance Show (DeltaS r sh) where
  show _ = "a DeltaS delta expression"


-- * Delta expression identifiers

toDeltaId :: Int -> DeltaId a
toDeltaId = DeltaId

-- The key property is that it preserves the phantom type.
succDeltaId :: DeltaId a -> DeltaId a
succDeltaId (DeltaId i) = DeltaId (succ i)


-- * Evaluation of the delta expressions

data DeltaLevel = D0 | D1 | D2 | DX

data SDeltaLevel a where
  SD0 :: SDeltaLevel 'D0
  SD1 :: SDeltaLevel 'D1
  SD2 :: SDeltaLevel 'D2
  SDX :: SDeltaLevel 'DX

type Delta0 r = Delta r 'D0
type Delta1 r = Delta r 'D1
type Delta2 r = Delta r 'D2
type DeltaX r = Delta r 'DX

deriving instance (Show r, Numeric r) => Show (Delta r d)

data Delta (r :: Type) (d :: DeltaLevel) where
  Zero0 :: Delta r 'D0
  Scale0 :: r -> Delta0 r -> Delta r 'D0
  Add0 :: Delta0 r -> Delta0 r -> Delta r 'D0
  Var0 :: DeltaId 'D0 -> Delta r 'D0
  Delta0Others :: Delta0Others (Vector r) (Delta1 r) (DeltaX r) (DeltaS r '[])
               -> Delta r 'D0

  Zero1 :: Delta r 'D1
  Scale1 :: Vector r -> Delta1 r -> Delta r 'D1
  Add1 :: Delta1 r -> Delta1 r -> Delta r 'D1
  Var1 :: DeltaId 'D1 -> Delta r 'D1
  FlattenS1 :: OS.Shape sh => DeltaS r sh -> Delta r 'D1
  FromS1 :: KnownNat len => DeltaS r '[len] -> Delta r 'D1
  Delta1Others :: Delta1Others (Matrix r) (Vector r) (Delta0 r) (Delta1 r) (Delta2 r) (DeltaX r)
               -> Delta r 'D1

  Zero2 :: Delta r 'D2
  Scale2 :: Matrix r -> Delta2 r -> Delta r 'D2
  Add2 :: Delta2 r -> Delta2 r -> Delta r 'D2
  Var2 :: DeltaId 'D2 -> Delta r 'D2
  FromS2 :: (KnownNat rows, KnownNat cols)
         =>DeltaS r '[rows, cols]-> Delta r 'D2

  Delta2Others :: Delta2Others (Matrix r) (Delta0 r) (Delta1 r) (Delta2 r) (DeltaX r)
               -> Delta r 'D2

  ZeroX :: Delta r 'DX
  ScaleX :: OT.Array r -> DeltaX r ->  Delta r 'DX
  AddX :: DeltaX r -> DeltaX r -> Delta r 'DX
  VarX :: DeltaId 'DX -> Delta r 'DX
  FromSX :: OS.Shape sh
         => DeltaS r sh -> Delta r 'DX
  DeltaXOthers :: DeltaXOthers (Delta0 r) (Delta1 r) (Delta2 r) (DeltaX r)
               -> Delta r 'DX

newtype DeltaId (d :: DeltaLevel) where
  DeltaId :: Int -> DeltaId d
  deriving Show

-- | Binding at one of the ranks, with a given underlying scalar.
--
-- The 'DeltaId' components could be re-computed on the fly in 'buildFinMaps',
-- but it costs more (they are boxed, so re-allocation is expensive)
-- than storing them here at the time of binding creation and accessing
-- in `buildFinMaps`.
data DeltaBinding r where
  DeltaBinding :: SDeltaLevel d -> DeltaId d -> Delta r d -> DeltaBinding r

data DeltaState r = DeltaState
  { deltaCounter0 :: DeltaId 'D0
  , deltaCounter1 :: DeltaId 'D1
  , deltaCounter2 :: DeltaId 'D2
  , deltaCounterX :: DeltaId 'DX
  , deltaBindings :: [DeltaBinding r]
  }

-- | Helper definitions to shorten type signatures. Note that these
-- differ from their counterparts in all other modules, because the type
-- argument here is the underlying scalar (e.g., @Double),
-- while elsewhere it's the dual component of dual numbers from
-- rank 0 (scalar) level (e.g., @Delta0 Double@).
-- By chance, these definitions and definitions from other modules
-- coincide in case of "forward derivatives computed on the spot"
-- where @r@ is @Double@ and @Double@ is also the dual component.
--
-- More generally, @r@ in this module tends to refer to the underlying
-- scalar type, while in all other modules it refers to the rank 0 dual
-- component type.
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
-- > dt <.> derivativeFromDelta st d ds = gradientFromDelta st d dt <.> ds
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
gradientFromDelta :: (Eq r, Numeric r, Num (Vector r))
                  => Int -> Int -> Int -> Int -> DeltaState r -> Delta0 r -> r
                  -> Domains r
gradientFromDelta dim0 dim1 dim2 dimX st deltaTopLevel dt =
  -- This is morally @V.create@ and so totally safe,
  -- but we can't just call @V.create@ thrice, because it would run
  -- the @ST@ action thrice, so we inline and extend @V.create@ here.
  runST $ do
    (finMap0, finMap1, finMap2, finMapX) <- buildFinMaps st deltaTopLevel dt
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
  let DeltaId counter0 = deltaCounter0 st
      DeltaId counter1 = deltaCounter1 st
      DeltaId counter2 = deltaCounter2 st
      DeltaId counterX = deltaCounterX st
  finMap0 <- VM.replicate counter0 0  -- correct value
  finMap1 <- VM.replicate counter1 (V.empty :: Vector r)  -- dummy value
  finMap2 <- VM.replicate counter2 MO.emptyMatrixOuter  -- dummy value
  finMapX <- VM.replicate counterX dummyTensor
  return (finMap0, finMap1, finMap2, finMapX)

buildFinMaps :: forall s r. (Eq r, Numeric r, Num (Vector r))
             => DeltaState r -> Delta0 r -> r
             -> ST s ( Data.Vector.Storable.Mutable.MVector s r
                     , Data.Vector.Mutable.MVector s (Vector r)
                     , Data.Vector.Mutable.MVector s (MO.MatrixOuter r)
                     , Data.Vector.Mutable.MVector s (OT.Array r) )
buildFinMaps st deltaTopLevel dt = do
  (finMap0, finMap1, finMap2, finMapX) <- initializeFinMaps st
  let addToVector :: Vector r -> Vector r -> Vector r
      addToVector r = \v -> if V.null v then r else v + r
      addToMatrix :: MO.MatrixOuter r -> MO.MatrixOuter r -> MO.MatrixOuter r
      addToMatrix r = \v -> if MO.nullMatrixOuter v then r else MO.plus v r
      addToArray :: OT.Array r -> OT.Array r -> OT.Array r
      addToArray r = \v -> if isTensorDummy v then r else OT.zipWithA (+) v r
      addToArrayS :: OS.Shape sh => OS.Array sh r -> OT.Array r -> OT.Array r
      addToArrayS r = \v -> let rs = Data.Array.Convert.convert r
                            in if isTensorDummy v
                               then rs
                               else OT.zipWithA (+) v rs
      eval0 :: r -> Delta0 r -> ST s ()
      eval0 !r = \case
        Zero0 -> return ()
        Scale0 k d -> eval0 (k * r) d
        Add0 d e -> eval0 r d >> eval0 r e
        Var0 (DeltaId i) -> VM.modify finMap0 (+ r) i

        Delta0Others d0 -> case d0 of
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
        FromS1 d -> evalS (OS.fromVector r) d
        FlattenS1 d -> evalS (OS.fromVector r) d

        Delta1Others d1 -> case d1 of
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
            FlattenX1 sh d -> evalX (OT.fromVector sh r) d

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
        FromS2 d -> evalS (OS.fromVector $ V.concat $ MO.toRows r) d

        Delta2Others d2 -> case d2 of
            FromRows2 lvd -> zipWithM_ eval1 (MO.toRows r) (V.toList lvd)
            FromColumns2 lvd -> zipWithM_ eval1 (MO.toColumns r) (V.toList lvd)
            Konst2 d _sz -> mapM_ (V.mapM_ (`eval0` d)) $ MO.toRows r
            Transpose2 md -> eval2 (MO.transpose r) md  -- TODO: test!
            M_MD2 m md -> zipWithM_ (\rRow row -> eval1 rRow (Delta1Others (MD_V1 md row)))
                                    (HM.toRows m) (MO.toRows r)
    --      inlining eval1 to demonstrate the calls to eval2 with outer products:
    --      M_MD2 m md ->
    --        zipWithM_ (\rRow row ->
    --                     eval2 (MO.MatrixOuter Nothing (Just rRow) (Just row)) md)
    --                  (HM.toRows m) (MO.toRows r)
            MD_M2 md m -> zipWithM_ (\rCol col -> eval1 rCol (Delta1Others (MD_V1 md col)))
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
        FromSX d -> evalS (Data.Array.Convert.convert r) d

        DeltaXOthers dX -> case dX of
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
                       d  -- TODO: optimize for Var case
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
      evalS :: OS.Shape sh
            => OS.Array sh r -> DeltaS r sh -> ST s ()
      evalS !r = \case
        ZeroS -> return ()
        ScaleS k d -> evalS (OS.zipWithA (*) k r) d
        AddS d e -> evalS r d >> evalS r e
        VarS (DeltaId i) -> VM.modify finMapX (addToArrayS r) i

        KonstS d -> mapM_ (`eval0` d) $ OS.toList r
        AppendS (d :: DeltaS r (k ': rest)) (e :: DeltaS r (l ': rest)) ->
          evalS (OS.slice @'[ '(0, k) ] r) d
          >> evalS (OS.slice @'[ '(k, l) ] r) e
        SliceS (_ :: Proxy i) _ (d :: DeltaS r (i_plus_n_plus_k ': rest)) ->
          evalS (OS.constant @(i ': rest) 0
                 `OS.append` r
                 `OS.append` OS.constant 0)
                d
        IndexS (d :: DeltaS r (ix_plus_1_plus_k ': rest)) (_ :: Proxy ix) ->
          evalS (OS.constant @(ix ': rest) 0
                 `OS.append` OS.reshape r
                 `OS.append` OS.constant 0)
                d  -- TODO: optimize for Var case
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

  eval0 dt deltaTopLevel

  let evalUnlessZero :: DeltaBinding r -> ST s ()
      evalUnlessZero (DeltaBinding SD0 (DeltaId i) d) = do
        r <- finMap0 `VM.read` i
        unless (r == 0) $  -- we init with exactly 0.0 so the comparison works
          eval0 r d
      evalUnlessZero (DeltaBinding SD1 (DeltaId i) d) = do
        r <- finMap1 `VM.read` i
        unless (V.null r) $
          eval1 r d
      evalUnlessZero (DeltaBinding SD2 (DeltaId i) d) = do
        r <- finMap2 `VM.read` i
        unless (MO.nullMatrixOuter r) $
          eval2 r d
      evalUnlessZero (DeltaBinding SDX (DeltaId i) d) =do
        r <- finMapX `VM.read` i
        unless (isTensorDummy r) $
          evalX r d
  mapM_ evalUnlessZero (deltaBindings st)
  return (finMap0, finMap1, finMap2, finMapX)

-- | Forward derivative computation via forward-evaluation of delta-expressions
-- (which is surprisingly competitive to the direct forward method,
-- until the allocation of deltas gets large enough to affect cache hits).
-- This is the directional derivative, calculated for the point,
-- at which the delta expression was computed (which is the point
-- represented by the parameters of the objective function and used
-- to compute it's dual number result) and along the direction vector(s)
-- given in the last parameter called @ds@.
derivativeFromDelta :: forall r. (Numeric r, Num (Vector r))
                    => DeltaState r -> Delta0 r -> Domains r -> r
derivativeFromDelta st deltaTopLevel
                    _ds@(params0Init, params1Init, params2Init, paramsXInit) =
  let eval0 :: Domains r -> Delta0 r -> r
      eval0 parameters@(params0, _, _, _) = \case
        Zero0 -> 0
        Scale0 k d -> k * eval0 parameters d
        Add0 d e -> eval0 parameters d + eval0 parameters e
        Var0 (DeltaId i) -> params0 V.! i

        Delta0Others d0 -> case d0 of
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

        FromS1 d -> OS.toVector $ evalS parameters d
        FlattenS1 d -> OS.toVector $ evalS parameters d

        Delta1Others d1 -> case d1 of
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

            Reverse1 d -> V.reverse $ eval1 parameters d
            Flatten1 _rows _cols d -> HM.flatten $ eval2 parameters d
            FlattenX1 _sh d -> OT.toVector $ evalX parameters d
      eval2 :: Domains r -> Delta2 r -> Matrix r
      eval2 parameters@( _, _, params2, _) = \case
        Zero2 -> 0
        Scale2 k d -> k * eval2 parameters d
        Add2 d e -> eval2 parameters d + eval2 parameters e
        Var2 (DeltaId i) -> params2 V.! i

        FromS2 d ->
          let t = evalS parameters d
          in case OS.shapeL t of
            [_rows, cols] -> HM.reshape cols $ OS.toVector t
            _ -> error "eval2: wrong tensor dimensions"

        Delta2Others d2 -> case d2 of
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
        FromSX d -> Data.Array.Convert.convert $ evalS parameters d

        DeltaXOthers dX -> case dX of
            KonstX d sz -> OT.constant sz $ eval0 parameters d
            AppendX d _k e -> evalX parameters d `OT.append` evalX parameters e
            SliceX i n d _len -> OT.slice [(i, n)] $ evalX parameters d
            IndexX d ix _len -> OT.index (evalX parameters d) ix
            RavelFromListX ld ->
              let la = map (evalX parameters) ld
                  sh = case la of
                    a : _ -> length la : OT.shapeL a
                    [] -> []
              in OT.ravel $ OTB.fromList sh la
            ReshapeX _sh sh' d -> OT.reshape sh' $ evalX parameters d

            From0X d -> OT.scalar $ eval0 parameters d
            From1X d -> let v = eval1 parameters d
                        in OT.fromVector [V.length v] v
            From2X d cols -> let l = eval2 parameters d
                             in OT.fromVector [HM.rows l, cols] $ HM.flatten l
      evalS :: OS.Shape sh => Domains r -> DeltaS r sh -> OS.Array sh r
      evalS parameters@( _, _, _, paramsX) = \case
        ZeroS -> 0
        ScaleS k d -> k * evalS parameters d
        AddS d e -> evalS parameters d + evalS parameters e
        VarS (DeltaId i) -> Data.Array.Convert.convert $ paramsX V.! i

        KonstS d -> OS.constant $ eval0 parameters d
        AppendS d e -> evalS parameters d `OS.append` evalS parameters e
        SliceS (_ :: Proxy i) (_ :: Proxy n) d ->
          OS.slice @'[ '(i, n) ] $ evalS parameters d
        IndexS d proxyIx ->
          OS.index (evalS parameters d) (fromInteger $ natVal proxyIx)
        RavelFromListS ld ->
          let la = map (evalS parameters) ld
          in OS.ravel $ OSB.fromList la
        ReshapeS d -> OS.reshape $ evalS parameters d

        From0S d -> OS.scalar $ eval0 parameters d
        From1S d -> OS.fromVector $ eval1 parameters d
        From2S _ d -> OS.fromVector $ HM.flatten $ eval2 parameters d
        FromXS d -> Data.Array.Convert.convert $ evalX parameters d
      evalUnlessZero :: Domains r -> DeltaBinding r -> Domains r
      evalUnlessZero parameters@(!params0, !params1, !params2, !paramsX) = \case
        DeltaBinding SD0 (DeltaId i) d ->
          let v = eval0 parameters d
          in (params0 V.// [(i, v)], params1, params2, paramsX)
        DeltaBinding SD1 (DeltaId i) d ->
          let v = eval1 parameters d
          in (params0, params1 V.// [(i, v)], params2, paramsX)
        DeltaBinding SD2 (DeltaId i) d ->
          let v = eval2 parameters d
          in (params0, params1, params2 V.// [(i, v)], paramsX)
        DeltaBinding SDX (DeltaId i) d ->
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
  DeltaBinding SD0 (DeltaId i) d ->
    [prefix ++ "0 DeltaId_", show i, " = ", ppShow d, "\n"]
  DeltaBinding SD1 (DeltaId i) d ->
    [prefix ++ "1 DeltaId_", show i, " = ", ppShow d, "\n"]
  DeltaBinding SD2 (DeltaId i) d ->
    [prefix ++ "2 DeltaId_", show i, " = ", ppShow d, "\n"]
  DeltaBinding SDX (DeltaId i) d ->
    [prefix ++ "X DeltaId_", show i, " = ", ppShow d, "\n"]

bindInState :: (DeltaId a -> t -> DeltaBinding r)
            -> (DeltaState r -> DeltaId a)
            -> (DeltaId a -> DeltaState r -> a1)
            -> t
            -> DeltaState r
            -> (a1, DeltaId a)
bindInState deltaBinding deltaCounter setDeltaCounter u' st =
  let dId = deltaCounter st
      !binding = deltaBinding dId u'
  in ( setDeltaCounter (succDeltaId dId)
         (st { deltaBindings = binding : deltaBindings st })
     , dId )

bindInState0 :: Delta0 r -> DeltaState r -> (DeltaState r, DeltaId 'D0)
{-# INLINE bindInState0 #-}
bindInState0 = bindInState (\x y -> DeltaBinding SD0 x y) deltaCounter0 (\d st -> st { deltaCounter0 = d })

bindInState1 :: Delta1 r -> DeltaState r -> (DeltaState r, DeltaId 'D1)
{-# INLINE bindInState1 #-}
bindInState1 = bindInState (\x y -> DeltaBinding SD1 x y) deltaCounter1 (\d st -> st { deltaCounter1 = d })

bindInState2 :: Delta2 r -> DeltaState r -> (DeltaState r, DeltaId 'D2)
{-# INLINE bindInState2 #-}
bindInState2 = bindInState (\x y -> DeltaBinding SD2 x y) deltaCounter2 (\d st -> st { deltaCounter2 = d })

bindInStateX :: DeltaX r -> DeltaState r -> (DeltaState r, DeltaId 'DX)
{-# INLINE bindInStateX #-}
bindInStateX = bindInState (\x y -> DeltaBinding SDX x y) deltaCounterX (\d st -> st { deltaCounterX = d })

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
