{-# LANGUAGE AllowAmbiguousTypes, CPP, ConstraintKinds, DataKinds,
             FlexibleInstances, MultiParamTypeClasses, PolyKinds,
             QuantifiedConstraints, TypeFamilyDependencies, TypeOperators,
             UndecidableInstances #-}
#if !MIN_VERSION_base(4,17,0)
{-# LANGUAGE IncoherentInstances #-}
#endif
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | The class of dual components of dual numbers and related classes,
-- constraints and instances.
module HordeAd.Core.DualClass
  ( IsDualWithScalar, IsDualWithScalarVar, IsScalar, IsScalarVar
  , HasDelta, HasForward
  , IsDual(Primal, dZero, dScale, dAdd)
  , IsDualVar(dVar, bindInState)
  , HasRanks(..), TensorS
  , Delta0  -- re-export; should be rarely used
  ) where

import Prelude

import qualified Data.Array.Convert
import qualified Data.Array.Dynamic as OTB
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.Shaped as OSB
import qualified Data.Array.ShapedS as OS
import           Data.Kind (Type)
import           Data.Proxy (Proxy)
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import           Numeric.LinearAlgebra (Matrix, Numeric, Vector)
import qualified Numeric.LinearAlgebra as HM

import HordeAd.Internal.Delta

-- * Abbreviations for export (not used anywhere below)

-- | A shorthand for a useful set of constraints. The intended semantics
-- (not fully enforced by the constraints in isolation) is that the first
-- type is a dual component of a dual number type at an unknown rank
-- and the second type is a dual component of the same dual number types
-- collection at the scalar level (rank 0), which also implies the underlying
-- scalar type is the same. Additionally, the primal component
-- corresponding to the first type is required to satisfy constraint @Num@.
type IsDualWithScalar a r = (IsDual a, ScalarOf a ~ Primal r, Num (Primal a))

type IsDualWithScalarVar a r = (IsDualVar a, ScalarOf a ~ Primal r, Num (Primal a))

-- | A mega-shorthand for a bundle of connected type constraints.
-- The @Scalar@ in the name means that this type is a dual component
-- of a dual number type at the scalar (rank 0) level.
-- A more precise name would be @IsRank0DualWithAWellBehavedSetOfAllRanks@.
type IsScalar r =
       ( HasRanks r, Ord (Primal r), Numeric (Primal r), RealFloat (Primal r)
       , IsDualWithScalar r r, IsDualWithScalar (Tensor1 r) r
       , IsDualWithScalar (Tensor2 r) r, IsDualWithScalar (TensorX r) r
       , Primal (Tensor1 r) ~ Vector (Primal r)
       , Primal (Tensor2 r) ~ Matrix (Primal r)
       , Primal (TensorX r) ~ OT.Array (Primal r)
       -- This fragment is for @TensorS@ and it's irregular, because we can't
       -- mention @sh@ and so fully apply @TensorS@.
       , IsDualS (TensorS r), ScalarOfS (TensorS r) ~ Primal r
-- If we haven't inlined away @PrimalS@, we'd need this type equality,
-- which appears to work fine (but involves the @RevArray@ newtype wrapper).
--       , PrimalS (TensorS r) ~ RevArray (Primal r)
       )

type IsScalarVar r =
       ( HasRanks r, Ord (Primal r), Numeric (Primal r), RealFloat (Primal r)
       , IsDualWithScalarVar r r, IsDualWithScalarVar (Tensor1 r) r
       , IsDualWithScalarVar (Tensor2 r) r, IsDualWithScalarVar (TensorX r) r
       , Primal (Tensor1 r) ~ Vector (Primal r)
       , Primal (Tensor2 r) ~ Matrix (Primal r)
       , Primal (TensorX r) ~ OT.Array (Primal r)
       -- This fragment is for @TensorS@ and it's irregular, because we can't
       -- mention @sh@ and so fully apply @TensorS@.
       , IsDualSVar (TensorS r), ScalarOfS (TensorS r) ~ Primal r
-- If we haven't inlined away @PrimalS@, we'd need this type equality,
-- which appears to work fine (but involves the @RevArray@ newtype wrapper).
--       , PrimalS (TensorS r) ~ RevArray (Primal r)
       )

-- | A constraint expressing that dual numbers with this dual component
-- are implemented via gathering delta expressions in state.
type HasDelta r = (IsScalar r, r ~ Delta0 (Primal r))

-- | A constraint expressing that dual numbers with this dual component
-- are implemented via computing forward derivative on the spot.
type HasForward r = ( IsScalar r, r ~ ScalarOf r, Tensor1 r ~ Vector r
                    , Tensor2 r ~ Matrix r, TensorX r ~ OT.Array r )


-- * Class definitions

-- | Each shape of containers of parameters (a tensor of particular rank)
-- has its own collection of vector-space-like operations that are
-- a crucial part of the machinery for computing gradients or derivatives
-- of objective functions defined on dual numbers.
--
-- The chosen representation makes the dual component of dual numbers
-- the argument of the class and the primal component the result
-- of the associated type synonym family @Primal@. A disadvantage
-- of this approach is that the @Primal@ type family is not injective
-- because it has the same value, say @Double@, in the instance
-- @Delta0 Double@ for computing gradients via delta-expressions
-- and in the instance @Double@ for computing forward derivatives on the spot.
-- The lack of injectivity results in a lot of @AllowAmbiguousTypes@ pragmas
-- and type arguments to functions.
--
-- Another disadvantage is @UndecidableInstances@ pragmas,
-- e.g., due to @Illegal nested constraint ‘Ord (Primal r)’@.
-- Yet another disadvantage is that once the gradient-based method
-- and an underlying scalar is chosen, a fully instantiated type
-- of a dual number function is peppered with @Delta0 Double@, etc.
-- This forces writing such function using spurious polymorphism,
-- with constraints that determine that the type is, in fact, monomorphic.
-- E.g., @(HasDelta r, Primal r ~ Double)@ constraint that permits
-- writing @r@ instead of @Delta0 Double@.
--
-- However, all this is better than the inverse problem, where the argument
-- of the class is the primal component and @Dual@ is an injective
-- associated type family. There, we'd need two different instances
-- for @Double@ to cover both gradients and forward derivatives.
-- This could be done via a newtype, which would incur some notational overhead
-- and the need to define many instances for the newtype, e.g., all hmatrix
-- instances, which requires fragile code based on hmatrix internal modules.
class IsDual a where
  type Primal a  -- can't be injective, because same for gradient and derivative
  dZero :: a
  dScale :: Primal a -> a -> a
  dAdd :: a -> a -> a
  type ScalarOf a  -- verbose name to remember not to export from this module

class IsDual a => IsDualVar a where
  type DD a :: DeltaLevel
  dVar :: DeltaId (DD a) -> a
  bindInState :: a
              -> DeltaState (ScalarOf a)
              -> (DeltaState (ScalarOf a), DeltaId (DD a))

-- We had to inline @PrimalS@ in the signatures of the methods and everywhere
-- else in the code, because @~@ doesn't work on higher-rank types.
class IsDualS (t :: [Nat] -> Type) where
-- This is inlined away in order to avoid using the @RevArray@ newtype wrapper
-- that would be needed to partially apply @OS.Array@. Thanks to inlining
-- we can use @OS.Array@ below without the wrapper and not even
-- export @RevArray@, simplifying the API of this module.
--   type PrimalS t :: [Nat] -> Type
  dZeroS :: forall sh. OS.Shape sh => t sh
  dScaleS :: forall sh. OS.Shape sh => OS.Array sh (ScalarOfS t) -> t sh -> t sh
  dAddS :: forall sh. OS.Shape sh => t sh -> t sh -> t sh
  type ScalarOfS t :: Type

class IsDualS (t :: [Nat] -> Type) => IsDualSVar t where
  dVarS :: forall sh. OS.Shape sh => DeltaId 'DX -> t sh

-- This type family needs to be closed and injective or else GHC complains
-- when using the instance below (how bad things go depends on GHC version).
type family TensorS r = (result :: [Nat] -> Type) | result -> r where
  TensorS (Delta0 r) = DeltaS r
  TensorS Double = RevArray Double
  TensorS Float = RevArray Float

-- This instance saves us from splitting @DualNumber@ and @DualNumberS@,
-- @scale@ and @scaleS@, etc., despite inlining @PrimalS@ (but not @Primal@).
instance (IsDualS t, OS.Shape sh) => IsDual (t sh) where
  type Primal (t sh) = OS.Array sh (ScalarOfS t)
  dZero = dZeroS
  dScale = dScaleS
  dAdd = dAddS
  type ScalarOf (t sh) = ScalarOfS t

instance OS.Shape sh => IsDualVar (DeltaS r sh) where
  type DD (DeltaS r sh) = 'DX
  dVar = dVarS
  {-# INLINE bindInState #-}
  bindInState u' = bindInStateX (FromSX u')

-- | An instance of the class is a type of rank 0 (scalar rank) dual components
-- of dual numbers. The associated type synonym families are dual component
-- counterparts at the remaining ranks, with the same underlying scalar.
-- The operations relate the dual and primal component at various ranks.
-- Not many of these properties are enforced by the definition of the class
-- itself, but together with the 'IsScalar' constraint, a lot is captured.
class HasRanks r where
  type Tensor1 r = result | result -> r
  type Tensor2 r = result | result -> r
  type TensorX r = result | result -> r

  delta0Others :: Delta0Others (Primal (Tensor1 r)) (Tensor1 r) (TensorX r) (TensorS r '[]) -> r
  delta1Others ::
    Delta1Others (Primal (Tensor2 r)) (Primal (Tensor1 r)) r (Tensor1 r) (Tensor2 r) (TensorX r)
    -> Tensor1 r
  delta2Others :: Delta2Others (Primal (Tensor2 r)) r (Tensor1 r) (Tensor2 r) (TensorX r) -> Tensor2 r
  deltaXOthers :: DeltaXOthers r (Tensor1 r) (Tensor2 r) (TensorX r) -> TensorX r

  dSumElements0 :: Tensor1 r -> Int -> r
  dSumElements0 = \x y -> delta0Others (SumElements0 x y)

  dIndex0 :: Tensor1 r -> Int -> Int -> r
  dIndex0 = \x y z -> delta0Others (Index0 x y z)

  dDot0 :: Primal (Tensor1 r) -> Tensor1 r -> r
  dDot0 = \x y -> delta0Others (Dot0 x y)

  dFromX0 :: TensorX r -> r
  dFromX0 = \x -> delta0Others (FromX0 x)

  dFromS0 :: TensorS r '[] -> r
  dFromS0 = \x -> delta0Others (FromS0 x)

  dSeq1 :: Data.Vector.Vector r -> Tensor1 r
  dSeq1 = \x -> delta1Others (Seq1 x)

  dKonst1 :: r -> Int -> Tensor1 r
  dKonst1 = \x y -> delta1Others (Konst1 x y)

  dAppend1 :: Tensor1 r -> Int -> Tensor1 r -> Tensor1 r
  dAppend1 x y z = delta1Others (Append1 x y z)

  dSlice1 :: Int -> Int -> Tensor1 r -> Int -> Tensor1 r
  dSlice1 w x y z = delta1Others (Slice1 w x y z)

  dSumRows1 :: Tensor2 r -> Int -> Tensor1 r
  dSumRows1 x y = delta1Others (SumRows1 x y)

  dSumColumns1 :: Tensor2 r -> Int -> Tensor1 r
  dSumColumns1 x y = delta1Others (SumColumns1 x y)

  dM_VD1 :: Primal (Tensor2 r) -> Tensor1 r -> Tensor1 r
  dM_VD1 x y = delta1Others (M_VD1 x y)

  dMD_V1 :: Tensor2 r -> Primal (Tensor1 r) -> Tensor1 r
  dMD_V1 x y = delta1Others (MD_V1 x y)

  dFromX1 :: TensorX r -> Tensor1 r
  dFromX1 t = delta1Others (FromX1 t)

  dReverse1 :: Tensor1 r -> Tensor1 r
  dReverse1 t = delta1Others (Reverse1 t)

  dFlatten1 :: Int -> Int -> Tensor2 r -> Tensor1 r
  dFlatten1 x y z = delta1Others (Flatten1 x y z)

  dFlattenX1 :: OT.ShapeL -> TensorX r -> Tensor1 r
  dFlattenX1 x y = delta1Others (FlattenX1 x y)

  dFromRows2 :: Data.Vector.Vector (Tensor1 r) -> Tensor2 r
  dFromRows2 t = delta2Others (FromRows2 t)

  dFromColumns2 :: Data.Vector.Vector (Tensor1 r) -> Tensor2 r
  dFromColumns2 t = delta2Others (FromColumns2 t)

  dKonst2 :: r -> (Int, Int) -> Tensor2 r
  dKonst2 x y = delta2Others (Konst2 x y)

  dTranspose2 :: Tensor2 r -> Tensor2 r
  dTranspose2 t = delta2Others (Transpose2 t)

  dM_MD2 :: Primal (Tensor2 r) -> Tensor2 r -> Tensor2 r
  dM_MD2 x y = delta2Others (M_MD2 x y)

  dMD_M2 :: Tensor2 r -> Primal (Tensor2 r) -> Tensor2 r
  dMD_M2 x y = delta2Others (MD_M2 x y)

  dRowAppend2 :: Tensor2 r -> Int -> Tensor2 r -> Tensor2 r
  dRowAppend2 x y z = delta2Others (RowAppend2 x y z)

  dColumnAppend2 :: Tensor2 r -> Int -> Tensor2 r -> Tensor2 r
  dColumnAppend2 x y z = delta2Others (ColumnAppend2 x y z)

  dRowSlice2 :: Int -> Int -> Tensor2 r -> Int -> Tensor2 r
  dRowSlice2 w x y z = delta2Others (RowSlice2 w x y z)

  dColumnSlice2 :: Int -> Int -> Tensor2 r -> Int -> Tensor2 r
  dColumnSlice2 w x y z = delta2Others (ColumnSlice2 w x y z)

  dAsRow2 :: Tensor1 r -> Tensor2 r
  dAsRow2 t = delta2Others (AsRow2 t)

  dAsColumn2 :: Tensor1 r -> Tensor2 r
  dAsColumn2 t = delta2Others (AsColumn2 t)

  dFromX2 :: TensorX r -> Tensor2 r
  dFromX2 t = delta2Others (FromX2 t)

  dFlipud2 :: Tensor2 r -> Tensor2 r
  dFlipud2 t = delta2Others (Flipud2 t)

  dFliprl2 :: Tensor2 r -> Tensor2 r
  dFliprl2 t = delta2Others (Fliprl2 t)

  dReshape2 :: Int -> Tensor1 r -> Tensor2 r
  dReshape2 x y = delta2Others (Reshape2 x y)

  dConv2 :: Primal (Tensor2 r) -> Tensor2 r -> Tensor2 r
  dConv2 x y = delta2Others (Conv2 x y)

  dKonstX :: r -> OT.ShapeL -> TensorX r
  dKonstX x y = deltaXOthers (KonstX x y)

  dAppendX :: TensorX r -> Int -> TensorX r -> TensorX r
  dAppendX x y z = deltaXOthers (AppendX x y z)

  dSliceX :: Int -> Int -> TensorX r -> Int -> TensorX r
  dSliceX w x y z = deltaXOthers (SliceX w x y z)

  dIndexX :: TensorX r -> Int -> Int -> TensorX r
  dIndexX x y z = deltaXOthers (IndexX x y z)

  dRavelFromListX :: [TensorX r] -> TensorX r
  dRavelFromListX t = deltaXOthers (RavelFromListX t)

  dReshapeX :: OT.ShapeL -> OT.ShapeL -> TensorX r -> TensorX r
  dReshapeX x y z = deltaXOthers (ReshapeX x y z)

  dFrom0X :: r -> TensorX r
  dFrom0X t = deltaXOthers (From0X t)

  dFrom1X :: Tensor1 r -> TensorX r
  dFrom1X t = deltaXOthers (From1X t)

  dFrom2X :: Tensor2 r -> Int -> TensorX r
  dFrom2X t u = deltaXOthers (From2X t u)

  dFromS1 :: KnownNat len
          => TensorS r '[len] -> Tensor1 r

  dFlattenS1 :: OS.Shape sh
             => TensorS r sh -> Tensor1 r

  dFromS2 :: (KnownNat rows, KnownNat cols)
          => TensorS r '[rows, cols] -> Tensor2 r

  dFromSX :: OS.Shape sh
          => TensorS r sh -> TensorX r

  dKonstS :: OS.Shape sh
          => r -> TensorS r sh
  dAppendS :: (OS.Shape sh, KnownNat m, KnownNat n)
           => TensorS r (m ': sh) -> TensorS r (n ': sh)
           -> TensorS r ((m + n) ': sh)
  dSliceS :: (KnownNat i, KnownNat n, KnownNat k, OS.Shape rest)
          => Proxy i -> Proxy n -> TensorS r (i + n + k ': rest)
          -> TensorS r (n ': rest)
  dIndexS :: (KnownNat ix, KnownNat k, OS.Shape rest)
          => TensorS r (ix + 1 + k ': rest) -> Proxy ix -> TensorS r rest
  dRavelFromListS :: (KnownNat k, OS.Shape rest)
                  => [TensorS r rest] -> TensorS r (k : rest)
  dReshapeS :: (OS.Shape sh, OS.Shape sh', OS.Size sh ~ OS.Size sh')
            => TensorS r sh -> TensorS r sh'
  dFrom0S :: r -> TensorS r '[]
  dFrom1S :: KnownNat n => Tensor1 r -> TensorS r '[n]
  dFrom2S :: (KnownNat rows, KnownNat cols)
          => Proxy cols -> Tensor2 r -> TensorS r '[rows, cols]
  dFromXS :: OS.Shape sh => TensorX r -> TensorS r sh


-- * Backprop gradient method instances

instance IsDual (Delta0 r) where
  type Primal (Delta0 r) = r
  dZero = Zero0
  dScale = Scale0
  dAdd = Add0
  type ScalarOf (Delta0 r) = r

instance IsDualVar (Delta0 r) where
  type DD (Delta0 r) = 'D0
  dVar = Var0
  {-# INLINE bindInState #-}
  bindInState = bindInState0

instance HasRanks (Delta0 r) where
  type Tensor1 (Delta0 r) = Delta1 r
  type Tensor2 (Delta0 r) = Delta2 r
  type TensorX (Delta0 r) = DeltaX r

  delta0Others = Delta0Others
  delta1Others = Delta1Others
  delta2Others = Delta2Others
  deltaXOthers = DeltaXOthers

  dFromS1 = FromS1
  dFlattenS1 = FlattenS1
  dFromS2 = FromS2

  dFromSX = FromSX
  dKonstS = KonstS
  dAppendS = AppendS
  dSliceS = SliceS
  dIndexS = IndexS
  dRavelFromListS = RavelFromListS
  dReshapeS = ReshapeS
  dFrom0S = From0S
  dFrom1S = From1S
  dFrom2S = From2S
  dFromXS = FromXS

instance IsDual (Delta1 r) where
  type Primal (Delta1 r) = Vector r
  dZero = Zero1
  dScale = Scale1
  dAdd = Add1
  type ScalarOf (Delta1 r) = r

instance IsDualVar (Delta1 r) where
  type DD (Delta1 r) = 'D1
  dVar = Var1
  {-# INLINE bindInState #-}
  bindInState = bindInState1

instance IsDual (Delta2 r) where
  type Primal (Delta2 r) = Matrix r
  dZero = Zero2
  dScale = Scale2
  dAdd = Add2
  type ScalarOf (Delta2 r) = r

instance IsDualVar (Delta2 r) where
  type DD (Delta2 r) = 'D2
  dVar = Var2
  {-# INLINE bindInState #-}
  bindInState = bindInState2

instance IsDual (DeltaX r) where
  type Primal (DeltaX r) = OT.Array r
  dZero = ZeroX
  dScale = ScaleX
  dAdd = AddX
  type ScalarOf (DeltaX r) = r

instance IsDualVar (DeltaX r) where
  type DD (DeltaX r) = 'DX
  dVar = VarX
  {-# INLINE bindInState #-}
  bindInState = bindInStateX

instance IsDualS (DeltaS r) where
  dZeroS = ZeroS
  dScaleS = ScaleS
  dAddS = AddS
  type ScalarOfS (DeltaS r) = r

instance IsDualSVar (DeltaS r) where
  dVarS = VarS


-- * Alternative instances: forward derivatives computed on the spot

instance IsDual Double where
  type Primal Double = Double
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  type ScalarOf Double = Double

instance IsDual Float where
  type Primal Float = Float
  dZero = 0
  dScale k d = k * d
  dAdd d e = d + e
  type ScalarOf Float = Float

-- These constraints force @UndecidableInstances@.
instance Num (Vector r) => IsDual (Vector r) where
  type Primal (Vector r) = Vector r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  type ScalarOf (Vector r) = r

instance Num (Matrix r) => IsDual (Matrix r) where
  type Primal (Matrix r) = Matrix r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  type ScalarOf (Matrix r) = r

instance Num (OT.Array r) => IsDual (OT.Array r) where
  type Primal (OT.Array r) = OT.Array r
  dZero = 0
  dScale k d = k * d
  dAdd = (+)
  type ScalarOf (OT.Array r) = r

-- Due to this definition, which is necessary to partially apply @OS.Array@
-- to the @r@ argument, we need a lot of coercions in the code below
-- (but not anywhere else, I hope?).
newtype RevArray r sh = RevArray {unRevArray :: OS.Array sh r}

instance (forall sh. OS.Shape sh => Num (OS.Array sh r))
         => IsDualS (RevArray r) where
  dZeroS = RevArray 0
  dScaleS k d = RevArray $ k * unRevArray d
  dAddS d e = RevArray $ unRevArray d + unRevArray e
  type ScalarOfS (RevArray r) = r

instance HasRanks Double where
  type Tensor1 Double = Vector Double
  type Tensor2 Double = Matrix Double
  type TensorX Double = OT.Array Double

  delta0Others = delta0OthersNumeric
  delta1Others = delta1OthersNumeric
  delta2Others = delta2OthersNumeric
  deltaXOthers = deltaXOthersNumeric

  dFromS1 = OS.toVector . unRevArray
  dFlattenS1 = OS.toVector . unRevArray
  dFromS2 d = case OS.shapeL $ unRevArray d of
    [_rows, cols] -> HM.reshape cols $ OS.toVector $ unRevArray d
    _ -> error "dFromS2: wrong tensor dimensions"

  dFromSX = Data.Array.Convert.convert . unRevArray
  dKonstS = RevArray . OS.constant
  dAppendS d e = RevArray $ OS.append (unRevArray d) (unRevArray e)
  dSliceS (_ :: Proxy i) (_ :: Proxy n) =
    RevArray . OS.slice @'[ '(i, n) ] . unRevArray
  dIndexS d proxyIx = RevArray
                      $ OS.index (unRevArray d) (fromInteger $ natVal proxyIx)
  dRavelFromListS = RevArray . OS.ravel . OSB.fromList . map unRevArray
  dReshapeS = RevArray . OS.reshape . unRevArray
  dFrom0S = RevArray . OS.scalar
  dFrom1S = RevArray . OS.fromVector
  dFrom2S _ = RevArray . OS.fromVector . HM.flatten
  dFromXS = RevArray . Data.Array.Convert.convert

delta0OthersNumeric :: Numeric a
                     => Delta0Others (Vector a) (Vector a) (OT.Array a) (RevArray a '[])
                     -> a
delta0OthersNumeric = \case
    SumElements0 vd _ -> HM.sumElements vd
    Index0 d ix _ -> d V.! ix
    Dot0 x y -> x HM.<.> y
    FromX0 x -> OT.unScalar x
    FromS0 x -> OS.unScalar (unRevArray x)

delta1OthersNumeric :: Numeric a
                    => Delta1Others (Matrix a) (Vector a) a (Vector a) (Matrix a) (OT.Array a)
                    -> Vector a
delta1OthersNumeric = \case
  Seq1 v -> V.convert v
  Konst1 v i -> HM.konst v i
  Append1 d _k e -> d V.++ e
  Slice1 i n d _len -> V.slice i n d
  M_VD1 x y -> (HM.#>) x y
  MD_V1 x y -> (HM.#>) x y
  SumRows1 dm _cols -> V.fromList $ map HM.sumElements $ HM.toRows dm
  SumColumns1 dm _rows -> V.fromList $ map HM.sumElements $ HM.toColumns dm
  FromX1 x -> OT.toVector x
  Reverse1 x -> V.reverse x
  Flatten1 _rows _cols i -> HM.flatten i
  FlattenX1 _sh a -> OT.toVector a

delta2OthersNumeric :: (Numeric a, Num (Vector a))
                    => Delta2Others (Matrix a) a (Vector a) (Matrix a) (OT.Array a)
                    -> Matrix a
delta2OthersNumeric = \case
  FromRows2 x -> HM.fromRows . V.toList $ x
  FromColumns2 x -> HM.fromColumns . V.toList $ x
  Konst2 x y -> HM.konst x y
  Transpose2 x -> HM.tr' x
  M_MD2 x y -> (HM.<>) x y
  MD_M2 x y -> (HM.<>) x y
  AsRow2 x -> HM.asRow x
  AsColumn2 x -> HM.asColumn x
  RowAppend2 d _k e -> d HM.=== e
  ColumnAppend2 d _k e -> d HM.||| e
  RowSlice2 i n d _rows -> HM.takeRows n $ HM.dropRows i d
  ColumnSlice2 i n d _cols -> HM.takeColumns n $ HM.dropColumns i d
  FromX2 d -> case OT.shapeL d of
   [_rows, cols] -> HM.reshape cols $ OT.toVector d
   _ -> error "dFromX2: wrong tensor dimensions"
  Flipud2 x -> HM.flipud x
  Fliprl2 x -> HM.fliprl x
  Reshape2 x y -> HM.reshape x y
  Conv2 x y -> HM.conv2 x y

deltaXOthersNumeric :: HM.Element a
                    => DeltaXOthers a (Vector a) (Matrix a) (OT.Array a) -> OT.Array a
deltaXOthersNumeric = \case
  KonstX d sz -> OT.constant sz d
  AppendX d _k e -> d `OT.append` e
  SliceX i n d _len -> OT.slice [(i, n)] d
  IndexX d ix _len -> OT.index d ix
  RavelFromListX ld ->
   let sh = case ld of
         d : _ -> length ld : OT.shapeL d
         [] -> []
   in OT.ravel $ OTB.fromList sh ld
  ReshapeX _sh sh' d -> OT.reshape sh' d
  From0X x -> OT.scalar x
  From1X d -> OT.fromVector [V.length d] d
  From2X d cols -> OT.fromVector [HM.rows d, cols] $ HM.flatten d

instance HasRanks Float where
  type Tensor1 Float = Vector Float
  type Tensor2 Float = Matrix Float
  type TensorX Float = OT.Array Float

  delta0Others = delta0OthersNumeric
  delta1Others = delta1OthersNumeric
  delta2Others = delta2OthersNumeric
  deltaXOthers = deltaXOthersNumeric

  -- Below it's completely repeated after the @Double@ case.
  dFromS1 = OS.toVector . unRevArray
  dFlattenS1 = OS.toVector . unRevArray
  dFromS2 d = case OS.shapeL $ unRevArray d of
    [_rows, cols] -> HM.reshape cols $ OS.toVector $ unRevArray d
    _ -> error "dFromS2: wrong tensor dimensions"
  dFromSX = Data.Array.Convert.convert . unRevArray
  dKonstS = RevArray . OS.constant
  dAppendS d e = RevArray $ OS.append (unRevArray d) (unRevArray e)
  dSliceS (_ :: Proxy i) (_ :: Proxy n) =
    RevArray . OS.slice @'[ '(i, n) ] . unRevArray
  dIndexS d proxyIx = RevArray
                      $ OS.index (unRevArray d) (fromInteger $ natVal proxyIx)
  dRavelFromListS = RevArray . OS.ravel . OSB.fromList . map unRevArray
  dReshapeS = RevArray . OS.reshape . unRevArray
  dFrom0S = RevArray . OS.scalar
  dFrom1S = RevArray . OS.fromVector
  dFrom2S _ = RevArray . OS.fromVector . HM.flatten
  dFromXS = RevArray . Data.Array.Convert.convert
