{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | This is an adaptor from user-defined objective functions
-- with complicated domains to the restricted from of functions
-- that the AD machinery can efficiently differentiate.
module HordeAd.External.Adaptor
  ( AdaptableDomains(Scalar, Value, toDomains, nParams, nScalars)
  , AdaptableInputs
  , RandomDomains(randomVals)
  , parseDomains, parseADInputs
  , revL, revDtMaybeL, revDtFun, rev, revDt
  , srevL, srevDtMaybeL, srev, srevDt
  , crev, crevDt, fwd
  ) where

import Prelude

import           Control.Arrow ((&&&))
import           Control.Exception (assert)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Functor.Compose
import           Data.List (foldl')
import qualified Data.Strict.Vector as Data.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstInterpret
import HordeAd.Core.AstSimplify
import HordeAd.Core.Delta (DeltaR, ForwardDerivative)
import HordeAd.Core.Domains
import HordeAd.Core.DualClass (dFromVectorR, dScalarR)
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorADVal
import HordeAd.Core.TensorClass

-- These only work with non-scalar codomain. A fully general version
-- is possible, but the user has to write many more type applications.
revL
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> [vals] -> [vals]
revL f valsAll = revDtMaybeL f valsAll Nothing

revDtMaybeL
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> [vals] -> Maybe (TensorOf n r) -> [vals]
revDtMaybeL _ [] _ = []
revDtMaybeL f valsAll@(vals : _) dt =
  let asts4 = fst $ revDtFun f vals
      h val = parseDomains val $ fst
              $ revAstOnDomainsEval asts4 (toDomains val) dt
  in map h valsAll

revDtFun
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> vals
  -> (ADAstArtifact6 n r, DeltaR n (Ast0 r))
{-# INLINE revDtFun #-}
revDtFun f vals =
  let parameters0 = toDomains vals
      dim0 = tlength $ domains0 parameters0
      shapes1 = map dshape $ V.toList $ domainsR parameters0
  in revAstOnDomainsFun dim0 shapes1 (revDtInterpret vals f)

revDtInterpret
  :: forall r n vals astvals.
     ( InterpretAst r, KnownNat n, ScalarOf r ~ r, Floating (Vector r)
     , RealFloat r, AdaptableDomains astvals
     , vals ~ Value astvals, Scalar astvals ~ Ast0 r )
  => vals -> (astvals -> Ast n r)
  -> Domains (ADVal (Ast0 r)) -> Domains (Ast0 r)
  -> (ADAstVarNames n r, ADAstVars n r)
  -> Compose ADVal (AstRanked r) n
{-# INLINE revDtInterpret #-}
revDtInterpret vals f varInputs domains ((var0, _, vars1), (ast0, _, _)) =
  let ast = f $ parseDomains vals domains
      d0 = dD emptyADShare
              ast0
              (dFromVectorR $ V.map dScalarR $ inputDual0 varInputs)
      env0 = extendEnvR var0 (Compose d0) EM.empty
      env1 = foldr extendEnvD env0
             $ zip vars1 $ V.toList
             $ V.zipWith (dDnotShared emptyADShare)
                         (inputPrimal1 varInputs)
                         (inputDual1 varInputs)
  in snd $ interpretAst env1 emptyMemo ast

rev
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> vals -> vals
rev f vals = head $ revL f [vals]

-- This version additionally takes the sensitivity parameter.
revDt
  :: forall r n vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast n r) -> vals -> TensorOf n r -> vals
revDt f vals dt = head $ revDtMaybeL f [vals] (Just dt)

-- Versions that work with scalar codomain.
srevL
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> [vals] -> [vals]
srevL f = revL (tscalar . f)

srevDtMaybeL
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> [vals] -> Maybe r -> [vals]
srevDtMaybeL _ [] _ = []
srevDtMaybeL f valsAll dt = revDtMaybeL (tscalar . f) valsAll (tscalar <$> dt)

srev
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> vals -> vals
srev f = rev (tscalar . f)

-- This version additionally takes the sensitivity parameter.
srevDt
  :: forall r vals astvals.
     ( ADTensor r, InterpretAst r, DomainsTensor r, ScalarOf r ~ r
     , Floating (Vector r), RealFloat r
     , AdaptableDomains astvals, AdaptableDomains vals
     , Domains r ~ Data.Vector.Vector (DTensorOf r)
     , r ~ Scalar vals, vals ~ Value vals, vals ~ Value astvals
     , Scalar astvals ~ Ast0 r )
  => (astvals -> Ast0 r) -> vals -> r -> vals
srevDt f vals dt = revDt (tscalar . f) vals (tscalar dt)

-- Old version of the three functions, with constant, fixed inputs and dt.
crev :: forall n r vals advals.
       ( r ~ Scalar vals, vals ~ Value advals
       , ADTensor r, DynamicTensor r, DomainsTensor r
       , IsPrimal (Flip OR.Array r n)
       , AdaptableDomains (Value advals)
       , AdaptableInputs advals, Scalar advals ~ r
       , Domains r ~ Data.Vector.Vector (DTensorOf r)
       , IsPrimal r, DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
       , vals ~ Value vals, DomainsOf r ~ Domains r )
    => (advals -> Compose ADVal (Flip OR.Array r) n) -> vals
    -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
crevDt :: forall n r vals advals.
         ( r ~ Scalar vals, vals ~ Value advals
         , ADTensor r, DynamicTensor r, DomainsTensor r
         , IsPrimal (Flip OR.Array r n)
         , AdaptableDomains (Value advals)
         , AdaptableInputs advals, Scalar advals ~ r
         , Domains r ~ Data.Vector.Vector (DTensorOf r)
         , IsPrimal r, DTensorOf (ADVal r) ~ ADVal (DTensorOf r)
         , vals ~ Value vals, DomainsOf r ~ Domains r )
      => (advals -> Compose ADVal (Flip OR.Array r) n) -> vals -> OR.Array n r
      -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe
  :: forall n vals r advals.
     ( r ~ Scalar vals, vals ~ Value vals, vals ~ Value advals
     , ADTensor r, DynamicTensor r, DomainsTensor r
     , IsPrimal (Flip OR.Array r n)
     , AdaptableDomains (Value advals)
     , AdaptableInputs advals, Scalar advals ~ r
     , DomainsOf r ~ Domains r, Domains r ~ Data.Vector.Vector (DTensorOf r)
     , IsPrimal r, DTensorOf (ADVal r) ~ ADVal (DTensorOf r) )
  => (advals -> Compose ADVal (Flip OR.Array r) n)
  -> vals -> Maybe (OR.Array n r)
  -> vals
crevDtMaybe f vals dt =
  let g inputs = getCompose $ f $ parseADInputs vals inputs
  in parseDomains vals $ fst $ revOnDomains (Flip <$> dt) g (toDomains vals)

-- This takes the sensitivity parameter, by convention.
fwd :: forall a vals r advals.
       ( ForwardDerivative a, r ~ Scalar vals, vals ~ Value advals
       , ADTensor r, DynamicTensor r, DomainsTensor r, IsPrimalWithScalar a r
       , AdaptableDomains (Value advals), Scalar advals ~ r
       , AdaptableInputs advals, Domains r ~ Data.Vector.Vector (DTensorOf r)
       , IsPrimal r, DTensorOf (ADVal r) ~ ADVal (DTensorOf r) )
    => (advals -> ADVal a) -> vals -> vals
    -> a
fwd f x ds =
  let g inputs = f $ parseADInputs ds inputs
  in fst $ slowFwdOnDomains (toDomains x) g (toDomains ds)

class AdaptableDomains vals where
  type Scalar vals
  type Value vals
  toDomains :: vals -> Domains (Scalar vals)
  fromDomains :: Value vals -> Domains (Scalar vals)
              -> (vals, Domains (Scalar vals))
  nParams :: vals -> Int
  nScalars :: vals -> Int

class RandomDomains vals where
  randomVals
    :: forall r g.
       ( RandomGen g
       , r ~ Scalar vals, Numeric r, Fractional r, Random r, Num (Vector r) )
    => r -> g -> (vals, g)

class AdaptableInputs advals where
  fromADInputs :: Value advals -> Domains (ADVal (Scalar advals))
               -> (advals, Domains (ADVal (Scalar advals)))

parseDomains
  :: ( AdaptableDomains vals, Tensor (Scalar vals)
     , DomainsCollection (Scalar vals) )
  => Value vals -> Domains (Scalar vals) -> vals
parseDomains aInit domains =
  let (vals, rest) = fromDomains aInit domains
  in assert (isEmptyDoms rest) vals

parseADInputs :: ( AdaptableInputs advals, Tensor r, DynamicTensor r
                 , r ~ Scalar advals, DomainsCollection r
                 , Domains r ~ Data.Vector.Vector (DTensorOf r)
                 , IsPrimal r, DTensorOf (ADVal r) ~ ADVal (DTensorOf r) )
              => Value advals -> Domains (ADVal r)
              -> advals
parseADInputs aInit inputs =
  let (advals, rest) = fromADInputs aInit inputs
  in assert (isEmptyDoms rest) advals

instance AdaptableDomains Double where
  type Scalar Double = Double
  type Value Double = Double
  toDomains a = mkDomains (tfromList [tscalar a]) V.empty
  fromDomains _aInit params = case uncons0 params of
    Just (a, rest) -> (a, rest)
    Nothing -> error "fromDomains in AdaptableDomains Double"
  nParams _ = 1
  nScalars _ = 1

instance RandomDomains Double where
  randomVals range = randomR (- range, range)
    -- note that unlike in hmatrix the range is closed from the top

instance AdaptableDomains (ADVal Double) where
  type Scalar (ADVal Double) = Double
  type Value (ADVal Double) = Double
  toDomains = undefined
  fromDomains = undefined
  nParams = undefined
  nScalars = undefined

instance AdaptableInputs (ADVal Double) where
  fromADInputs _aInit inputs = case uncons0 inputs of
    Just (a, rest) -> (a, rest)
    Nothing -> error "fromADInputs in AdaptableInputs (ADVal Double)"

instance AdaptableDomains Float where
  type Scalar Float = Float
  type Value Float = Float
  toDomains a = mkDomains (tfromList [tscalar a]) V.empty
  fromDomains _aInit params = case uncons0 params of
    Just (a, rest) -> (a, rest)
    Nothing -> error "fromDomains in AdaptableDomains Float"
  nParams _ = 1
  nScalars _ = 1

instance RandomDomains Float where
  randomVals range = randomR (- range, range)

instance AdaptableDomains (ADVal Float) where
  type Scalar (ADVal Float) = Float
  type Value (ADVal Float) = Float
  toDomains = undefined
  fromDomains = undefined
  nParams = undefined
  nScalars = undefined

instance AdaptableInputs (ADVal Float) where
  fromADInputs _aInit inputs = case uncons0 inputs of
    Just (a, rest) -> (a, rest)
    Nothing -> error "fromADInputs in AdaptableInputs (ADVal Float)"

instance AdaptableDomains (ADVal (Ast0 r)) where
  type Scalar (ADVal (Ast0 r)) = Ast0 r
  type Value (ADVal (Ast0 r)) = r
  toDomains = undefined
  fromDomains = undefined
  nParams = undefined
  nScalars = undefined

instance ShowAstSimplify r
         => AdaptableInputs (ADVal (Ast0 r)) where
  fromADInputs _aInit inputs = case uncons0 inputs of
    Just (a, rest) -> (a, rest)
    Nothing -> error "fromADInputs in AdaptableInputs (ADVal (Ast0 r))"

instance (Scalar r ~ r, ShowAstSimplify r)
         => AdaptableDomains (Ast0 r) where
  type Scalar (Ast0 r) = Ast0 r
  type Value (Ast0 r) = r
  toDomains = undefined
  fromDomains _aInit params = case uncons0 params of
    Just (a, rest) -> (a, rest)
    Nothing -> error "fromDomains in AdaptableDomains (Ast0 r)"
  nParams = undefined
  nScalars = undefined

{- TODO: requires IncoherentInstances no matter what pragma I stick in
-- A special case, because for @Double@ we have faster @randomVals@,
-- though the quality of randomness is worse (going through a single @Int@).
instance {-# OVERLAPS #-} {-# OVERLAPPING #-}
         KnownNat n
         => AdaptableDomains (OR.Array n Double) where
  type Scalar (OR.Array n Double) = Double
  toDomains a =
    (V.empty, V.empty, V.empty, V.singleton (Data.Array.Convert.convert a))
  fromDomains _aInit (v0, v1) = case V.uncons v1 of
    Just (a, rest) -> (toShapedOrDummy a, (v0, v1, v2, rest))
    Nothing -> error "fromDomains in AdaptableDomains (OR.Array n r)"
  randomVals range g =
    let -- Note that hmatrix produces numbers from the range open at the top,
        -- unlike package random.
        createRandomVector n seedInt =
          LA.scale (2 * range)
          $ LA.randomVector seedInt LA.Uniform n - LA.scalar 0.5
        (i, g2) = random g
        arr = OR.fromVector $ createRandomVector (OR.sizeP (Proxy @n)) i
    in (arr, g2)
-}

instance ( Tensor r, ShowAstSimplify r, KnownNat n
         , TensorOf n r ~ Flip OR.Array r n )
         => AdaptableDomains (Ast n r) where
  type Scalar (Ast n r) = Ast0 r
  type Value (Ast n r) = OR.Array n r
  toDomains = undefined
  fromDomains aInit params = case unconsR params of
    Just (a, rest) -> (ttoRankedOrDummy (tshape $ Flip aInit) a, rest)
    Nothing -> error "fromDomains in AdaptableDomains (Ast n r)"
  nParams = undefined
  nScalars = undefined

ttoRankedOrDummy :: (Tensor r, DynamicTensor r, DomainsTensor r, KnownNat n)
                 => ShapeInt n -> DTensorOf r -> TensorOf n r
ttoRankedOrDummy sh x = if disDummy x
                        then tzero sh
                        else tfromD x

instance ( Numeric r, KnownNat n, Tensor r, DynamicTensor r, DomainsTensor r
         , Domains r ~ Data.Vector.Vector (DTensorOf r), DomainsCollection r
         , TensorOf n r ~ Flip OR.Array r n, DTensorOf r ~ OD.Array r )
         => AdaptableDomains (OR.Array n r) where
  type Scalar (OR.Array n r) = r
  type Value (OR.Array n r) = OR.Array n r
  toDomains a =
    mkDoms emptyDoms0 (V.singleton (Data.Array.Convert.convert a))
  fromDomains aInit params = case unconsR params of
    Just (a, rest) -> (runFlip $ ttoRankedOrDummy (tshape $ Flip aInit) a, rest)
    Nothing -> error "fromDomains in AdaptableDomains (OR.Array n r)"
  nParams _ = 1
  nScalars = OR.size

instance ( Numeric r, KnownNat n, Tensor r, DynamicTensor r, DomainsTensor r
         , Domains r ~ Data.Vector.Vector (DTensorOf r), DomainsCollection r
         , TensorOf n r ~ Flip OR.Array r n, DTensorOf r ~ OD.Array r )
         => AdaptableDomains (Flip OR.Array r n) where
  type Scalar (Flip OR.Array r n) = r
  type Value (Flip OR.Array r n) = OR.Array n r
  toDomains a =
    mkDoms emptyDoms0
              (V.singleton (Data.Array.Convert.convert $ runFlip a))
  fromDomains aInit params = case unconsR params of
    Just (a, rest) -> (ttoRankedOrDummy (tshape $ Flip aInit) a, rest)
    Nothing -> error "fromDomains in AdaptableDomains (Flip OR.Array r n)"
  nParams _ = 1
  nScalars = OR.size . runFlip

instance KnownNat n
         => RandomDomains (OR.Array n r) where
  randomVals range g =
    let createRandomVector n seed =
          LA.scale (2 * range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OR.fromVector undefined
              $ createRandomVector (OR.size undefined) g1  -- TODO
    in (arr, g2)

instance AdaptableDomains (ADVal (Flip OR.Array r n)) where
  type Scalar (ADVal (Flip OR.Array r n)) = r
  type Value (ADVal (Flip OR.Array r n)) = OR.Array n r
  toDomains = undefined
  fromDomains = undefined
  nParams = undefined
  nScalars = undefined

instance ( Tensor r, Tensor (ADVal r), IsPrimal r
         , KnownNat n, TensorOf n r ~ Flip OR.Array r n
         , TensorOf n (ADVal r) ~ Compose ADVal (Flip OR.Array r) n
         , DTensorOf r ~ OD.Array r
         , Domains r ~ Data.Vector.Vector (DTensorOf r)
         , DTensorOf (ADVal r) ~ ADVal (OD.Array r) )
         => AdaptableInputs (ADVal (Flip OR.Array r n)) where
  fromADInputs _aInit inputs = case unconsR inputs of
    Just (a, rest) -> (getCompose $ tfromD @(ADVal r) @n a, rest)
    Nothing -> error "fromADInputs in AdaptableInputs (ADVal (Flip OR.Array r n))"

instance AdaptableDomains (Compose ADVal (Flip OR.Array r) n) where
  type Scalar (Compose ADVal (Flip OR.Array r) n) = r
  type Value (Compose ADVal (Flip OR.Array r) n) = OR.Array n r
  toDomains = undefined
  fromDomains = undefined
  nParams = undefined
  nScalars = undefined

instance ( Tensor r, Tensor (ADVal r), IsPrimal r
         , KnownNat n, TensorOf n r ~ Flip OR.Array r n
         , TensorOf n (ADVal r) ~ Compose ADVal (Flip OR.Array r) n
         , DTensorOf r ~ OD.Array r
         , Domains r ~ Data.Vector.Vector (DTensorOf r)
         , DTensorOf (ADVal r) ~ ADVal (OD.Array r) )
         => AdaptableInputs (Compose ADVal (Flip OR.Array r) n) where
  fromADInputs _aInit inputs = case unconsR inputs of
    Just (a, rest) -> (tfromD @(ADVal r) @n a, rest)
    Nothing -> error "fromADInputs in AdaptableInputs (Compose ADVal (Flip OR.Array r) n)"

instance AdaptableDomains (ADVal (Ast n r)) where
  type Scalar (ADVal (Ast n r)) = Ast0 r
  type Value (ADVal (Ast n r)) = OR.Array n r
  toDomains = undefined
  fromDomains = undefined
  nParams = undefined
  nScalars = undefined

instance (KnownNat n, ShowAstSimplify r)
         => AdaptableInputs (ADVal (Ast n r)) where
  fromADInputs _aInit inputs = case unconsR inputs of
    Just (a, rest) -> (getCompose $ tfromD @(ADVal (Ast0 r)) @n a, rest)
    Nothing -> error "fromADInputs in AdaptableInputs (ADVal (Ast n r))"

instance ( AdaptableDomains a, Tensor (Scalar a), DynamicTensor (Scalar a)
         , DomainsCollection (Scalar a)
         , Domains (Scalar a) ~ Data.Vector.Vector (DTensorOf (Scalar a)) )
         => AdaptableDomains [a] where
  type Scalar [a] = Scalar a
  type Value [a] = [Value a]
  toDomains l =
    let (l0, l1) = unzip $ map ((domains0 &&& domainsR) . toDomains) l
    in mkDomains (tconcat l0) (V.concat l1)
  fromDomains lInit source =
    let f (lAcc, restAcc) aInit =
          let (a, rest) = fromDomains aInit restAcc
          in (a : lAcc, rest)
        (l, restAll) = foldl' f ([], source) lInit
    in (reverse l, restAll)
    -- is the following as performant? benchmark:
    -- > fromDomains lInit source =
    -- >   let f = swap . flip fromDomains
    -- >   in swap $ mapAccumL f source lInit
  nParams = sum . map nParams
  nScalars = sum . map nScalars

instance AdaptableInputs a
         => AdaptableInputs [a] where
  fromADInputs lInit source =
    let f (lAcc, restAcc) aInit =
          let (a, rest) = fromADInputs aInit restAcc
          in (a : lAcc, rest)
        (l, restAll) = foldl' f ([], source) lInit
    in (reverse l, restAll)

instance ( Tensor (Scalar a), DynamicTensor r, DomainsCollection r
         , r ~ Scalar a, r ~ Scalar b
         , Domains r ~ Data.Vector.Vector (DTensorOf r)
         , AdaptableDomains a
         , AdaptableDomains b ) => AdaptableDomains (a, b) where
  type Scalar (a, b) = Scalar a
  type Value (a, b) = (Value a, Value b)
  toDomains (a, b) =
    let (a0, a1) = domains0 &&& domainsR $ toDomains a
        (b0, b1) = domains0 &&& domainsR $ toDomains b
    in mkDomains (tconcat [a0, b0])
                 (V.concat [a1, b1])
  fromDomains (aInit, bInit) source =
    let (a, aRest) = fromDomains aInit source
        (b, bRest) = fromDomains bInit aRest
    in ((a, b), bRest)
  nParams (a, b) = nParams a + nParams b
  nScalars (a, b) = nScalars a + nScalars b

instance ( r ~ Scalar a, r ~ Scalar b
         , RandomDomains a
         , RandomDomains b ) => RandomDomains (a, b) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
    in ((v1, v2), g2)

instance ( Tensor (Scalar a), DynamicTensor r, DomainsCollection r
         , r ~ Scalar a, r ~ Scalar b, r ~ Scalar c
         , Domains r ~ Data.Vector.Vector (DTensorOf r)
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c ) => AdaptableDomains (a, b, c) where
  type Scalar (a, b, c) = Scalar a
  type Value (a, b, c) = (Value a, Value b, Value c)
  toDomains (a, b, c) =
    let (a0, a1) = domains0 &&& domainsR $ toDomains a
        (b0, b1) = domains0 &&& domainsR $ toDomains b
        (c0, c1) = domains0 &&& domainsR $ toDomains c
    in mkDomains (tconcat [a0, b0, c0])
                 (V.concat [a1, b1, c1])
  fromDomains (aInit, bInit, cInit) source =
    let (a, aRest) = fromDomains aInit source
        (b, bRest) = fromDomains bInit aRest
        (c, rest) = fromDomains cInit bRest
    in ((a, b, c), rest)
  nParams (a, b, c) = nParams a + nParams b + nParams c
  nScalars (a, b, c) = nScalars a + nScalars b + nScalars c

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c
         , RandomDomains a
         , RandomDomains b
         , RandomDomains c ) => RandomDomains (a, b, c) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
    in ((v1, v2, v3), g3)

instance ( Tensor (Scalar a), DynamicTensor r, DomainsCollection r
         , r ~ Scalar a, r ~ Scalar b, r ~ Scalar c, r ~ Scalar d
         , Domains r ~ Data.Vector.Vector (DTensorOf r)
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c
         , AdaptableDomains d ) => AdaptableDomains (a, b, c, d) where
  type Scalar (a, b, c, d) = Scalar a
  type Value (a, b, c, d) = (Value a, Value b, Value c, Value d)
  toDomains (a, b, c, d) =
    let (a0, a1) = domains0 &&& domainsR $ toDomains a
        (b0, b1) = domains0 &&& domainsR $ toDomains b
        (c0, c1) = domains0 &&& domainsR $ toDomains c
        (d0, d1) = domains0 &&& domainsR $ toDomains d
    in mkDomains (tconcat [a0, b0, c0, d0])
                 (V.concat [a1, b1, c1, d1])
  fromDomains (aInit, bInit, cInit, dInit) source =
    let (a, aRest) = fromDomains aInit source
        (b, bRest) = fromDomains bInit aRest
        (c, cRest) = fromDomains cInit bRest
        (d, rest) = fromDomains dInit cRest
    in ((a, b, c, d), rest)
  nParams (a, b, c, d) = nParams a + nParams b + nParams c + nParams d
  nScalars (a, b, c, d) = nScalars a + nScalars b + nScalars c + nScalars d

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c, r ~ Scalar d
         , RandomDomains a
         , RandomDomains b
         , RandomDomains c
         , RandomDomains d ) => RandomDomains (a, b, c, d) where
  randomVals range g =
    let (v1, g1) = randomVals range g
        (v2, g2) = randomVals range g1
        (v3, g3) = randomVals range g2
        (v4, g4) = randomVals range g3
    in ((v1, v2, v3, v4), g4)

instance (  r ~ Scalar a, r ~ Scalar b
         , AdaptableInputs a
         , AdaptableInputs b )
         => AdaptableInputs (a, b) where
  fromADInputs (aInit, bInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, rest) = fromADInputs bInit aRest
    in ((a, b), rest)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c
         , AdaptableInputs a
         , AdaptableInputs b
         , AdaptableInputs c )
         => AdaptableInputs (a, b, c) where
  fromADInputs (aInit, bInit, cInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, bRest) = fromADInputs bInit aRest
        (c, rest) = fromADInputs cInit bRest
    in ((a, b, c), rest)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c, r ~ Scalar d
         , AdaptableInputs a
         , AdaptableInputs b
         , AdaptableInputs c
         , AdaptableInputs d )
         => AdaptableInputs (a, b, c, d) where
  fromADInputs (aInit, bInit, cInit, dInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, bRest) = fromADInputs bInit aRest
        (c, cRest) = fromADInputs cInit bRest
        (dd, rest) = fromADInputs dInit cRest
    in ((a, b, c, dd), rest)

instance ( r ~ Scalar a, r ~ Scalar b
         , AdaptableDomains a, AdaptableDomains b )
         => AdaptableDomains (Either a b) where
  type Scalar (Either a b) = Scalar a
  type Value (Either a b) = Either (Value a) (Value b)
  toDomains e = case e of
    Left a -> toDomains a
    Right b -> toDomains b
  fromDomains eInit source = case eInit of
    Left a -> let (a2, rest) = fromDomains a source
              in (Left a2, rest)
    Right b -> let (b2, rest) = fromDomains b source
               in (Right b2, rest)
  nParams = either nParams nParams
  nScalars = either nScalars nScalars

instance ( r ~ Scalar a, r ~ Scalar b
         , Domains r ~ Data.Vector.Vector (DTensorOf r)
         , AdaptableInputs a, AdaptableInputs b)
         => AdaptableInputs (Either a b) where
  fromADInputs eInit source = case eInit of
    Left a -> let (a2, rest) = fromADInputs a source
              in (Left a2, rest)
    Right b -> let (b2, rest) = fromADInputs b source
               in (Right b2, rest)

instance ( AdaptableDomains a, DynamicTensor (Scalar a)
         , DomainsCollection (Scalar a)
         , Domains (Scalar a) ~ Data.Vector.Vector (DTensorOf (Scalar a)) )
         => AdaptableDomains (Maybe a) where
  type Scalar (Maybe a) = Scalar a
  type Value (Maybe a) = Maybe (Value a)
  toDomains e = case e of
    Nothing -> mkDoms emptyDoms0 V.empty
    Just a -> toDomains a
  fromDomains eInit source = case eInit of
    Nothing -> (Nothing, source)
    Just a -> let (a2, rest) = fromDomains a source
              in (Just a2, rest)
  nParams = maybe 0 nParams
  nScalars = maybe 0 nScalars

instance AdaptableInputs a
         => AdaptableInputs (Maybe a) where
  fromADInputs eInit source = case eInit of
    Nothing -> (Nothing, source)
    Just a -> let (a2, rest) = fromADInputs a source
              in (Just a2, rest)
