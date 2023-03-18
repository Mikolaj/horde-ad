{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module HordeAd.External.Adaptor
  ( Adaptable, Scalar
  , AdaptableDomains(toDomains, nParams, nScalars)
  , RandomDomains(randomVals)
  , AdaptableInputs(Value), parseDomains, parseADInputs
  , revL, rev, revDt, crev, crevDt
  ) where

import Prelude

import           Control.Exception (assert)
import qualified Data.Array.Convert
import qualified Data.Array.DynamicS as OT
import qualified Data.Array.RankedS as OR
import           Data.List (foldl')
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat)
import           Numeric.LinearAlgebra (Numeric, Vector)
import qualified Numeric.LinearAlgebra as LA
import           System.Random

import HordeAd.Core.ADValTensor
import HordeAd.Core.Ast
import HordeAd.Core.DualNumber
import HordeAd.Core.Engine
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass
import HordeAd.Internal.TensorOps

revL
  :: forall r n vals advals.
     ( Numeric r, Show r, Floating (Vector r)
     , KnownNat n, ScalarOf r ~ r, InterpretAst r
     , AdaptableInputs (Ast0 r) advals, AdaptableDomains vals
     , ADTensor r, r ~ Scalar vals, vals ~ Value advals )
  => (advals -> ADVal (Ast n r)) -> [vals] -> [vals]
revL _ [] = []
revL f vals@(val0 : _) =
  let g inputs = f $ parseADInputs val0 inputs
      parameters0 = toDomains val0
      dim0 = tlength $ domains0 parameters0
      shapes1 = map tshapeD $ V.toList $ domains1 parameters0
      gradientAst = revAstOnDomainsFun dim0 shapes1 g
      h val = parseDomains val0 $ fst
              $ revAstOnDomainsEval dim0 (length shapes1)
                                    gradientAst
                                    (toDomains val) Nothing
  in map h vals

rev
  :: forall r n vals advals.
     ( Numeric r, Show r, Floating (Vector r)
     , KnownNat n, ScalarOf r ~ r, InterpretAst r
     , AdaptableInputs (Ast0 r) advals, AdaptableDomains vals
     , ADTensor r, r ~ Scalar vals, vals ~ Value advals )
  => (advals -> ADVal (Ast n r)) -> vals -> vals
rev f vals = revDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
revDt
  :: forall r n vals advals.
     ( Numeric r, Show r, Floating (Vector r)
     , KnownNat n, ScalarOf r ~ r, InterpretAst r
     , AdaptableInputs (Ast0 r) advals, AdaptableDomains vals
     , ADTensor r, r ~ Scalar vals, vals ~ Value advals )
  => (advals -> ADVal (Ast n r)) -> vals -> TensorOf n r -> vals
revDt f vals dt = revDtMaybe f vals (Just dt)

revDtMaybe
  :: forall r n vals advals.
     ( ADTensor r, InterpretAst r, KnownNat n, ScalarOf r ~ r
     , Floating (Vector r), Show r, Numeric r
     , AdaptableInputs (Ast0 r) advals, AdaptableDomains vals
     , r ~ Scalar vals, vals ~ Value advals )
  => (advals -> ADVal (Ast n r)) -> vals -> Maybe (TensorOf n r) -> vals
revDtMaybe f vals dt =
  let g inputs = f $ parseADInputs vals inputs
  in parseDomains vals $ fst $ revAstOnDomains g (toDomains vals) dt

-- Old version of the three functions, with constant, fixed inputs and dt.
crev :: forall a vals r advals.
       ( r ~ Scalar vals, vals ~ Value advals
       , ADTensor r, IsPrimalWithScalar a r
       , Adaptable advals )
    => (advals -> ADVal a) -> vals
    -> vals
crev f vals = crevDtMaybe f vals Nothing

-- This version additionally takes the sensitivity parameter.
crevDt :: forall a vals r advals.
         ( r ~ Scalar vals, vals ~ Value advals
         , ADTensor r, IsPrimalWithScalar a r
         , Adaptable advals )
      => (advals -> ADVal a) -> vals -> a
      -> vals
crevDt f vals dt = crevDtMaybe f vals (Just dt)

crevDtMaybe :: forall a vals r advals.
            ( r ~ Scalar vals, vals ~ Value advals
            , ADTensor r, IsPrimalWithScalar a r
            , Adaptable advals )
         => (advals -> ADVal a) -> vals -> Maybe a
         -> vals
crevDtMaybe f vals dt =
  let g inputs = f $ parseADInputs vals inputs
  in parseDomains vals $ fst $ revOnDomains dt g (toDomains vals)

-- Inspired by adaptors from @tomjaguarpaw's branch.
type Adaptable advals =
  ( AdaptableDomains (Value advals)
  , AdaptableInputs (Scalar (Value advals)) advals )

class FromDomainsAst astvals where
  type ValueAst astvals
  fromDomainsAst :: ValueAst astvals
                 -> Domains (Ast0 (Scalar (ValueAst astvals)))
                 -> (astvals, Domains (Ast0 (Scalar (ValueAst astvals))))

class AdaptableDomains vals where
  type Scalar vals
  toDomains :: Tensor (Scalar vals)
            => vals -> Domains (Scalar vals)
  fromDomains :: vals -> Domains (Scalar vals)
              -> (vals, Domains (Scalar vals))
  nParams :: vals -> Int
  nScalars :: vals -> Int

class RandomDomains vals where
  randomVals
    :: forall r g.
       ( RandomGen g
       , r ~ Scalar vals, Numeric r, Fractional r, Random r, Num (Vector r) )
    => r -> g -> (vals, g)

class AdaptableInputs r advals where
  type Value advals
  fromADInputs :: Value advals -> ADInputs r -> (advals, ADInputs r)

parseDomainsAst
  :: ( FromDomainsAst astvals, Tensor (Scalar (ValueAst astvals))
     , Numeric (Scalar (ValueAst astvals)), Show (Scalar (ValueAst astvals))
     , Floating (Vector (Scalar (ValueAst astvals))) )
  => ValueAst astvals -> Domains (Ast0 (Scalar (ValueAst astvals)))
  -> astvals
parseDomainsAst aInit domains =
  let (vals, rest) = fromDomainsAst aInit domains
  in assert (nullDomains rest) vals

parseDomains
  :: (AdaptableDomains vals, Tensor (Scalar vals))
  => vals -> Domains (Scalar vals) -> vals
parseDomains aInit domains =
  let (vals, rest) = fromDomains aInit domains
  in assert (nullDomains rest) vals

parseADInputs :: (AdaptableInputs r advals, Tensor r)
              => Value advals -> ADInputs r
              -> advals
parseADInputs aInit inputs =
  let (advals, rest) = fromADInputs aInit inputs
  in assert (nullADInputs rest) advals

instance FromDomainsAst (Ast0 Double) where
  type ValueAst (Ast0 Double) = Double
  fromDomainsAst _aInit (Domains v0 v1) = case tuncons v0 of
    Just (a, rest) -> (tunScalar a, Domains rest v1)
    Nothing -> error "fromDomainsAst in FromDomainsAst Double"

instance AdaptableDomains Double where
  type Scalar Double = Double
  toDomains a = Domains (tfromList [tscalar a]) V.empty
  fromDomains _aInit (Domains v0 v1) = case tuncons v0 of
    Just (a, rest) -> (tunScalar a, Domains rest v1)
    Nothing -> error "fromDomains in AdaptableDomains Double"
  nParams _ = 1
  nScalars _ = 1

instance RandomDomains Double where
  randomVals range = randomR (- range, range)
    -- note that unlike in hmatrix the range is closed from the top

instance AdaptableInputs Double (ADVal Double) where
  type Value (ADVal Double) = Double
  fromADInputs _aInit inputs@ADInputs{..} = case tuncons inputPrimal0 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual0 of
      Just (aDual, restDual) ->
        ( dD (tunScalar aPrimal) aDual
        , inputs {inputPrimal0 = restPrimal, inputDual0 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs Double"
    Nothing -> error "fromADInputs in AdaptableInputs Double"

instance FromDomainsAst (Ast0 Float) where
  type ValueAst (Ast0 Float) = Float
  fromDomainsAst _aInit (Domains v0 v1) = case tuncons v0 of
    Just (a, rest) -> (tunScalar a, Domains rest v1)
    Nothing -> error "fromDomainsAst in FromDomainsAst Float"

instance AdaptableDomains Float where
  type Scalar Float = Float
  toDomains a = Domains (tfromList [tscalar a]) V.empty
  fromDomains _aInit (Domains v0 v1) = case tuncons v0 of
    Just (a, rest) -> (tunScalar a, Domains rest v1)
    Nothing -> error "fromDomains in AdaptableDomains Float"
  nParams _ = 1
  nScalars _ = 1

instance RandomDomains Float where
  randomVals range = randomR (- range, range)

instance AdaptableInputs Float (ADVal Float) where
  type Value (ADVal Float) = Float
  fromADInputs _aInit inputs@ADInputs{..} = case tuncons inputPrimal0 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual0 of
      Just (aDual, restDual) ->
        ( dD (tunScalar aPrimal) aDual
        , inputs {inputPrimal0 = restPrimal, inputDual0 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs Float"
    Nothing -> error "fromADInputs in AdaptableInputs Float"

instance (RealFloat r, Show r, Numeric r, Floating (Vector r))
         => AdaptableInputs (Ast0 r) (ADVal (Ast0 r)) where
  type Value (ADVal (Ast0 r)) = r
  fromADInputs _aInit inputs@ADInputs{..} = case tuncons inputPrimal0 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual0 of
      Just (aDual, restDual) ->
        ( dD (tunScalar aPrimal) aDual
        , inputs {inputPrimal0 = restPrimal, inputDual0 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs (Ast0 r)"
    Nothing -> error "fromADInputs in AdaptableInputs (Ast0 r)"

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

instance ( Tensor r, Numeric r, Show r, Floating (Vector r), KnownNat n
         , TensorOf n r ~ OR.Array n r )
         => FromDomainsAst (Ast n r) where
  type ValueAst (Ast n r) = OR.Array n r
  fromDomainsAst aInit (Domains v0 v1) = case V.uncons v1 of
    Just (a, rest) -> (ttoRankedOrDummy (tshape aInit) a, Domains v0 rest)
    Nothing -> error "fromDomainsAst in FromDomainsAst (OR.Array n r)"

ttoRankedOrDummy :: (Tensor r, HasPrimal r, KnownNat n)
                 => ShapeInt n -> DynamicTensor r -> TensorOf n r
ttoRankedOrDummy sh x = if tisDummyD x
                        then tzero sh
                        else tfromD x

instance (Numeric r, KnownNat n, DynamicTensor r ~ OT.Array r)
         => AdaptableDomains (OR.Array n r) where
  type Scalar (OR.Array n r) = r
  toDomains a =
    Domains emptyDomain0 (V.singleton (Data.Array.Convert.convert a))
  fromDomains aInit (Domains v0 v1) = case V.uncons v1 of
    Just (a, rest) -> (toRankedOrDummy (OR.shapeL aInit) a, Domains v0 rest)
    Nothing -> error "fromDomains in AdaptableDomains (OR.Array n r)"
  nParams _ = 1
  nScalars = OR.size

instance KnownNat n
         => RandomDomains (OR.Array n r) where
  randomVals range g =
    let createRandomVector n seed =
          LA.scale (2 * range)
          $ V.fromListN n (randoms seed) - LA.scalar 0.5
        (g1, g2) = split g
        arr = OR.fromVector undefined $ createRandomVector (OR.size undefined) g1  -- TODO
    in (arr, g2)

instance ( ADTensor r, KnownNat n, TensorOf n r ~ OR.Array n r
         , DynamicTensor r ~ OT.Array r )
         => AdaptableInputs r (ADVal (OR.Array n r)) where
  type Value (ADVal (OR.Array n r)) = OR.Array n r
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimal1 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual1 of
      Just (aDual, restDual) ->
        ( fromX1 @n $ dD aPrimal aDual
        , inputs {inputPrimal1 = restPrimal, inputDual1 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs (OR.Array n r)"
    Nothing -> error "fromADInputs in AdaptableInputs (OR.Array n r)"

instance (KnownNat n, RealFloat r, Show r, Numeric r, Floating (Vector r))
         => AdaptableInputs (Ast0 r) (ADVal (Ast n r)) where
  type Value (ADVal (Ast n r)) = OR.Array n r
  fromADInputs _aInit inputs@ADInputs{..} = case V.uncons inputPrimal1 of
    Just (aPrimal, restPrimal) -> case V.uncons inputDual1 of
      Just (aDual, restDual) ->
        ( fromX1 @n $ dD aPrimal aDual
        , inputs {inputPrimal1 = restPrimal, inputDual1 = restDual} )
      Nothing -> error "fromADInputs in AdaptableInputs (OR.Array n r)"
    Nothing -> error "fromADInputs in AdaptableInputs (OR.Array n r)"

instance FromDomainsAst a
         => FromDomainsAst [a] where
  type ValueAst [a] = [ValueAst a]
  fromDomainsAst lInit source =
    let f (lAcc, restAcc) aInit =
          let (a, rest) = fromDomainsAst aInit restAcc
          in (a : lAcc, rest)
        (l, restAll) = foldl' f ([], source) lInit
    in (reverse l, restAll)

instance AdaptableDomains a
         => AdaptableDomains [a] where
  type Scalar [a] = Scalar a
  toDomains l =
    let (l0, l1) = unzip $ map (domainsToQuadruple . toDomains) l
    in Domains (tconcat l0) (V.concat l1)
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

domainsToQuadruple :: Domains r -> (Domain0 r, Domain1 r)
domainsToQuadruple Domains{..} = (domains0, domains1)

instance AdaptableInputs r a
         => AdaptableInputs r [a] where
  type Value [a] = [Value a]
  fromADInputs lInit source =
    let f (lAcc, restAcc) aInit =
          let (a, rest) = fromADInputs aInit restAcc
          in (a : lAcc, rest)
        (l, restAll) = foldl' f ([], source) lInit
    in (reverse l, restAll)

instance ( r ~ Scalar (ValueAst a), r ~ Scalar (ValueAst b)
         , FromDomainsAst a
         , FromDomainsAst b ) => FromDomainsAst (a, b) where
  type ValueAst (a, b) = (ValueAst a, ValueAst b)
  fromDomainsAst (aInit, bInit) source =
    let (a, aRest) = fromDomainsAst aInit source
        (b, bRest) = fromDomainsAst bInit aRest
    in ((a, b), bRest)

instance ( r ~ Scalar a, r ~ Scalar b
         , AdaptableDomains a
         , AdaptableDomains b ) => AdaptableDomains (a, b) where
  type Scalar (a, b) = Scalar a
  toDomains (a, b) =
    let Domains a0 a1 = toDomains a
        Domains b0 b1 = toDomains b
    in Domains (tconcat [a0, b0])
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

instance ( r ~ Scalar (ValueAst a), r ~ Scalar (ValueAst b)
         , r ~ Scalar (ValueAst c)
         , FromDomainsAst a
         , FromDomainsAst b
         , FromDomainsAst c ) => FromDomainsAst (a, b, c) where
  type ValueAst (a, b, c) = (ValueAst a, ValueAst b, ValueAst c)
  fromDomainsAst (aInit, bInit, cInit) source =
    let (a, aRest) = fromDomainsAst aInit source
        (b, bRest) = fromDomainsAst bInit aRest
        (c, rest) = fromDomainsAst cInit bRest
    in ((a, b, c), rest)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c ) => AdaptableDomains (a, b, c) where
  type Scalar (a, b, c) = Scalar a
  toDomains (a, b, c) =
    let Domains a0 a1 = toDomains a
        Domains b0 b1 = toDomains b
        Domains c0 c1 = toDomains c
    in Domains (tconcat [a0, b0, c0])
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

instance ( r ~ Scalar (ValueAst a), r ~ Scalar (ValueAst b)
         , r ~ Scalar (ValueAst c), r ~ Scalar (ValueAst d)
         , FromDomainsAst a
         , FromDomainsAst b
         , FromDomainsAst c
         , FromDomainsAst d ) => FromDomainsAst (a, b, c, d) where
  type ValueAst (a, b, c, d) =
    (ValueAst a, ValueAst b, ValueAst c, ValueAst d)
  fromDomainsAst (aInit, bInit, cInit, dInit) source =
    let (a, aRest) = fromDomainsAst aInit source
        (b, bRest) = fromDomainsAst bInit aRest
        (c, cRest) = fromDomainsAst cInit bRest
        (d, rest) = fromDomainsAst dInit cRest
    in ((a, b, c, d), rest)

instance ( r ~ Scalar a, r ~ Scalar b, r ~ Scalar c, r ~ Scalar d
         , AdaptableDomains a
         , AdaptableDomains b
         , AdaptableDomains c
         , AdaptableDomains d ) => AdaptableDomains (a, b, c, d) where
  type Scalar (a, b, c, d) = Scalar a
  toDomains (a, b, c, d) =
    let Domains a0 a1 = toDomains a
        Domains b0 b1 = toDomains b
        Domains c0 c1 = toDomains c
        Domains d0 d1 = toDomains d
    in Domains (tconcat [a0, b0, c0, d0])
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

instance ( AdaptableInputs r a
         , AdaptableInputs r b )
         => AdaptableInputs r (a, b) where
  type Value (a, b) = (Value a, Value b)
  fromADInputs (aInit, bInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, rest) = fromADInputs bInit aRest
    in ((a, b), rest)

instance ( AdaptableInputs r a
         , AdaptableInputs r b
         , AdaptableInputs r c )
         => AdaptableInputs r (a, b, c) where
  type Value (a, b, c) = (Value a, Value b, Value c)
  fromADInputs (aInit, bInit, cInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, bRest) = fromADInputs bInit aRest
        (c, rest) = fromADInputs cInit bRest
    in ((a, b, c), rest)

instance ( AdaptableInputs r a
         , AdaptableInputs r b
         , AdaptableInputs r c
         , AdaptableInputs r dd )
         => AdaptableInputs r (a, b, c, dd) where
  type Value (a, b, c, dd) = (Value a, Value b, Value c, Value dd)
  fromADInputs (aInit, bInit, cInit, dInit) source =
    let (a, aRest) = fromADInputs aInit source
        (b, bRest) = fromADInputs bInit aRest
        (c, cRest) = fromADInputs cInit bRest
        (dd, rest) = fromADInputs dInit cRest
    in ((a, b, c, dd), rest)

instance ( r ~ Scalar (ValueAst a), r ~ Scalar (ValueAst b)
         , FromDomainsAst a, FromDomainsAst b )
         => FromDomainsAst (Either a b) where
  type ValueAst (Either a b) = Either (ValueAst a) (ValueAst b)
  fromDomainsAst eInit source = case eInit of
    Left a -> let (a2, rest) = fromDomainsAst a source
              in (Left a2, rest)
    Right b -> let (b2, rest) = fromDomainsAst b source
               in (Right b2, rest)

instance ( r ~ Scalar a, r ~ Scalar b
         , AdaptableDomains a, AdaptableDomains b )
         => AdaptableDomains (Either a b) where
  type Scalar (Either a b) = Scalar a
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

instance (AdaptableInputs r a, AdaptableInputs r b)
         => AdaptableInputs r (Either a b) where
  type Value (Either a b) = Either (Value a) (Value b)
  fromADInputs eInit source = case eInit of
    Left a -> let (a2, rest) = fromADInputs a source
              in (Left a2, rest)
    Right b -> let (b2, rest) = fromADInputs b source
               in (Right b2, rest)

instance FromDomainsAst a
         => FromDomainsAst (Maybe a) where
  type ValueAst (Maybe a) = Maybe (ValueAst a)
  fromDomainsAst eInit source = case eInit of
    Nothing -> (Nothing, source)
    Just a -> let (a2, rest) = fromDomainsAst a source
              in (Just a2, rest)

instance AdaptableDomains a
         => AdaptableDomains (Maybe a) where
  type Scalar (Maybe a) = Scalar a
  toDomains e = case e of
    Nothing -> Domains emptyDomain0 V.empty
    Just a -> toDomains a
  fromDomains eInit source = case eInit of
    Nothing -> (Nothing, source)
    Just a -> let (a2, rest) = fromDomains a source
              in (Just a2, rest)
  nParams = maybe 0 nParams
  nScalars = maybe 0 nScalars

instance AdaptableInputs r a
         => AdaptableInputs r (Maybe a) where
  type Value (Maybe a) = Maybe (Value a)
  fromADInputs eInit source = case eInit of
    Nothing -> (Nothing, source)
    Just a -> let (a2, rest) = fromADInputs a source
              in (Just a2, rest)
