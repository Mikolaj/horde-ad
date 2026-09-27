{-# LANGUAGE AllowAmbiguousTypes #-}
-- | Micro-benchmarks of small recursive functions and methods, most of them
-- dispatching on a tensor kind: 'mapAccumL'', 'sameSTK', 'matchingFTK',
-- the Concrete @tfromList@ (through 'tscan'), 'astConcrete' (also through
-- 'tconcrete') and @concreteRepW@ (through 'astConcrete' at a nested kind,
-- which has no shortcut there), the AST @interpretAstHFun@
-- (through interpreting a mapAccum), @astConvDown@ and @astConvUp@
-- (through simplifying a mapAccum whose accumulator is converted),
-- the AST instance methods 'tsum', 'treplicate' and 'treverse', and the class
-- default methods 'tappend', 'tunravelToListShare', 'tsize', 'tsum',
-- 'treplicate' and 'treverse' at the instances that take them.
--
-- Each is timed in isolation, on arguments small enough that its own call
-- and dispatch cost is not drowned by the kernels it dispatches to, so that
-- a change in how GHC compiles one of them --- whether it is inlined,
-- worker/wrappered or specialised --- shows here where the end-to-end
-- suites average it away. Compare two builds by allocation first, collected
-- with @--regress allocated:iters@ and @+RTS -T@, which is exact in the
-- iteration count; then by instructions a call, the difference
-- of @perf stat -e instructions:u@ over two processes running one benchmark
-- for @--iters 2N@ and @--iters N@, divided by @N@. Criterion's times are
-- not enough at this scale: across one pair of builds @tsize-S@ took 14%
-- longer at an instruction count within 0.4%.
--
-- Each tensor-kind argument is a product tree over one leaf of every array
-- variant (@P4@), so that every arm of each dispatcher runs. The @-S@
-- variants, on the Concrete and AST instances only, pass a single shaped leaf
-- whose kind is known at the call, where an inlined dispatcher folds to one
-- kernel call.
module Main (main) where

import Prelude

import Control.Exception (evaluate)
import Criterion.Main
import Data.List (foldl')
import Data.Maybe (isJust)
import Data.Proxy (Proxy (Proxy))
import GHC.TypeLits (KnownNat)

import Data.Array.Nested (MapJust)
import Data.Array.Nested.Ranked.Shape (pattern (:$:), pattern ZSR)
import Data.Array.Nested.Shaped.Shape (knownShS)

import HordeAd.Core.Ast
import HordeAd.Core.AstEnv (emptyEnv, extendEnv)
import HordeAd.Core.AstInterpret (interpretAstFull)
import HordeAd.Core.AstSimplify (astConcrete)
import HordeAd.Core.CarriersADVal (ADVal)
import HordeAd.Core.CarriersAst (AstRaw (..))
import HordeAd.Core.CarriersConcrete
import HordeAd.Core.ConvertTensor
import HordeAd.Core.Ops
import HordeAd.Core.OpsADVal ()
import HordeAd.Core.OpsAst ()
import HordeAd.Core.OpsConcrete ()
import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- * The tensor kinds

type Sh = '[2, 3]
type L = TKS Sh Double
type R = TKR 2 Double
type X = TKX (MapJust Sh) Double
-- | One leaf of each array variant, so that every arm of a dispatcher runs.
type P4 = TKProduct (TKProduct L R) (TKProduct X L)
type K = 4

type AstF = AstTensor AstMethodLet FullSpan

-- * Concrete values

cL :: Concrete L
cL = srepl 1.5

cR :: Concrete R
cR = rfromS cL

cX :: Concrete X
cX = xfromS cL

cP4 :: Concrete P4
cP4 = tpair (tpair cL cR) (tpair cX cL)

stkP4 :: SingletonTK P4
stkP4 = knownSTK

stkL :: SingletonTK L
stkL = knownSTK

snatK :: SNat K
snatK = SNat

cBP4 :: Concrete (BuildTensorKind K P4)
cBP4 = treplicate snatK stkP4 cP4

cBL :: Concrete (BuildTensorKind K L)
cBL = treplicate snatK stkL cL

-- * AST values

astVarOf :: FullShapeTK y -> Int -> AstF y
astVarOf ftk n = AstVar $ mkAstVarName ftk (intToAstVarId n)

aP4 :: AstF P4
aP4 = astVarOf (tftk stkP4 cP4) 100000001

aBP4 :: AstF (BuildTensorKind K P4)
aBP4 = astVarOf (tftk (buildSTK snatK stkP4) cBP4) 100000002

aL :: AstF L
aL = astVarOf (tftk stkL cL) 100000003

aBL :: AstF (BuildTensorKind K L)
aBL = astVarOf (tftk (buildSTK snatK stkL) cBL) 100000004

rawOf :: AstF y -> AstRaw FullSpan y
rawOf (AstVar var) = AstRaw (AstVar var)
rawOf _ = error "rawOf: not a variable"

-- * Singletons for the equality tests

data SomeSTK = forall y. SomeSTK (SingletonTK y)
data SomeFTK = forall y. SomeFTK (FullShapeTK y)

-- | A balanced product tree of the given depth over the four leaves
-- of 'P4', built at runtime, so that no two calls share a structure
-- and nothing is known statically.
stkTree :: Int -> SomeSTK
stkTree 0 = SomeSTK stkP4
stkTree d = case (stkTree (d - 1), stkTree (d - 1)) of
  (SomeSTK a, SomeSTK b) -> SomeSTK (STKProduct a b)

ftkTree :: Int -> SomeFTK
ftkTree 0 = SomeFTK (tftk stkP4 cP4)
ftkTree d = case (ftkTree (d - 1), ftkTree (d - 1)) of
  (SomeFTK a, SomeFTK b) -> SomeFTK (FTKProduct a b)

-- | The same tree with its last leaf of a different scalar type, so that
-- the test walks it all and then fails.
stkTreeOff :: Int -> SomeSTK
stkTreeOff 0 = SomeSTK (STKProduct (STKProduct stkL (knownSTK @R))
                                   (STKProduct (knownSTK @X)
                                               (knownSTK @(TKS Sh Float))))
stkTreeOff d = case (stkTree (d - 1), stkTreeOff (d - 1)) of
  (SomeSTK a, SomeSTK b) -> SomeSTK (STKProduct a b)

ftkTreeOff :: Int -> SomeFTK
ftkTreeOff 0 = case tftk stkP4 cP4 of
  FTKProduct l (FTKProduct x (FTKS sh FTKScalar)) ->
    SomeFTK (FTKProduct l (FTKProduct x (FTKS sh (FTKScalar @Float))))
ftkTreeOff d = case (ftkTree (d - 1), ftkTreeOff (d - 1)) of
  (SomeFTK a, SomeFTK b) -> SomeFTK (FTKProduct a b)

sameSome :: (SomeSTK, SomeSTK) -> Bool
sameSome (SomeSTK a, SomeSTK b) = isJust (sameSTK a b)

matchingSome :: (SomeFTK, SomeFTK) -> Bool
matchingSome (SomeFTK a, SomeFTK b) = isJust (matchingFTK a b)

-- * mapAccumL'

stepAcc :: Int -> Int -> (Int, Int)
stepAcc !acc x = (acc + x, acc * x)

-- | Through the RULE, fused with an enumeration.
mapAccumFused :: Int -> Int
mapAccumFused n = let (a, l) = mapAccumL' stepAcc 0 [1 .. n]
                  in foldl' (+) a l

-- | Through the out-of-line function: passed unapplied to a NOINLINE
-- function, the call is one the RULE cannot match, having no arguments,
-- where written directly it would be fused into a local loop, as in
-- 'mapAccumFused', even on a list that exists before the call.
mapAccumList :: [Int] -> Int
mapAccumList = mapAccumVia mapAccumL'

mapAccumVia :: ((Int -> Int -> (Int, Int)) -> Int -> [Int] -> (Int, [Int]))
            -> [Int] -> Int
{-# NOINLINE mapAccumVia #-}
mapAccumVia mapAcc l0 = let (a, l) = mapAcc stepAcc 0 l0
                        in foldl' (+) a l

-- * interpretAstHFun, astConvDown and astConvUp

type AccR = TKR 1 Double
type AccS = TKS '[3] Double
type KM = 2
-- | The argument and result of the mapAccum step.
type XM = TKProduct AccR AccR

accSftk :: FullShapeTK AccS
accSftk = FTKS knownShS FTKScalar

accRftk :: FullShapeTK AccR
accRftk = tftk knownSTK (rfromS @Concrete (srepl @'[3] @Double 0))

esRftk :: FullShapeTK (BuildTensorKind KM AccR)
esRftk = buildFTK (SNat @KM) accRftk

mapAccumStep :: ADReady f => f AccR -> f AccR -> f (TKProduct AccR AccR)
mapAccumStep acc e = tpair (acc + e) (acc * e)

-- | A mapAccum simplified at construction whose initial accumulator is
-- a conversion, which is what calls @astConvDown@ and @astConvUp@;
-- the derivative functions are built once, outside the timed call.
mapAccumConv :: AstF AccS -> AstF (TKProduct AccR (BuildTensorKind KM AccR))
mapAccumConv =
  let xftk = FTKProduct accRftk accRftk
      fl :: forall f. ADReady f => f XM -> f XM
      fl !args = ttlet args $ \ !args1 ->
                   mapAccumStep (tproject1 args1) (tproject2 args1)
      hf :: HFunOf AstF XM XM
      !hf = tlambda @AstF xftk (HFun fl)
      hdf, hrf :: HFunOf AstF (TKProduct (ADTensorKind XM) XM)
                              (ADTensorKind XM)
      !hdf = tjvp @AstF xftk (HFun fl)
      !hrf = tvjp @AstF xftk (HFun fl)
      !es = astVarOf esRftk 100000011
  in \acc0S -> tmapAccumLDer (Proxy @AstF) (SNat @KM) accRftk accRftk accRftk
                             hf hdf hrf (rfromS acc0S) es

-- * Main

main :: IO ()
main = do
  let !stkTrees = (stkTree 3, stkTree 3)
      !stkTreesOff = (stkTree 3, stkTreeOff 3)
      !ftkTrees = (ftkTree 3, ftkTree 3)
      !ftkTreesOff = (ftkTree 3, ftkTreeOff 3)
      !stkLeaves = (SomeSTK stkL, SomeSTK (knownSTK @L))
      !ftkLeaves = (SomeFTK (tftk stkL cL), SomeFTK (tftk stkL cL))
      listIn = [1 .. 1000] :: [Int]
      aS = astVarOf accSftk 100000010
      mapAccumAst = mapAccumConv aS
      cS = srepl @'[3] @Double 0.5
      cEs = treplicate (SNat @KM) (knownSTK @AccR) (rfromS @Concrete cS)
      varS = mkAstVarName @FullSpan accSftk (intToAstVarId 100000010)
      varEs = mkAstVarName @FullSpan esRftk (intToAstVarId 100000011)
      envM = extendEnv varS cS $ extendEnv varEs cEs emptyEnv
      adP4 :: ADVal Concrete P4
      adP4 = tfromPrimal stkP4 cP4
      adBP4 :: ADVal Concrete (BuildTensorKind K P4)
      adBP4 = tfromPrimal (buildSTK snatK stkP4) cBP4
  _ <- evaluate (length listIn)
  _ <- evaluate cBP4
  _ <- evaluate cBL
  _ <- evaluate aBP4
  _ <- evaluate mapAccumAst
  _ <- evaluate adBP4
  defaultMain
    [ bgroup "mapAccumL'"
        [ bench "fused" $ whnf mapAccumFused 1000
        , bench "list" $ whnf mapAccumList listIn
        ]
    , bgroup "sameSTK"
        [ bench "tree-eq" $ whnf sameSome stkTrees
        , bench "tree-neq" $ whnf sameSome stkTreesOff
        , bench "leaf-S" $ whnf sameSome stkLeaves
        ]
    , bgroup "matchingFTK"
        [ bench "tree-eq" $ whnf matchingSome ftkTrees
        , bench "tree-neq" $ whnf matchingSome ftkTreesOff
        , bench "leaf-S" $ whnf matchingSome ftkLeaves
        ]
    , bgroup "Concrete"
        [ bench "tscan-P4" $ nf (tscan @Concrete (SNat @2) stkP4 stkP4
                                      (\a b -> tpair (tproject1 a)
                                                     (tproject2 b))
                                      cP4)
                                (treplicate (SNat @2) stkP4 cP4)
        , bench "tsum-P4" $ nf (tsum snatK stkP4) cBP4
        , bench "tsum-S" $ nf (tsum snatK stkL) cBL
        , bench "treplicate-P4" $ nf (treplicate snatK stkP4) cP4
        , bench "treplicate-S" $ nf (treplicate snatK stkL) cL
        , bench "treverse-P4" $ nf (treverse snatK stkP4) cBP4
        , bench "treverse-S" $ nf (treverse snatK stkL) cBL
        , bench "tappend-P4" $ nf (\u -> tappend snatK snatK stkP4 u u) cBP4
        , bench "tappend-S" $ nf (\u -> tappend snatK snatK stkL u u) cBL
        , bench "tunravelToListShare-P4" $
            nf (tunravelToListShare snatK stkP4) cBP4
        , bench "tunravelToListShare-S" $
            nf (tunravelToListShare snatK stkL) cBL
        , bench "tsize-P4" $ whnf (tsize stkP4) cP4
        , bench "tsize-S" $ whnf (tsize stkL) cL
        ]
    , bgroup "ADVal"
        [ bench "tsum-P4" $ whnf (tsum snatK stkP4) adBP4
        , bench "treplicate-P4" $ whnf (treplicate snatK stkP4) adP4
        , bench "treverse-P4" $ whnf (treverse snatK stkP4) adBP4
        , bench "tappend-P4" $ whnf (\u -> tappend snatK snatK stkP4 u u) adBP4
        , bench "tunravelToListShare-P4" $
            whnf (length . tunravelToListShare snatK stkP4) adBP4
        , bench "tsize-P4" $ whnf (tsize stkP4) adP4
        ]
    , bgroup "AstRaw"
        [ bench "tsum-P4" $ whnf (tsum snatK stkP4) (rawOf aBP4)
        , bench "treplicate-P4" $ whnf (treplicate snatK stkP4) (rawOf aP4)
        , bench "treverse-P4" $ whnf (treverse snatK stkP4) (rawOf aBP4)
        , bench "tappend-P4" $
            whnf (\u -> tappend snatK snatK stkP4 u u) (rawOf aBP4)
        , bench "tunravelToListShare-P4" $
            whnf (length . tunravelToListShare snatK stkP4) (rawOf aBP4)
        , bench "tsize-P4" $ whnf (tsize stkP4) (rawOf aP4)
        ]
    , bgroup "Ast"
        [ bench "tsum-P4" $ whnf (tsum snatK stkP4) aBP4
        , bench "tsum-S" $ whnf (tsum snatK stkL) aBL
        , bench "treplicate-P4" $ whnf (treplicate snatK stkP4) aP4
        , bench "treplicate-S" $ whnf (treplicate snatK stkL) aL
        , bench "treverse-P4" $ whnf (treverse snatK stkP4) aBP4
        , bench "treverse-S" $ whnf (treverse snatK stkL) aBL
        , bench "tappend-P4" $
            whnf (\u -> tappend snatK snatK stkP4 u u) aBP4
        , bench "tsize-P4" $ whnf (tsize stkP4) aP4
        , bench "tconcrete-P4" $
            whnf (tconcrete @AstF (tftk stkP4 cP4)) cP4
        , bench "astConcrete-P4" $
            whnf (astConcrete (tftk stkP4 cP4)) cP4
        , bench "astConcrete-nested" $
            whnf (astConcrete (tftk knownSTK cNested)) cNested
        , bench "mapAccum-convUp" $ whnf mapAccumConv aS
        , bench "interpret-mapAccum" $
            nf (interpretAstFull @Concrete envM) mapAccumAst
        ]
    ]

-- | A ranked tensor of shaped tensors, which 'astConcrete' has no
-- shortcut for and so hands to @concreteTarget@ and @concreteRepW@.
cNested :: Concrete (TKR2 1 (TKS Sh Double))
cNested = tdefTarget (FTKR (2 :$: ZSR) (FTKS knownShS FTKScalar))
