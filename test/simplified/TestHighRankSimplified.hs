{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleInstances, OverloadedLists,
             RankNTypes, TypeFamilies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module TestHighRankSimplified (testTrees) where

import Prelude

import qualified Data.Array.RankedS as OR
import           Data.MonoTraversable (Element)
import qualified Data.Strict.IntMap as IM
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)
import           Test.Tasty
import           Test.Tasty.HUnit hiding (assert)

import HordeAd
import HordeAd.Core.DualClass (inputConstant)

import Tool.EqEpsilon

testTrees :: [TestTree]
testTrees =
  [ -- Tensor tests
    testCase "3foo" testFoo
  , testCase "3bar" testBar
  , testCase "3fooD T Double [1.1, 2.2, 3.3]" testFooD
  , testCase "3fooBuild0" testFooBuild0
  , testCase "3fooBuildOut" testFooBuildOut
  , testCase "3fooBuild21" testFooBuild21
  , testCase "3fooBuild25" testFooBuild25
  , testCase "3fooBuild3" testFooBuild3
  , testCase "3fooBuildDt" testFooBuildDt
  , testCase "3fooBuild5" testFooBuild5
  , testCase "3fooBuild1" testFooBuild1
    {-
  , testCase "3fooMap" testFooMap
  , testCase "3fooMap1" testFooMap1
  , testCase "3fooNoGoAst" testFooNoGoAst
  , testCase "3fooNoGo" testFooNoGo
  , testCase "3nestedBuildMap" testNestedBuildMap
  , testCase "3nestedBuildMap1" testNestedBuildMap1
  , testCase "3nestedSumBuild" testNestedSumBuild
  , testCase "3nestedBuildIndex" testNestedBuildIndex
  , testCase "3barReluADValDt" testBarReluADValDt
  , testCase "3barReluADVal" testBarReluADVal
  , testCase "3barReluADVal3" testBarReluADVal3
  , testCase "3barReluAst0" testBarReluAst0
  , testCase "3barReluAst1" testBarReluAst1
  , testCase "3konstReluAst" testKonstReluAst
  , -- Tests by TomS:
    testCase "3F1" testF1
  , testCase "3F11" testF11
  , testCase "3F2" testF2
  , testCase "3F21" testF21
  , testCase "3F3" testF3
  , -- Hairy tests
    testCase "3braidedBuilds" testBraidedBuilds
  , testCase "3braidedBuilds1" testBraidedBuilds1
  , testCase "3recycled" testRecycled
  , testCase "3recycled1" testRecycled1
  , testCase "3concatBuild" testConcatBuild
  , testCase "3concatBuild1" testConcatBuild1 -}
  ]

rev' :: forall a r n m.
        ( KnownNat n, KnownNat m
        , ADModeAndNumTensor 'ADModeGradient r, HasDelta r, ADReady r
        , a ~ OR.Array m r, TensorOf n r ~ OR.Array n r )
     => (forall x. ADReady x => TensorOf n x -> TensorOf m x)
     -> OR.Array n r
     -> (a, TensorOf m r, a, OR.Array n r, OR.Array n r)
rev' f vals =
  let dt = inputConstant @a 1
      g inputs = f $ parseADInputs vals inputs
      (advalGrad, value1) = revOnDomainsFun dt g (toDomains vals)
      gradient1 = parseDomains vals advalGrad
      value2 = f vals
      env inputs = IM.singleton 0 (AstVarR $ from1X $ parseADInputs vals inputs)
      h inputs =
        interpretAst (env inputs) (f (AstVar (tshape vals) (AstVarName 0)))
      (astGrad, value3) = revOnDomainsFun dt h (toDomains vals)
      gradient2 = parseDomains vals astGrad
  in (value1, value2, value3, gradient1, gradient2)

assertEqualUpToEpsilon'
    :: (AssertEqualUpToEpsilon z a, AssertEqualUpToEpsilon z b)
    => z  -- ^ error margin (i.e., the epsilon)
    -> a  -- ^ expected value
    -> (b, b, b, a, a)   -- ^ actual values
    -> Assertion
assertEqualUpToEpsilon' error_margin expected
                        (value1, value2, value3, gradient1, gradient2) = do
  value1 @?~ value2
  value3 @?~ value2
  assertEqualUpToEpsilon error_margin expected gradient1
  assertEqualUpToEpsilon error_margin expected gradient2


-- * Tensor tests

t16 :: (Numeric r, Fractional r) => OR.Array 5 r
t16 = OR.fromList [2, 2, 1, 2, 2] [5, 2, 6, 1, -2, 0.000001, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26]

t48 :: (Numeric r, Fractional r) => OR.Array 7 r
t48 = OR.fromList [3, 1, 2, 2, 1, 2, 2] [18.1,29.1,32.1,40.1,52.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,58.0,54.99432,97.1,52.8943200001, 5, 2, 6, 1, -2, 0.92, 0.1, -0.2, 13.1, 9, 8, -4, 34, 2.99432, -33, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003]

t128 :: (Numeric r, Fractional r) => OR.Array 10 r
t128 = OR.fromList [1, 2, 2, 1, 2, 2, 2, 2, 2, 1] [29.1,32.1,40.1,29.0,53.99432,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.0,53.99432,97.1,25.8943200001, 5, 2, 6, 1, -2, 97.1,58.8943200001,97.1,55.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,32.1,40.1,53.0,53.99432, -0.00001, 0.1, -0.2, 13.1, 9, 8, -4, 29, 2.99432, -335, 26, 2, 2, 2, 2, -0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,-0.2,-0.2,-0.2,-0.2,25.0003,25.0003,25.0003,25.0003,40.1,8.0,11.0,-3.0,25.89432,28.79432,-39.09999999999997,25.8,40.1,8.0,11.0,-3.0,25.89432,28.79432,-19.09999999999997,25.8, 8.1,29.1,32.1,40.1,32.1,40.1,292.0,53.99432,97.1,55.8943200001,97.1,85.8943200001,97.1,85.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,22.0,53.99432,97.1,82.8943200001,97.1,22.8943200001,97.1,58.8943200001,18.1,29.1,32.1,40.1,32.1,40.1,32.1,40.1,89.0,53.99432,97.1,56.8943200001,97.1,52.8943200001,97.1,55.8943200001]

foo :: RealFloat a => (a,a,a) -> a
foo (x,y,z) =
  let w = x * sin y
  in atan2 z w + z * w

testFoo :: Assertion
testFoo =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [2,2,1, 2,2] [-4.6947093,1.5697206,-1.6332961,0.34882763,1.5697206,-1.0,-0.9784988,-0.9158946,6.6326222,3.6699238,7.85237,-2.9069107,17.976654,0.3914159,32.98194,19.807974],OR.fromList [2,2,1, 2,2] [6.943779,-1.436789,33.67549,0.22397964,-1.436789,-1.0,-0.975235,-0.90365005,147.06645,-73.022705,-9.238474,-10.042692,-980.2843,-7.900571,-14.451739,436.9084],OR.fromList [2,2,1, 2,2] [-4.8945336,2.067469,-1.7196897,1.3341143,2.067469,1.0,0.99846554,0.99536234,6.6943173,3.7482092,7.977362,-3.1475093,18.000969,0.48736274,33.01224,19.845064])
    (rev @(OR.Array 5 Float) foo (t16, t16, t16))

bar :: forall a. RealFloat a => (a, a) -> a
bar (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

testBar :: Assertion
testBar =
  assertEqualUpToEpsilon 1e-9
    (OR.fromList [3, 1, 2, 2, 1, 2, 2] [304.13867,914.9335,823.0187,1464.4688,5264.3306,1790.0055,1535.4309,3541.6572,304.13867,914.9335,823.0187,1464.4688,6632.4355,6047.113,1535.4309,1346.6815,45.92141,6.4903135,5.5406737,1.4242969,6.4903135,1.1458766,4.6446533,2.3550234,88.783676,27.467598,125.27507,18.177452,647.1917,0.3878851,2177.6152,786.1792,6.4903135,6.4903135,6.4903135,6.4903135,2.3550234,2.3550234,2.3550234,2.3550234,21.783596,2.3550234,2.3550234,2.3550234,21.783596,21.783596,21.783596,21.783596],OR.fromList [3, 1, 2, 2, 1, 2, 2] [-5728.7617,24965.113,32825.07,-63505.953,-42592.203,145994.88,-500082.5,-202480.06,-5728.7617,24965.113,32825.07,-63505.953,49494.473,-2446.7632,-500082.5,-125885.58,-43.092484,-1.9601002,-98.97709,2.1931143,-1.9601002,1.8243169,-4.0434446,-1.5266153,2020.9731,-538.0603,-84.28137,62.963814,-34987.0,-9.917454,135.30023,17741.998,-1.9601002,-1.9601002,-1.9601002,-1.9601002,-1.5266153,-1.5266153,-1.5266153,-1.5266153,-4029.1775,-1.5266153,-1.5266153,-1.5266153,-4029.1775,-4029.1775,-4029.1775,-4029.1775])
    (rev (bar @(ADVal 'ADModeGradient (OR.Array 7 Float))) (t48, t48))

-- A dual-number and list-based version of a function that goes
-- from `R^3` to `R`.
fooD :: forall r n d. (ADModeAndNum d r, KnownNat n)
     => [ADVal d (OR.Array n r)] -> ADVal d (OR.Array n r)
fooD [x, y, z] =
  let w = x * sin y
  in atan2 z w + z * w
fooD _ = error "wrong number of arguments"

testFooD :: Assertion
testFooD =
  assertEqualUpToEpsilon 1e-10
    [OR.fromList [1,2,2,1,2,2,2,2,2,1] [18.73108960474591,20.665204824764675,25.821775835995922,18.666613887422585,34.775664100213014,62.54884873632415,37.93303229694526,11.635186977032971,18.73108960474591,20.665204824764675,25.821775835995922,20.600738734367262,34.775664100213014,62.54884873632415,16.663997008808924,3.1300339898598155,1.060799258653783,3.78942741815228,0.1889454555944933,-1.060799258653783,62.54884873632415,37.93303229694526,62.54884873632415,35.99996432769119,62.54884873632415,37.93303229694526,11.635186977032971,18.73108960474591,20.665204824764675,25.821775835995922,20.665204824764675,20.665204824764675,25.821775835995922,34.134947381491145,34.775664100213014,45527.22315787758,-4.488300547708207,2.1475176207684497,8.404498097344806,5.747373381623309,5.096832468946128,-2.4630526910399646,18.666613887422585,1.7769486222994448,-215.8115662030395,16.73214939773215,1.060799258653783,1.060799258653783,1.060799258653783,1.060799258653783,2.1475176207684497,2.1475176207684497,2.1475176207684497,2.1475176207684497,16.08742477551077,16.08742477551077,16.08742477551077,16.08742477551077,2.1475176207684497,2.1475176207684497,2.1475176207684497,2.1475176207684497,16.08742477551077,16.08742477551077,16.08742477551077,16.08742477551077,25.821775835995922,5.096832468946128,7.045006174919766,-1.7808956511653404,16.663997008744435,18.533999054066836,-25.177267779903083,16.60317012020362,25.821775835995922,5.096832468946128,7.045006174919766,-1.7808956511653404,16.663997008744435,18.533999054066836,-12.280721583745471,16.60317012020362,5.161956818274285,18.73108960474591,20.665204824764675,25.821775835995922,20.665204824764675,25.821775835995922,188.11000552192755,34.775664100213014,62.54884873632415,35.99996432769119,62.54884873632415,55.32933980086011,62.54884873632415,55.32933980086011,11.635186977032971,18.73108960474591,20.665204824764675,25.821775835995922,20.665204824764675,25.821775835995922,20.665204824764675,25.821775835995922,14.152094926881784,34.775664100213014,62.54884873632415,53.39649491503442,62.54884873632415,14.72904006548922,62.54884873632415,37.93303229694526,11.635186977032971,18.73108960474591,20.665204824764675,25.821775835995922,20.665204824764675,25.821775835995922,20.665204824764675,25.821775835995922,57.33025874582143,34.775664100213014,62.54884873632415,36.64432517917614,62.54884873632415,34.06684929392724,62.54884873632415,35.99996432769119],OR.fromList [1,2,2,1,2,2,2,2,2,1] [647.1354943759653,787.5605199613974,1229.333367336918,642.6917612678424,2229.2701397674327,7210.705208776531,2652.3459120285806,250.02943073785886,647.1354943759653,787.5605199613974,1229.333367336918,782.6578815409038,2229.2701397674327,7210.705208776531,512.2982591657892,18.580536443699742,2.518850510725482,26.993800503829114,0.2243239488720164,2.518850510725482,7210.705208776531,2652.3459120285806,7210.705208776531,2388.9603285490866,7210.705208776531,2652.3459120285806,250.02943073785886,647.1354943759653,787.5605199613974,1229.333367336918,787.5605199613974,787.5605199613974,1229.333367336918,2147.9011858437157,2229.2701397674327,-0.5405182383359878,-0.5328698165396271,-0.5099245509210925,130.7140495214786,61.4116989316311,48.40938174779479,11.696956758139343,642.6917612678424,6.317020301049852,85833.87394976329,516.4928003659018,2.518850510725482,2.518850510725482,2.518850510725482,2.518850510725482,-0.5099245509210925,-0.5099245509210925,-0.5099245509210925,-0.5099245509210925,477.4973215160379,477.4973215160379,477.4973215160379,477.4973215160379,-0.5099245509210925,-0.5099245509210925,-0.5099245509210925,-0.5099245509210925,477.4973215160379,477.4973215160379,477.4973215160379,477.4973215160379,1229.333367336918,48.40938174779479,92.00538642301063,6.3430614471479245,512.2982591618282,633.5999783697488,1168.7578661039847,508.56903530563443,1229.333367336918,48.40938174779479,92.00538642301063,6.3430614471479245,512.2982591618282,633.5999783697488,278.48156010484087,508.56903530563443,49.64077766932281,647.1354943759653,787.5605199613974,1229.333367336918,787.5605199613974,1229.333367336918,65212.963738386214,2229.2701397674327,7210.705208776531,2388.9603285490866,7210.705208776531,5642.338335044463,7210.705208776531,5642.338335044463,250.02943073785886,647.1354943759653,787.5605199613974,1229.333367336918,787.5605199613974,1229.333367336918,787.5605199613974,1229.333367336918,369.6431004072799,2229.2701397674327,7210.705208776531,5255.048317224881,7210.705208776531,400.3514287686239,7210.705208776531,2652.3459120285806,250.02943073785886,647.1354943759653,787.5605199613974,1229.333367336918,787.5605199613974,1229.333367336918,787.5605199613974,1229.333367336918,6057.774447242021,2229.2701397674327,7210.705208776531,2475.225838667682,7210.705208776531,2139.3419044407133,7210.705208776531,2388.9603285490866],OR.fromList [1,2,2,1,2,2,2,2,2,1] [18.76237979248771,20.69357069589509,25.8444826804669,18.698011972363496,34.7925278085306,62.558226125235436,37.948492946856575,11.685493300971446,18.76237979248771,20.69357069589509,25.8444826804669,20.629193248844963,34.7925278085306,62.558226125235436,16.699160877305292,3.3121428825170947,1.516071490296981,3.9411848287000124,1.0994899188808887,-1.516071490296981,62.558226125235436,37.948492946856575,62.558226125235436,36.01625479268449,62.558226125235436,37.948492946856575,11.685493300971446,18.76237979248771,20.69357069589509,25.8444826804669,20.69357069589509,20.69357069589509,25.8444826804669,34.1521274657041,34.7925278085306,-45527.22317076194,4.617144085155745,-2.4052046956635262,8.474005308282699,5.84854498865513,5.210650526856928,-2.6906888068615635,18.698011972363496,2.0810391881996813,-215.8142842462135,16.767170338627782,1.516071490296981,1.516071490296981,1.516071490296981,1.516071490296981,-2.4052046956635262,-2.4052046956635262,-2.4052046956635262,-2.4052046956635262,16.123846116986126,16.123846116986126,16.123846116986126,16.123846116986126,-2.4052046956635262,-2.4052046956635262,-2.4052046956635262,-2.4052046956635262,16.123846116986126,16.123846116986126,16.123846116986126,16.123846116986126,25.8444826804669,5.210650526856928,7.127782944309438,-2.0844104722608057,16.69916087724094,18.565621417897145,-25.200555362084323,16.638462541261234,25.8444826804669,5.210650526856928,7.127782944309438,-2.0844104722608057,16.69916087724094,18.565621417897145,-12.328394068734287,16.638462541261234,5.2743697149763085,18.76237979248771,20.69357069589509,25.8444826804669,20.69357069589509,25.8444826804669,188.113123824884,34.7925278085306,62.558226125235436,36.01625479268449,62.558226125235436,55.33994055377702,62.558226125235436,55.33994055377702,11.685493300971446,18.76237979248771,20.69357069589509,25.8444826804669,20.69357069589509,25.8444826804669,20.69357069589509,25.8444826804669,14.193483311576621,34.7925278085306,62.558226125235436,53.40747931617656,62.558226125235436,14.768811697198851,62.558226125235436,37.948492946856575,11.685493300971446,18.76237979248771,20.69357069589509,25.8444826804669,20.69357069589509,25.8444826804669,20.69357069589509,25.8444826804669,57.34048958248757,34.7925278085306,62.558226125235436,36.660329315674915,62.558226125235436,34.08406370302229,62.558226125235436,36.01625479268449]]
    (rev fooD [t128, OR.constant [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]
                                 (0.7 :: Double), t128])

fooBuild0 :: forall r n. (ADReady r, KnownNat n)
          => TensorOf (1 + n) r -> TensorOf (1 + n) r
fooBuild0 v =
  let r = tsum v
  in tbuild1 2 $ \ix -> r

testFooBuild0 :: Assertion
testFooBuild0 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2,2,1,2,2] [2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0,2.0])
    (rev' @(OR.Array 5 Double) fooBuild0 t16)

fooBuildOut :: forall r n. (ADReady r, KnownNat n)
            => TensorOf (1 + n) r -> TensorOf (1 + n) r
fooBuildOut v =
  tbuild1 2 $ \ix -> tindex v [ix + 1]  -- index out of bounds; fine

testFooBuildOut :: Assertion
testFooBuildOut =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2,2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @(OR.Array 5 Double) fooBuildOut t16)

fooBuild2 :: forall r n.
             ( ADReady r, KnownNat n, RealFloat (TensorOf n r) )
          => TensorOf (1 + n) r -> TensorOf (1 + n) r
fooBuild2 v =
  tbuild1 2 $ \ix -> tindex v [max 1 (ix + 1)]  -- index out of bounds; fine

testFooBuild21 :: Assertion
testFooBuild21 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2] [0.0,1.0])
    (rev' @(OR.Array 1 Double) fooBuild2 (OR.fromList [2] [3.0,2.0]))

testFooBuild25 :: Assertion
testFooBuild25 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2,2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0,1.0])
    (rev' @(OR.Array 5 Double) fooBuild2 t16)

fooBuild3 :: forall r n.
             ( ADReady r, KnownNat n, RealFloat (TensorOf n r) )
          => TensorOf (1 + n) r -> TensorOf (1 + n) r
fooBuild3 v =
  tbuild1 22 $ \ix ->
    bar ( tkonst0N (tailShape $ tshape v) 1
        , tindex v [min 1 (ix + 1)] )  -- index not out of bounds

testFooBuild3 :: Assertion
testFooBuild3 =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [2,2,1,2,2] [0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,423.72976235076516,-260.41676627885636,-17.60047532855961,151.18955028869385,-1059.9668424433578,-65.00898015327623,-21.49245448729951,743.7622427949768])
    (rev' @(OR.Array 5 Double) fooBuild3 t16)

fooBuild5 :: forall r n.
             ( ADReady r, KnownNat n, RealFloat (TensorOf n r) )
          => TensorOf (1 + n) r -> TensorOf (1 + n) r
fooBuild5 v =
  let r = tsum v
      v' = tkonst0N (tailShape $ tshape v) $ tminimum0 $ tflatten v
  in tbuild1 2 $ \ix ->
       r * foo ( 3
               , 5 * r
               , r * v')
       + bar (r, tindex v [min 1 (ix + 1)])  -- index not out of bounds

testFooBuildDt :: Assertion
testFooBuildDt =
  assertEqualUpToEpsilon 1e-8
    (OR.fromList [2,2,1,2,2] [1.1033568028244503e7,74274.22833989389,-5323238.2765011545,253074.03394016018,4.14744804041263e7,242643.98750578283,-1.922371592087736e7,2.730274503834733e7,1.135709425204681e7,6924.195066252549,-5345004.080027547,255679.51406100337,3.8870981856703006e7,241810.92121468345,-1.9380955730171032e7,2.877024321777493e7])
    (revDt @(OR.Array 5 Double) fooBuild5 t16 (OR.constant [2, 2, 1, 2, 2] 42))

testFooBuild5 :: Assertion
testFooBuild5 =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [3,1,2,2,1,2,2] [-613291.6547530327,571164.2201603781,-1338602.6247083102,528876.2566682736,1699442.2143691683,2874891.369778316,-3456754.605470273,3239487.8744244366,554916.1344235454,-775449.1803684114,3072.200583200206,1165767.8436804386,-1.0686356667942494e7,-6606976.194539241,-6457671.748790982,4791868.42112978,-615556.7946425928,569660.3506343022,-1348678.1169100606,534886.9366492515,1696036.143341285,2883992.9672165257,-3456212.5353846983,3240296.690514803,629047.8398075115,-794389.5797803313,-1143.8025173051583,1177448.8083517442,-1.15145721735623e7,-6618648.839812404,-6462386.031613377,5358224.852822481,-613291.6547530327,571164.2201603781,-1338602.6247083102,528876.2566682736,1699442.2143691683,2874891.369778316,-3456754.605470273,3239487.8744244366,554916.1344235454,-775449.1803684114,3072.200583200206,1165767.8436804386,-1.0686356667942494e7,-6606976.194539241,-6457671.748790982,4791868.42112978])
    (rev' @(OR.Array 7 Double) fooBuild5 t48)

fooBuild1 :: forall r n.
             ( ADReady r, KnownNat n, RealFloat (TensorOf n r) )
          => TensorOf (1 + n) r -> TensorOf (1 + n) r
fooBuild1 v =
  let r = tsum v
      v' = tkonst0N (tailShape $ tshape v) $ tminimum0 $ tflatten v
  in tbuild1 3 $ \ix ->
       r * foo ( 3
               , 5 * r
               , r * v')
       + bar (r, tindex v [min 1 (ix + 1)])

testFooBuild1 :: Assertion
testFooBuild1 =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [2,2,1,2,2] [394056.00100873224,2652.651012139068,-190115.65273218407,9038.358355005721,1481231.4430045108,8665.8566966351,-686561.2828884773,975098.0370838332,405610.50900167174,247.29268093759174,-190893.00285812665,9131.411216464405,1388249.3520251075,8636.104329095837,-692176.9903632513,1027508.6863491047])
    (rev' @(OR.Array 5 Double) fooBuild1 t16)
{-

fooMap1 :: ADReady r => r -> TensorOf 1 r
fooMap1 r =
  let v = fooBuild1 $ tkonst0N [130] (tscalar r)
  in tmap0N (\x -> x * r + 5) v

testFooMap :: Assertion
testFooMap =
  assertEqualUpToEpsilon 1e-6
    4.438131773948916e7
    (rev @(OR.Array 1 Double) fooMap1 1.1)

testFooMap1 :: Assertion
testFooMap1 =
  assertEqualUpToEpsilon' 1e-6
    4.438131773948916e7
    (rev' @(OR.Array 1 Double) (fooMap1 . tunScalar) 1.1)

barAst :: (Numeric r, RealFloat r, RealFloat (Vector r))
       => (Ast 0 r, Ast 0 r) -> Ast 0 r
barAst (x, y) =
  let w = foo (x, y, x) * sin y
  in atan2 x w + y * w

fooNoGoAst :: forall r. (Show r, Numeric r, RealFloat r, Floating (Vector r))
           => Ast 1 r -> Ast 1 r
fooNoGoAst v =
  let r = tsum0 v
  in tbuild1 3 (\ix ->
       barAst (3.14, bar (3.14, tindex v [ix]))
       + astCond (AstBoolOp AndOp  -- TODO: overload &&, <=, >, etc.
                             [ tindex @(Ast 0 r) @1 v [ix * 2] `tleq` 0
                             , gtInt @(Ast 0 r) 6 (abs ix) ])
                 r (5 * r))
     / tslice 1 3 (tmap0N (\x -> astCond (x `tgt` r) r x) v)
     * tbuild1 3 (const 1)

testFooNoGoAst :: Assertion
testFooNoGoAst =
  let f :: ADModeAndNumTensor d r
        => ADVal d (OR.Array 1 r) -> ADVal d (OR.Array 1 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (fooNoGoAst (AstVar [5] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-6
       (OR.fromList [5] [344.3405885672822,-396.1811403813819,7.735358041386672,-0.8403418295960372,5.037878787878787])
       (rev @(OR.Array 1 Double) f
             (OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

fooNoGo :: forall r. ADReady r
        => TensorOf 1 r -> TensorOf 1 r
fooNoGo v =
  let r = tsum0 v
  in tbuild1 3 (\ix ->
       bar (3.14, bar (3.14, tindex v [ix]))
       + tcond (andBool @r (tindex @r @1 v [ix * 2] `tleq` 0)
                           (gtInt @r 6 (abs ix)))
               r (5 * r))
     / tslice 1 3 (tmap0N (\x ->
         tunScalar $ tcond (tscalar x `tgt` r) r (tscalar x)) v)
     * tbuild1 3 (const 1)

testFooNoGo :: Assertion
testFooNoGo =
  assertEqualUpToEpsilon' 1e-6
   (OR.fromList [5] [344.3405885672822,-396.1811403813819,7.735358041386672,-0.8403418295960372,5.037878787878787])
   (rev' @(OR.Array 1 Double) fooNoGo
         (OR.fromList [5] [1.1 :: Double, 2.2, 3.3, 4, 5]))

nestedBuildMap :: forall r. ADReady r => r -> TensorOf 1 r
nestedBuildMap r =
  let w = tkonst0N [4]  -- (AstIntCond (x `leqAst` 0) 3 4)
      v' = tkonst0N [177] (tscalar r) :: TensorOf 1 r
      nestedMap x = tmap0N (x /) (w (tscalar x))
      variableLengthBuild iy = tbuild1 7 (\ix -> tindex v' [ix + iy])
      doublyBuild = tbuild1 5 (tminimum0 . variableLengthBuild)
  in tmap0N (\x -> x
                  * tunScalar (tsum0
                      (tbuild1 3 (\ix -> bar ( tscalar x
                                            , tindex v' [ix]) )
                       + fooBuild1 (nestedMap x)
                       / fooMap1 x))
           ) doublyBuild

testNestedBuildMap :: Assertion
testNestedBuildMap =
  assertEqualUpToEpsilon 1e-10
    107.25984443006627
    (rev @(OR.Array 1 Double) nestedBuildMap 1.1)

testNestedBuildMap1 :: Assertion
testNestedBuildMap1 =
  assertEqualUpToEpsilon' 1e-10
    107.25984443006627
    (rev' @(OR.Array 1 Double) (nestedBuildMap . tunScalar) 1.1)

nestedSumBuild :: ADReady r => TensorOf 1 r -> TensorOf 1 r
nestedSumBuild v =
  tbuild1 13 (\ix ->
    tsum (tbuild1 4 (\ix2 ->
      flip tindex [ix2]
        (tbuild1 5 (\ _ -> tsum v)
         * tfromList
             [ tfromIntOf0 ix
             , tsum (tbuild1 9 tfromIntOf0)
             , tsum (tbuild1 6 (\_ -> tsum v))
             , tindex v [ix2]
             , tsum (tbuild1 3 (\ix7 ->
                 tsum (tkonst 5 (tfromIntOf0 ix7))))
-- dynamic shapes:
--             , tsum (tbuild1 3 (\ix7 ->
--                 tsum (tkonst0N [ix2 + 1] (tfromIntOf0 ix7))))
-- irregular array:
--             , tsum (tbuild1 3 (\ix7 ->
--                 tsum (tkonst0N [ix2 + ix7 + 1] 2.4)))
             ]))))
  + tbuild1 13 (\ix ->
      nestedBuildMap (tunScalar $ tsum0 v) `tindex` [min ix 4])

testNestedSumBuild :: Assertion
testNestedSumBuild =
  assertEqualUpToEpsilon' 1e-8
    (OR.fromList [5] [-14084.715065313612,-14084.715065313612,-14084.715065313612,-14014.775065313623,-14084.715065313612])
    (rev' @(OR.Array 1 Double) nestedSumBuild (OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

nestedBuildIndex :: forall r. ADReady r => TensorOf 1 r -> TensorOf 1 r
nestedBuildIndex v =
  tbuild1 2 $ \ix2 -> tindex @r @1 (tbuild1 3 $ \ix3 -> tindex (tbuild1 4 $ \ix4 -> tindex @r @1 v [ix4]) [ix3]) [ix2]

testNestedBuildIndex :: Assertion
testNestedBuildIndex =
  assertEqualUpToEpsilon' 1e-10
    (OR.fromList [5]  [1,1,0,0,0])
    (rev' @(OR.Array 1 Double) nestedBuildIndex (OR.fromList [5] [1.1, 2.2, 3.3, 4, -5.22]))

barRelu
  :: ( RealFloat (TensorOf n r), HasPrimal (TensorOf n r)
     , Ord (Element (PrimalOf (TensorOf n r)))
     , Fractional (Element (PrimalOf (TensorOf n r))) )
  => TensorOf n r -> TensorOf n r
barRelu x = relu1 $ bar (x, relu1 x)

testBarReluADValDt :: Assertion
testBarReluADValDt =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [] [191.20462646925841])
    (revDt @(OR.Array 0 Double) barRelu (OR.fromList [] [1.1]) 42.2)

testBarReluADVal :: Assertion
testBarReluADVal =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [] [4.5309153191767395])
    (rev @(OR.Array 0 Double) barRelu (OR.fromList [] [1.1]))

testBarReluADVal3 :: Assertion
testBarReluADVal3 =
  assertEqualUpToEpsilon 1e-10
    (OR.fromList [2, 1, 2] [4.5309153191767395,4.5302138998556,-9.39547533946234,95.29759282497125])
    (rev @(OR.Array 3 Double) barRelu (OR.fromList [2, 1, 2] [1.1, 2, 3, 4.2]))

barReluAst
  :: (KnownNat n, Numeric r, RealFloat r, Floating (Vector r))
  => Ast n r -> Ast n r
barReluAst x = reluAst1 $ bar (x, reluAst1 x)
  -- TODO; barRelu @(Ast 0 r) fails
  -- due to relu using conditionals and @>@ instead of
  -- a generalization of those that have Ast instance:

testBarReluAst0 :: Assertion
testBarReluAst0 =
  let f :: ADModeAndNumTensor d r
        => ADVal d (OR.Array 0 r) -> ADVal d (OR.Array 0 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (barReluAst (AstVar [] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [] [191.20462646925841])
       (revDt @(OR.Array 0 Double) f (OR.fromList [] [1.1]) 42.2)

testBarReluAst1 :: Assertion
testBarReluAst1 =
  let f :: ADModeAndNumTensor d r
        => ADVal d (OR.Array 1 r) -> ADVal d (OR.Array 1 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (barReluAst (AstVar [5] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [5] [4.530915319176739,-2.9573428114591314e-2,5.091137576320349,81.14126788127645,2.828924924816215])
       (rev @(OR.Array 1 Double) f (OR.fromList [5] [1.1, 2.2, 3.3, 4, 5]))

konstReluAst
  :: forall r. (Show r, Numeric r, RealFloat r, RealFloat (Vector r))
  => Ast 0 r -> Ast 0 r
konstReluAst x = tsum0 $ reluAst1 @1 $ tkonst0N [7] x

testKonstReluAst :: Assertion
testKonstReluAst =
  let f :: ADModeAndNumTensor d r
        => ADVal d (OR.Array 0 r) -> ADVal d (OR.Array 0 r)
      f x = interpretAst (IM.singleton 0 (AstVarR $ from1X x))
                         (konstReluAst (AstVar [] (AstVarName 0)))
  in assertEqualUpToEpsilon 1e-10
       (OR.fromList [] [295.4])
       (revDt @(OR.Array 0 Double) f (OR.fromList [] [1.1]) 42.2)


-- * Tests by TomS

f1 :: ADReady a => a -> a
f1 = \arg -> tunScalar $ tsum0 (tbuild1 10 (\i -> tscalar arg * tfromIntOf0 i))

testF1 :: Assertion
testF1 =
  assertEqualUpToEpsilon 1e-10
    45.0
    (rev @Double f1 1.1)

testF11 :: Assertion
testF11 =
  assertEqualUpToEpsilon' 1e-10
    45.0
    (rev' @(OR.Array 0 Double) (tscalar . f1 . tunScalar) 1.1)

f2 :: ADReady a => a -> a
f2 = \arg ->
  let fun1 i = tscalar arg * tfromIntOf0 i
      v1a = tsum0 (tbuild1 10 fun1)
      v1b = tsum0 (tbuild1 20 fun1)
      fun2 y i = tscalar y * tfromIntOf0 i
      v2a = tsum0 (tbuild1 10 (fun2 arg))
      v2b = tsum0 (tbuild1 20 (fun2 (arg + 1)))
  in tunScalar $ v1a + v1b + v2a + v2b

testF2 :: Assertion
testF2 =
  assertEqualUpToEpsilon 1e-10
    470
    (rev @Double f2 1.1)

testF21 :: Assertion
testF21 =
  assertEqualUpToEpsilon' 1e-10
    470
    (rev' @(OR.Array 0 Double) (tscalar . f2 . tunScalar) 1.1)

f3 :: (ADReady r, Tensor (r -> r), Tensor ((r -> r) -> (r -> r)))
   => TensorOf 0 r -> TensorOf 0 r
f3 arg =
  let arr1 = tbuild [10] (\i -> tscalar $ \x ->
                            x + tunScalar (tfromIntOf0 (headIndex i)))
      arr2 = tbuild [10] (\i -> tscalar $ \f -> (tunScalar $ arr1 ! i) . f)
      arr3 = tbuild [10] (\i -> tscalar $ (tunScalar $ arr2 ! i)
                                            (tunScalar $ arr1 ! i)
                                              (tunScalar arg))
  in tsum arr3

testF3 :: Assertion
testF3 =
  let _ = assertEqualUpToEpsilon' 1e-10
            470
            (rev' @(OR.Array 0 Double) f3 1.1)
  in return ()  -- dummy instance for -> and Ast rewrites don't remove -> yet

-- * Hairy tests (many by TomS as well)

braidedBuilds :: forall r. ADReady r => r -> TensorOf 2 r
braidedBuilds r =
  tbuild1 3 (\ix1 ->
    tbuild1 4 (\ix2 -> tindex @r @1 (tfromList0N [4]
                                      [tunScalar $ tfromIntOf0 ix2, 7, r, -0.2]) [ix1]))

testBraidedBuilds :: Assertion
testBraidedBuilds =
  assertEqualUpToEpsilon 1e-10
    4.0
    (rev @(OR.Array 2 Double) braidedBuilds 3.4)

testBraidedBuilds1 :: Assertion
testBraidedBuilds1 =
  assertEqualUpToEpsilon' 1e-10
    4.0
    (rev' @(OR.Array 2 Double) (braidedBuilds . tunScalar) 3.4)

recycled :: ADReady r
         => r -> TensorOf 5 r
recycled r =
  tbuild1 2 $ \_ -> tbuild1 4 $ \_ -> tbuild1 2 $ \_ -> tbuild1 3 $ \_ ->
    nestedSumBuild (tkonst0N [7] (tscalar r))

testRecycled :: Assertion
testRecycled =
  assertEqualUpToEpsilon 1e-6
    3.983629038066359e7
    (rev @(OR.Array 5 Double) recycled 1.0001)

testRecycled1 :: Assertion
testRecycled1 =
  assertEqualUpToEpsilon' 1e-6
    3.983629038066359e7
    (rev' @(OR.Array 5 Double) (recycled . tunScalar)  1.0001)

concatBuild :: ADReady r => r -> TensorOf 2 r
concatBuild r =
  tbuild1 7 (\i ->
    tappend (tappend (tbuild1 5 (\_j -> tscalar r))  -- TODO: i should work
                     (tkonst 1 (tfromIntOf0 i)))
            (tbuild1 13 (\_k -> tscalar r)))
-- TODO: reject via types or accept with type obligations:
--    tappend (tappend (tbuild1 (1 + i) (\_j -> tscalar r))  -- TODO: i should work
--                     (tkonst0N [1] (tfromIntOf0 i)))
--            (tbuild1 (13 - i) (\_k -> tscalar r)))

testConcatBuild :: Assertion
testConcatBuild =
  assertEqualUpToEpsilon 1e-10
    126.0
    (rev @(OR.Array 2 Double) concatBuild 3.4)

testConcatBuild1 :: Assertion
testConcatBuild1 =
  assertEqualUpToEpsilon' 1e-10
    126.0
    (rev' @(OR.Array 2 Double) (concatBuild . tunScalar) 3.4)

-- TODO:
_concatBuild2 :: ADReady r => r -> TensorOf 2 r
_concatBuild2 _r =
-- TODO: tbuild0N (7, 14) (\ (i,j)
  tbuild1 7 $ \i -> tbuild1 14 $ \_j ->
    -- TODO: use classes Cond and Bool: if i == j then tfromIntOf0 i else r
   tfromIntOf0 i
      -- need to prove that i + 1 + (13 - i) = 14
-}
