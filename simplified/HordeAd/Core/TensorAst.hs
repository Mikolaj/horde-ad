{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | 'Tensor' class instances for 'Ast' terms. Some of these instances
-- vectorize any terms starting with 'build1' and so eliminated the constructor.
module HordeAd.Core.TensorAst
  (
  ) where

import Prelude

import           Data.IORef.Unboxed (Counter, atomicAddCounter_, newCounter)
import           Data.List (foldl')
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Strict.Vector as Data.Vector
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, sameNat, type (+))
import           System.IO.Unsafe (unsafePerformIO)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstVectorize
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass

instance ShowAstSimplify r
         => Tensor (Ast0 r) where
  type TensorOf n (Ast0 r) = Ast n r
  type IntOf (Ast0 r) = AstInt r

  tlet a f = astLetFun a f

  tshape = shapeAst
  tminIndex0 = AstMinIndex1 . AstPrimalPart
  tmaxIndex0 = AstMaxIndex1 . AstPrimalPart
  tfloor = AstIntFloor . AstPrimalPart

  tindex = AstIndexZ
  tsum = AstSum
  tfromIndex0 i = AstConstant $ AstPrimalPart
                  $ AstIndexZ AstIota (singletonIndex i)
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstScatter sh t (funToAstIndex f)  -- introduces new vars

  tfromList = AstFromList
  tfromVector = AstFromVector
  tkonst = AstKonst
  tappend = AstAppend
  tslice = AstSlice
  treverse = AstReverse
  ttranspose = AstTranspose
  treshape = astReshape
  tbuild1 = astBuild1Fun
  tgather sh t f = AstGatherZ sh t (funToAstIndex f)  -- introduces new vars

  tscalar = unAst0
  tunScalar = Ast0
    -- due to injective type families, we have to distinguish Ast0 and Ast 0

  tsumOfList l = AstSumOfList l

  type ScalarOf (Ast0 r) = r
  type Primal (Ast0 r) = AstPrimalPart 0 r
  type DualOf n (Ast0 r) = AstDualPart n r
  tconst = AstConstant . AstPrimalPart . AstConst
  tconstant = AstConstant
  tscale0 (AstPrimalPart r) (Ast0 t) = Ast0 (r * t)
  tprimalPart = AstPrimalPart
  tdualPart = AstDualPart
  tD = AstD
  tScale (AstPrimalPart s) (AstDualPart t) = AstDualPart $ s `tmult` t

  tlet0 = astLet0Fun
  tletR = astLetRFun
  tregister = astRegisterFun
  tletWrap l u =
    let bindToLet g (i, AstDynamic t) = AstLet (intToAstVarId i) t g
    in foldl' bindToLet u l

  tfromD = astFromDynamic
  tletVectorOfDynamic a f = astLetVectorOfDynamicFun a f

instance DynamicTensor (Ast0 r) where
  type DTensorOf (Ast0 r) = AstDynamic r
  dfromR r = AstDynamic r

instance ShowAst r
         => DummyTensor (Ast0 r) where
  ddummy = AstDynamic AstIota
  disDummy t = case t of
    AstDynamic AstIota -> True
    _ -> False
  daddR :: forall n q. (KnownNat n, q ~ (Ast0 r))
        => TensorOf n q -> DTensorOf q -> DTensorOf q
  daddR r (AstDynamic AstIota) = AstDynamic r
  daddR r (AstDynamic @n2 (AstSumOfList l)) =
    case sameNat (Proxy @n) (Proxy @n2) of
      Just Refl -> AstDynamic (AstSumOfList (r : l))
      _ -> error "daddR: type mismatch"
  daddR r (AstDynamic @n2 v) =
    case sameNat (Proxy @n) (Proxy @n2) of
      Just Refl -> AstDynamic (AstSumOfList [r, v])
      _ -> error "daddR: type mismatch"
  dshape (AstDynamic v) = shapeToList $ shapeAst v

astLetFun :: (KnownNat n, ShowAstSimplify r)
          => Ast n r -> (Ast n r -> Ast m r) -> Ast m r
astLetFun a@AstVar{} f = f a
astLetFun a f =
  let sh = tshape a
      (AstVarName var, ast) = funToAstR sh f
  in AstLet var a ast

astLetVectorOfDynamicFun
  :: ShowAstSimplify r
  => Data.Vector.Vector (AstDynamic r)
  -> (Data.Vector.Vector (AstDynamic r) -> Ast m r)
  -> Ast m r
astLetVectorOfDynamicFun a f =
  let genVar (AstDynamic t) =
        let sh = tshape t
            (AstVarName var, ast) = funToAstR sh id
        in (var, AstDynamic ast)
      (vars, asts) = V.unzip $ V.map genVar a
  in AstLetVectorOfDynamic vars (AstVectorOfDynamic a) (f asts)

unsafeGlobalCounter :: Counter
{-# NOINLINE unsafeGlobalCounter #-}
unsafeGlobalCounter = unsafePerformIO (newCounter 100000000)

unsafeGetFreshId :: IO Int
{-# INLINE unsafeGetFreshId #-}
unsafeGetFreshId = atomicAddCounter_ unsafeGlobalCounter 1

astLet0Fun :: Ast0 r -> Ast0 r
{-# NOINLINE astLet0Fun #-}
astLet0Fun t@(Ast0 AstLetGlobal{}) = t
astLet0Fun t = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! Ast0 $ AstLetGlobal (NodeId n) (unAst0 t)

astLetRFun :: Ast m r -> Ast m r
{-# NOINLINE astLetRFun #-}
astLetRFun t@AstLetGlobal{} = t
astLetRFun t = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return $! AstLetGlobal (NodeId n) t

astRegisterFun :: (ShowAst r, KnownNat n)
               => Ast n r -> [(Int, AstDynamic r)]
               -> ([(Int, AstDynamic r)], Ast n r)
astRegisterFun r@AstVar{} l = (l, r)
astRegisterFun r@AstLetGlobal{} l = (l, r)
astRegisterFun r l = unsafePerformIO $ do
  n <- unsafeGetFreshId
  return ((n, AstDynamic r) : l, AstVar (shapeAst r) (intToAstVarId n))

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Fun :: (KnownNat n, ShowAstSimplify r)
             => Int -> (AstInt r -> Ast n r) -> Ast (1 + n) r
astBuild1Fun k f = build1Vectorize k $ funToAstI f

instance ShowAstSimplify r
         => Tensor (AstPrimalPart 0 r) where
  type TensorOf n (AstPrimalPart 0 r) = AstPrimalPart n r
  type IntOf (AstPrimalPart 0 r) = AstInt r

  tlet a f =
    AstPrimalPart
    $ astLetFun (unAstPrimalPart a) (unAstPrimalPart . f . AstPrimalPart)

  tshape = shapeAst . unAstPrimalPart
  tminIndex0 = AstMinIndex1
  tmaxIndex0 = AstMaxIndex1
  tfloor = AstIntFloor

  tindex v ix = AstPrimalPart $ AstIndexZ (unAstPrimalPart v) ix
  tsum = AstPrimalPart . AstSum . unAstPrimalPart
  tfromIndex0 i = AstPrimalPart
                  $ AstIndexZ AstIota (singletonIndex i)
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstPrimalPart $ AstScatter sh (unAstPrimalPart t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstPrimalPart . AstFromList . map unAstPrimalPart
  tfromVector = AstPrimalPart . AstFromVector . V.map unAstPrimalPart
  tkonst k = AstPrimalPart . AstKonst k . unAstPrimalPart
  tappend u v =
    AstPrimalPart $ AstAppend (unAstPrimalPart u) (unAstPrimalPart v)
  tslice i k = AstPrimalPart . AstSlice i k . unAstPrimalPart
  treverse = AstPrimalPart . AstReverse . unAstPrimalPart
  ttranspose perm = AstPrimalPart . AstTranspose perm . unAstPrimalPart
  treshape sh = AstPrimalPart . astReshape sh . unAstPrimalPart
  tbuild1 k f = AstPrimalPart $ astBuild1Fun k (unAstPrimalPart . f)
  tgather sh t f = AstPrimalPart $ AstGatherZ sh (unAstPrimalPart t)
                   $ funToAstIndex f  -- this introduces new variable names

  tscalar = id
  tunScalar = id
    -- identifying AstPrimalPart 0 with primal part scalars lets us avoid
    -- adding a lot of constraints to ADReady

  tsumOfList l = AstPrimalPart . AstSumOfList . map unAstPrimalPart $ l

  type ScalarOf (AstPrimalPart 0 r) = r
  type Primal (AstPrimalPart 0 r) = AstPrimalPart 0 r
  type DualOf n (AstPrimalPart 0 r) = ()
  tconst = AstPrimalPart . AstConst
  tconstant = id
  tscale0 r d = r * d
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u
  tScale _ _ = ()

  tlet0 = AstPrimalPart . astLetRFun . unAstPrimalPart
  tletR = AstPrimalPart . astLetRFun . unAstPrimalPart
  tregister = undefined

  tfromD = undefined
  tletVectorOfDynamic = undefined

instance ShowAstSimplify r
         => Tensor (AstNoVectorize 0 r) where
  type TensorOf n (AstNoVectorize 0 r) = AstNoVectorize n r
  type IntOf (AstNoVectorize 0 r) = AstInt r

  tlet a f =
    AstNoVectorize
    $ astLetFun (unAstNoVectorize a) (unAstNoVectorize . f . AstNoVectorize)

  tshape = shapeAst . unAstNoVectorize
  tminIndex0 = AstMinIndex1 . AstPrimalPart . unAstNoVectorize
  tmaxIndex0 = AstMaxIndex1 . AstPrimalPart . unAstNoVectorize
  tfloor = AstIntFloor . AstPrimalPart . unAstNoVectorize

  tindex v ix = AstNoVectorize $ AstIndexZ (unAstNoVectorize v) ix
  tsum = AstNoVectorize . AstSum . unAstNoVectorize
  tfromIndex0 i = AstNoVectorize $ AstConstant $ AstPrimalPart
                  $ AstIndexZ AstIota (singletonIndex i)
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstNoVectorize $ AstScatter sh (unAstNoVectorize t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstNoVectorize . AstFromList . map unAstNoVectorize
  tfromVector = AstNoVectorize . AstFromVector . V.map unAstNoVectorize
  tkonst k = AstNoVectorize . AstKonst k . unAstNoVectorize
  tappend u v =
    AstNoVectorize $ AstAppend (unAstNoVectorize u) (unAstNoVectorize v)
  tslice i k = AstNoVectorize . AstSlice i k . unAstNoVectorize
  treverse = AstNoVectorize . AstReverse . unAstNoVectorize
  ttranspose perm = AstNoVectorize . AstTranspose perm . unAstNoVectorize
  treshape sh = AstNoVectorize . astReshape sh . unAstNoVectorize
  tbuild1 k f = AstNoVectorize $ AstBuild1 k
                $ funToAstI  -- this introduces new variable names
                $ unAstNoVectorize . f
  tgather sh t f = AstNoVectorize $ AstGatherZ sh (unAstNoVectorize t)
                   $ funToAstIndex f  -- this introduces new variable names

  tscalar = id
  tunScalar = id

  tsumOfList l = AstNoVectorize . AstSumOfList . map unAstNoVectorize $ l

  type ScalarOf (AstNoVectorize 0 r) = r
  type Primal (AstNoVectorize 0 r) = AstNoVectorize 0 r
  type DualOf n (AstNoVectorize 0 r) = AstDualPart n r
  tconst = AstNoVectorize . AstConstant . AstPrimalPart . AstConst
  tconstant = AstNoVectorize . AstConstant . AstPrimalPart . unAstNoVectorize
  tscale0 r d = r * d
  tprimalPart = id
  tdualPart = AstDualPart . unAstNoVectorize
  tD u u' = AstNoVectorize $ AstD (AstPrimalPart $ unAstNoVectorize u) u'
  tScale (AstNoVectorize s) (AstDualPart t) = AstDualPart $ s `tmult` t

  tlet0 = AstNoVectorize . astLetRFun . unAstNoVectorize
  tletR = AstNoVectorize . astLetRFun . unAstNoVectorize
  tregister = undefined

  tfromD = undefined
  tletVectorOfDynamic = undefined
