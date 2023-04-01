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

import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))

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
  tfromIndex0 = AstConstant . AstPrimalPart . AstConstInt0
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
  type DynamicTensor (Ast0 r) = AstDynamic r
  tdummyD = AstDynamicDummy
  tisDummyD t = case t of
    AstDynamicDummy -> True
    _ -> False
  taddD = AstDynamicPlus
  tshapeD t = case t of
    AstDynamicDummy -> []
    AstDynamicPlus t1 _t2 -> tshapeD t1
    AstDynamicFrom v -> shapeToList $ shapeAst v
    AstDynamicVar sh _ -> shapeToList sh
  tfromD = astFromDynamic
  tfromR = AstDynamicFrom

astLetFun :: (KnownNat n, ShowAstSimplify r)
          => Ast n r -> (Ast n r -> Ast m r) -> Ast m r
astLetFun a f =
  let sh = tshape a
      (AstVarName var, ast) = funToAstR sh f
  in AstLet var a ast

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
  tfromIndex0 = AstPrimalPart . AstConstInt0
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstPrimalPart $ AstScatter sh (unAstPrimalPart t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstPrimalPart . AstFromList . map unAstPrimalPart
  tfromVector = AstPrimalPart . AstFromVector . V.map unAstPrimalPart
  tkonst k = AstPrimalPart . AstKonst k . unAstPrimalPart
  tappend u v =
    AstPrimalPart $ AstAppend (unAstPrimalPart u) (unAstPrimalPart v)
  tslice i k = AstPrimalPart . AstSlice i k  . unAstPrimalPart
  treverse = AstPrimalPart . AstReverse . unAstPrimalPart
  ttranspose perm = AstPrimalPart . AstTranspose perm . unAstPrimalPart
  treshape sh = AstPrimalPart . astReshape sh  . unAstPrimalPart
  tbuild1 k f = AstPrimalPart $ astBuild1Fun k (unAstPrimalPart . f)
  tgather sh t f = AstPrimalPart $ AstGatherZ sh (unAstPrimalPart t)
                   $ funToAstIndex f  -- this introduces new variable names

  tscalar = id
  tunScalar = id
    -- identifying AstPrimalPart 0 with primal part scalars lets us avoid
    -- adding a lot of constraints to ADReady

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
  -- TODO: if ever used, define, if not, use an Error type
  type DynamicTensor (AstPrimalPart 0 r) = Maybe r
  tdummyD = undefined
  tisDummyD = undefined
  taddD = undefined
  tshapeD = undefined
  tfromD = undefined
  tfromR = undefined

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
  tfromIndex0 = AstNoVectorize . AstConstInt0
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstNoVectorize $ AstScatter sh (unAstNoVectorize t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstNoVectorize . AstFromList . map unAstNoVectorize
  tfromVector = AstNoVectorize . AstFromVector . V.map unAstNoVectorize
  tkonst k = AstNoVectorize . AstKonst k . unAstNoVectorize
  tappend u v =
    AstNoVectorize $ AstAppend (unAstNoVectorize u) (unAstNoVectorize v)
  tslice i k = AstNoVectorize . AstSlice i k  . unAstNoVectorize
  treverse = AstNoVectorize . AstReverse . unAstNoVectorize
  ttranspose perm = AstNoVectorize . AstTranspose perm . unAstNoVectorize
  treshape sh = AstNoVectorize . astReshape sh  . unAstNoVectorize
  tbuild1 k f = AstNoVectorize $ AstBuild1 k
                $ funToAstI  -- this introduces new variable names
                $ unAstNoVectorize . f
  tgather sh t f = AstNoVectorize $ AstGatherZ sh (unAstNoVectorize t)
                   $ funToAstIndex f  -- this introduces new variable names

  tscalar = id
  tunScalar = id

  type ScalarOf (AstNoVectorize 0 r) = r
  type Primal (AstNoVectorize 0 r) = AstNoVectorize 0 r
  type DualOf n (AstNoVectorize 0 r) = ()
  tconst = AstNoVectorize . AstConst
  tconstant = id
  tscale0 r d = r * d
  tprimalPart = id
  tdualPart _ = ()
  tD u _ = u
  tScale _ _ = ()
  -- TODO: if ever used, define, if not, use an Error type
  type DynamicTensor (AstNoVectorize 0 r) = Either r r
  tdummyD = undefined
  tisDummyD = undefined
  taddD = undefined
  tshapeD = undefined
  tfromD = undefined
  tfromR = undefined
