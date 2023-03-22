{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Vectorization of the build operation in Ast.
module HordeAd.Core.TensorAst
  (
  ) where

import Prelude

import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           Numeric.LinearAlgebra (Numeric, Vector)

import HordeAd.Core.Ast
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstVectorize
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass

-- * Ast instances of Tensor (and Primal) that use vectorization

instance (Num (Vector r), Show r, Numeric r)
         => Tensor (Ast0 r) where
  type TensorOf n (Ast0 r) = Ast n r
  type IntOf (Ast0 r) = AstInt r

  tshape = shapeAst
  tminIndex0 = AstMinIndex1
  tmaxIndex0 = AstMaxIndex1
  tfloor = AstIntFloor

  tindex = AstIndexZ
  tsum = AstSum
  tfromIndex0 = AstConstant . AstPrimalPart . AstConstInt
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstScatter sh t (funToAstIndex f)  -- introduces new vars

  tfromList = AstFromList
  tfromVector = AstFromVector
  tkonst = AstKonst
  tappend = AstAppend
  tslice = AstSlice
  treverse = AstReverse
  ttranspose = AstTranspose
  treshape = AstReshape
  tbuild1 = astBuild1
  tgather sh t f = AstGatherZ sh t (funToAstIndex f)  -- introduces new vars

  tscalar = unAst0
  tunScalar = Ast0

  type ScalarOf (Ast0 r) = r
  type Primal (Ast0 r) = AstPrimalPart 0 r
  type DualOf n (Ast0 r) = ()  -- TODO: data AstDualPart: dAdd, dkonst1
  tconst = AstConstant . AstPrimalPart . AstConst
  tconstant = AstConstant
  tscale0 (AstPrimalPart r) (Ast0 t) = Ast0 (r * t)
  tprimalPart = AstPrimalPart
  tdualPart = error "TODO"
  tD = error "TODO"
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
  tfromR = AstDynamicFrom
  tfromD = AstFromDynamic

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1 :: (KnownNat n, Show r, Numeric r, Num (Vector r))
          => Int -> (AstInt r -> Ast n r) -> Ast (1 + n) r
astBuild1 k f = build1Vectorize k $ funToAstI f

instance (Num (Vector r), Show r, Numeric r)
         => Tensor (AstPrimalPart 0 r) where
  type TensorOf n (AstPrimalPart 0 r) = AstPrimalPart n r
  type IntOf (AstPrimalPart 0 r) = AstInt r

  tshape = shapeAst . unAstPrimalPart
  tminIndex0 = AstMinIndex1 . unAstPrimalPart
  tmaxIndex0 = AstMaxIndex1 . unAstPrimalPart
  tfloor = AstIntFloor . unAstPrimalPart

  tindex v ix = AstPrimalPart $ AstIndexZ (unAstPrimalPart v) ix
  tsum = AstPrimalPart . AstSum . unAstPrimalPart
  tfromIndex0 = AstPrimalPart . AstConstInt
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
  treshape sh = AstPrimalPart . AstReshape sh  . unAstPrimalPart
  tbuild1 k f = AstPrimalPart $ AstBuild1 k
                $ funToAstI  -- this introduces new variable names
                $ unAstPrimalPart . f
                -- TODO: $ AstConstant . f
                -- that's the correct one, but unvectorized tests fail with it
  tgather sh t f = AstPrimalPart $ AstGatherZ sh (unAstPrimalPart t)
                   $ funToAstIndex f  -- this introduces new variable names

  tscalar = id
  tunScalar = id

  type ScalarOf (AstPrimalPart 0 r) = r
  type Primal (AstPrimalPart 0 r) = AstPrimalPart 0 r
  type DualOf n (AstPrimalPart 0 r) = ()
  tconst = AstPrimalPart . AstConst
  tconstant = AstPrimalPart . AstConstant
  tscale0 (AstPrimalPart r) (AstPrimalPart t) = AstPrimalPart (r * t)
  tprimalPart = id
  tdualPart = error "TODO"
  tD = error "TODO"
  -- TODO: if ever used, define, if not, use an Error type
  type DynamicTensor (AstPrimalPart 0 r) = Maybe r
  tdummyD = undefined
  tisDummyD = undefined
  taddD = undefined
  tshapeD = undefined
  tfromR = undefined
  tfromD = undefined
