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

import qualified Data.Array.DynamicS as OD
import qualified Data.Array.RankedS as OR
import           Data.Bifunctor.Flip
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, Nat, sameNat, type (+))

import HordeAd.Core.Ast
import HordeAd.Core.AstFreshId
import HordeAd.Core.AstSimplify
import HordeAd.Core.AstTools
import HordeAd.Core.AstVectorize
import HordeAd.Core.Domains
import HordeAd.Core.SizedIndex
import HordeAd.Core.TensorClass

type instance IntOf (AstRanked r n) = AstInt r

type instance PrimalOf AstRanked = AstPrimalPart

type instance DualOf AstRanked = AstDualPart

instance Tensor AstRanked where
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
  tscatter sh t f = astScatter sh t (funToAstIndex f)  -- introduces new vars

  tfromList = AstFromList
  tfromVector = AstFromVector
  treplicate = AstReplicate
  tappend = AstAppend
  tslice = AstSlice
  treverse = AstReverse
  ttranspose = astTranspose
  treshape = astReshape
  tbuild1 = astBuild1Vectorize
  tgather sh t f = AstGatherZ sh t (funToAstIndex f)  -- introduces new vars

  tsumOfList l = AstSumOfList l
  tconst = AstConstant . AstPrimalPart . AstConst
  tconstBare = AstConst
  tletWrap = AstLetADShare
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.

  tconstant = astConstant
  tprimalPart = AstPrimalPart
  tdualPart = AstDualPart
  tD = AstD
  tScale (AstPrimalPart s) (AstDualPart t) = AstDualPart $ s `tmult` t

instance ConvertTensor AstDynamic AstRanked AstShapedTODO where
  tfromD = astFromDynamic
  tfromS = undefined
  dfromR r = AstDynamic r
  dfromS = undefined
  sfromR = undefined
  sfromD = undefined
  ddummy = AstDynamic AstIota
  disDummy t = case t of
    AstDynamic AstIota -> True
    _ -> False
  daddR :: forall n r. KnownNat n
        => AstRanked r n -> AstDynamic r -> AstDynamic r
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
  tregister = astRegisterFun

data AstShapedTODO r (sh :: [Nat])

instance (GoodScalar r, KnownNat n)
         => AdaptableDomains AstDynamic (Ast n r) where
  type Underlying (Ast n r) = r
  type Value (Ast n r) = Flip OR.Array r n
  toDomains = undefined
  fromDomains aInit params = case V.uncons params of
    Just (a, rest) -> Just (ttoRankedOrDummy @AstDynamic @AstRanked
                                             (tshape aInit) a, rest)
    Nothing -> Nothing

instance AdaptableDomains AstDynamic (AstDynamic r) where
  type Underlying (AstDynamic r) = r
  type Value (AstDynamic r) = OD.Array r
  toDomains = undefined
  fromDomains = undefined

instance AdaptableDomains AstDynamic (AstPrimalPart r n) where
  type Underlying (AstPrimalPart r n) = r
  type Value (AstPrimalPart r n) = r
  toDomains = undefined
  fromDomains = undefined

instance AdaptableDomains AstDynamic (AstNoVectorize r n) where
  type Underlying (AstNoVectorize r n) = r
  type Value (AstNoVectorize r n) = r
  toDomains = undefined
  fromDomains = undefined

instance AdaptableDomains AstDynamic (AstNoSimplify r n) where
  type Underlying (AstNoSimplify r n) = r
  type Value (AstNoSimplify r n) = r
  toDomains = undefined
  fromDomains = undefined

instance DomainsTensor AstDynamic AstRanked AstDomains where
  tletDomains = astLetDomainsFun
  dmkDomains = AstDomains
  dlet = astDomainsLetFun

astLetFun :: (KnownNat n, KnownNat m, ShowAst r)
          => Ast n r -> (Ast n r -> Ast m r) -> Ast m r
astLetFun a f | astIsSmall a = f a
astLetFun a f =
  let sh = shapeAst a
      (AstVarName var, ast) = funToAstR sh f
  in astLet var a ast  -- safe, because subsitution ruled out above

astLetDomainsFun
  :: forall m r. ShowAst r
  => AstDomains r
  -> (AstDomains r -> Ast m r)
  -> Ast m r
astLetDomainsFun a f =
  let genVar :: AstDynamic r -> (AstVarId, AstDynamic r)
      genVar (AstDynamic t) =
        let sh = shapeAst t
            (AstVarName var, ast) = funToAstR sh id
        in (var, AstDynamic ast)
      (vars, asts) = V.unzip $ V.map genVar (unwrapAstDomains a)
  in AstLetDomains vars a (f $ AstDomains asts)

astDomainsLetFun :: (KnownNat n, ShowAst r)
                 => Ast n r -> (Ast n r -> AstDomains r)
                 -> AstDomains r
astDomainsLetFun a f | astIsSmall a = f a
astDomainsLetFun a f =
  let sh = shapeAst a
      (AstVarName var, ast) = funToAstR sh id
  in astDomainsLet var a (f ast)  -- safe, because subsitution ruled out above

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize :: (KnownNat n, GoodScalar r)
                   => Int -> (AstInt r -> Ast n r) -> Ast (1 + n) r
astBuild1Vectorize k f = build1Vectorize k $ funToAstI f

type instance IntOf (AstPrimalPart r n) = AstInt r

type instance PrimalOf AstPrimalPart = AstPrimalPart

type instance DualOf AstPrimalPart = DummyDual

instance Tensor AstPrimalPart where
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
  tscatter sh t f = AstPrimalPart $ astScatter sh (unAstPrimalPart t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstPrimalPart . AstFromList . map unAstPrimalPart
  tfromVector = AstPrimalPart . AstFromVector . V.map unAstPrimalPart
  treplicate k = AstPrimalPart . AstReplicate k . unAstPrimalPart
  tappend u v =
    AstPrimalPart $ AstAppend (unAstPrimalPart u) (unAstPrimalPart v)
  tslice i k = AstPrimalPart . AstSlice i k . unAstPrimalPart
  treverse = AstPrimalPart . AstReverse . unAstPrimalPart
  ttranspose perm = AstPrimalPart . AstTranspose perm . unAstPrimalPart
  treshape sh = AstPrimalPart . astReshape sh . unAstPrimalPart
  tbuild1 k f = AstPrimalPart $ astBuild1Vectorize k (unAstPrimalPart . f)
  tgather sh t f = AstPrimalPart $ AstGatherZ sh (unAstPrimalPart t)
                   $ funToAstIndex f  -- this introduces new variable names

  tsumOfList l = AstPrimalPart . AstSumOfList . map unAstPrimalPart $ l
  tconst = AstPrimalPart . AstConst

  tconstant = id
  tprimalPart = id
  tdualPart _ = DummyDual
  tD u _ = u
  tScale _ _ = DummyDual

type instance IntOf (AstNoVectorize r n) = AstInt r

type instance PrimalOf AstNoVectorize = AstNoVectorize

type instance DualOf AstNoVectorize = AstDualPart

instance Tensor AstNoVectorize where
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
  tscatter sh t f = AstNoVectorize $ astScatter sh (unAstNoVectorize t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstNoVectorize . AstFromList . map unAstNoVectorize
  tfromVector = AstNoVectorize . AstFromVector . V.map unAstNoVectorize
  treplicate k = AstNoVectorize . AstReplicate k . unAstNoVectorize
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

  tsumOfList l = AstNoVectorize . AstSumOfList . map unAstNoVectorize $ l
  tconst = AstNoVectorize . AstConstant . AstPrimalPart . AstConst
  tconstBare = AstNoVectorize . AstConst

  tconstant = AstNoVectorize . astConstant . AstPrimalPart . unAstNoVectorize
  tprimalPart = id
  tdualPart = AstDualPart . unAstNoVectorize
  tD u u' = AstNoVectorize $ AstD (AstPrimalPart $ unAstNoVectorize u) u'
  tScale (AstNoVectorize s) (AstDualPart t) = AstDualPart $ s `tmult` t

type instance IntOf (AstNoSimplify r n) = AstInt r

type instance PrimalOf AstNoSimplify = AstNoSimplify

type instance DualOf AstNoSimplify = AstDualPart

instance Tensor AstNoSimplify where
  tlet a f =
    AstNoSimplify
    $ astLetFunUnSimp (unAstNoSimplify a) (unAstNoSimplify . f . AstNoSimplify)

  tshape = shapeAst . unAstNoSimplify
  tminIndex0 = AstMinIndex1 . AstPrimalPart . unAstNoSimplify
  tmaxIndex0 = AstMaxIndex1 . AstPrimalPart . unAstNoSimplify
  tfloor = AstIntFloor . AstPrimalPart . unAstNoSimplify

  tindex v ix = AstNoSimplify $ AstIndexZ (unAstNoSimplify v) ix
  tsum = AstNoSimplify . AstSum . unAstNoSimplify
  tfromIndex0 i = AstNoSimplify $ AstConstant $ AstPrimalPart
                  $ AstIndexZ AstIota (singletonIndex i)
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstNoSimplify $ AstScatter sh (unAstNoSimplify t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstNoSimplify . AstFromList . map unAstNoSimplify
  tfromVector = AstNoSimplify . AstFromVector . V.map unAstNoSimplify
  treplicate k = AstNoSimplify . AstReplicate k . unAstNoSimplify
  tappend u v =
    AstNoSimplify $ AstAppend (unAstNoSimplify u) (unAstNoSimplify v)
  tslice i k = AstNoSimplify . AstSlice i k . unAstNoSimplify
  treverse = AstNoSimplify . AstReverse . unAstNoSimplify
  ttranspose perm = AstNoSimplify . AstTranspose perm . unAstNoSimplify
  treshape sh = AstNoSimplify . AstReshape sh . unAstNoSimplify
  tbuild1 k f = AstNoSimplify $ astBuild1Vectorize k (unAstNoSimplify . f)
  tgather sh t f = AstNoSimplify $ AstGatherZ sh (unAstNoSimplify t)
                   $ funToAstIndex f  -- this introduces new variable names

  tsumOfList l = AstNoSimplify . AstSumOfList . map unAstNoSimplify $ l
  tconst = AstNoSimplify . AstConstant . AstPrimalPart . AstConst
  tconstBare = AstNoSimplify . AstConst

  tconstant = AstNoSimplify . astConstant . AstPrimalPart . unAstNoSimplify
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  tprimalPart = id
  tdualPart = AstDualPart . unAstNoSimplify
  tD u u' = AstNoSimplify $ AstD (AstPrimalPart $ unAstNoSimplify u) u'
  tScale (AstNoSimplify s) (AstDualPart t) = AstDualPart $ s `tmult` t

astLetFunUnSimp :: (KnownNat n, KnownNat m, ShowAst r)
                => Ast n r -> (Ast n r -> Ast m r) -> Ast m r
astLetFunUnSimp a f =
  let sh = shapeAst a
      (AstVarName var, ast) = funToAstR sh f
  in AstLet var a ast
