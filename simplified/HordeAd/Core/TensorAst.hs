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

import qualified Data.Array.Shape as OS
import           Data.Bifunctor.Clown
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.AstVectorize
import           HordeAd.Core.ShapedList (ShapedList (..))
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorClass
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape)

type instance RankedOf (Clown AstDynamic) = AstRanked

type instance ShapedOf (Clown AstDynamic) = AstShaped

type instance IntOf AstRanked = AstInt

type instance PrimalOf AstRanked = AstPrimalPart

type instance DualOf AstRanked = AstDualPart

type instance RankedOf AstRanked = AstRanked

type instance ShapedOf AstRanked = AstShaped

instance RankedTensor AstRanked where
  tlet a f = astLetFun a f

  tshape = shapeAst
  tminIndex0 = AstMinIndex1 . AstPrimalPart
  tmaxIndex0 = AstMaxIndex1 . AstPrimalPart
  tfloor = AstIntFloor . AstPrimalPart

  tindex = AstIndex
  tsum = AstSum
  tfromIndex0 i = AstConstant $ AstPrimalPart
                  $ AstIndex AstIota (singletonIndex i)
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
  tgather sh t f = AstGather sh t (funToAstIndex f)  -- introduces new vars
  tcast = AstCast

  tsumOfList = AstSumOfList
  tconst = AstConstant . AstPrimalPart . AstConst
  tconstBare = AstConst
  tletWrap = AstLetADShare
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  raddDynamic :: forall n r. (GoodScalar r, KnownNat n)
              => AstRanked r n -> DynamicExists AstDynamic
              -> DynamicExists AstDynamic
  raddDynamic r (DynamicExists @_ @r2 d) = DynamicExists $
    if disDummy @AstRanked d then AstRToD r
    else case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> case d of
        AstRToD AstIota -> AstRToD r
        AstRToD @n2 (AstSumOfList l) ->
          case sameNat (Proxy @n) (Proxy @n2) of
            Just Refl -> AstRToD (AstSumOfList (r : l))
            _ -> error "raddDynamic: type mismatch"
        AstRToD @n2 v ->
          case sameNat (Proxy @n) (Proxy @n2) of
            Just Refl -> AstRToD (AstSumOfList [r, v])
            _ -> error "raddDynamic: type mismatch"
        AstSToD AstIotaS -> AstRToD r
        AstSToD @sh2 (AstSumOfListS l) ->
          case matchingRank @sh2 @n of
            Just Refl -> AstSToD (AstSumOfListS (AstRToS r : l))
            _ -> error "raddDynamic: type mismatch"
        AstSToD @sh2 v ->
          case matchingRank @sh2 @n of
            Just Refl -> AstSToD (AstSumOfListS [AstRToS r, v])
            _ -> error "raddDynamic: type mismatch"
      _ -> error "raddDynamic: type mismatch"
  tregister = astRegisterFun

  tconstant = astConstant
  tprimalPart = AstPrimalPart
  tdualPart = AstDualPart
  tD = AstD
  tScale (AstPrimalPart s) (AstDualPart t) = AstDualPart $ s `tmult` t

instance ConvertTensor AstRanked AstShaped where
  tfromD = astFromDynamic
  tfromS (AstVarS @sh var) =
    let sh = OS.shapeT @sh
    in case someNatVal $ toInteger $ length sh of
      Just (SomeNat @p _proxy) ->
        gcastWith (unsafeCoerce Refl :: OS.Rank sh :~: p) $
        AstVar (listShapeToShape sh) var
      Nothing -> error "tfromS: impossible someNatVal error"
  tfromS (AstRToS t) = t
  tfromS t = AstSToR t
--  dfromR (AstDToR t) = t
  dfromR t = AstRToD t
--  dfromS (AstDToS t) = t
  dfromS t = AstSToD t
  sfromR :: forall sh r. (OS.Shape sh, KnownNat (OS.Rank sh))
         => AstRanked r (OS.Rank sh) -> AstShaped r sh
  sfromR (AstVar _sh var) = AstVarS var
  sfromR (AstSToR @sh1 t) =
    case sameShape @sh1 @sh of
      Just Refl -> t
      _ -> error "sfromR: different ranks in SToD(DToS)"
  sfromR t = AstRToS t
  sfromD = astFromDynamicS
  ddummy = AstRToD AstIota
  disDummy t = case t of
    AstRToD AstIota -> True
    AstSToD AstIotaS -> True
    _ -> False
  dshape (AstRToD v) = shapeToList $ shapeAst v
  dshape (AstSToD @sh _) = OS.shapeT @sh

instance DomainsTensor AstRanked AstShaped AstDomains where
  dmkDomains = AstDomains
  -- The operations below, for this instance, are not used ATM.
  -- They may be used once trev is a method of Tensor.
  rletDomainsOf = astLetDomainsFun
  rletToDomainsOf = astDomainsLetFun
  sletDomainsOf = undefined
  sletToDomainsOf = undefined

astLetFun :: (KnownNat n, KnownNat m, GoodScalar r, GoodScalar r2)
          => AstRanked r n -> (AstRanked r n -> AstRanked r2 m)
          -> AstRanked r2 m
astLetFun a f | astIsSmall True a = f a
astLetFun a f =
  let sh = shapeAst a
      (AstVarName var, ast) = funToAstR sh f
  in astLet var a ast  -- safe, because subsitution ruled out above

astLetDomainsFun
  :: forall m r. AstDomains -> (AstDomains -> AstRanked r m) -> AstRanked r m
astLetDomainsFun a f =
  let genVar :: DynamicExists AstDynamic -> (AstVarId, DynamicExists AstDynamic)
      genVar (DynamicExists @_ @r2 (AstRToD t)) =
        let sh = shapeAst t
            (AstVarName var, ast) = funToAstR sh id
        in (var, DynamicExists @AstDynamic @r2 $ AstRToD ast)
      genVar (DynamicExists @_ @r2 (AstSToD @sh _t)) =
        let (AstVarName var, ast) = funToAstS @sh id
        in (var, DynamicExists @AstDynamic @r2 $ AstSToD ast)
      (vars, asts) = V.unzip $ V.map genVar (unwrapAstDomains a)
  in AstLetDomains vars a (f $ AstDomains asts)

astDomainsLetFun :: (KnownNat n, GoodScalar r)
                 => AstRanked r n -> (AstRanked r n -> AstDomains)
                 -> AstDomains
astDomainsLetFun a f | astIsSmall True a = f a
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
                   => Int -> (AstInt -> AstRanked r n) -> AstRanked r (1 + n)
astBuild1Vectorize k f = build1Vectorize k $ funToAstI f

type instance IntOf AstPrimalPart = AstInt

type instance PrimalOf AstPrimalPart = AstPrimalPart

type instance DualOf AstPrimalPart = DummyDual

type instance RankedOf AstPrimalPart = AstPrimalPart

type instance ShapedOf AstPrimalPart = AstPrimalPartS

instance RankedTensor AstPrimalPart where
  tlet a f =
    AstPrimalPart
    $ astLetFun (unAstPrimalPart a) (unAstPrimalPart . f . AstPrimalPart)

  tshape = shapeAst . unAstPrimalPart
  tminIndex0 = AstMinIndex1
  tmaxIndex0 = AstMaxIndex1
  tfloor = AstIntFloor

  tindex v ix = AstPrimalPart $ AstIndex (unAstPrimalPart v) ix
  tsum = AstPrimalPart . AstSum . unAstPrimalPart
  tfromIndex0 i = AstPrimalPart
                  $ AstIndex AstIota (singletonIndex i)
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstPrimalPart $ astScatter sh (unAstPrimalPart t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstPrimalPart . AstFromList . map unAstPrimalPart
  tfromVector = AstPrimalPart . AstFromVector . V.map unAstPrimalPart
  treplicate k = AstPrimalPart . AstReplicate k . unAstPrimalPart
  tappend u v =
    AstPrimalPart $ AstAppend (unAstPrimalPart u) (unAstPrimalPart v)
  tslice i n = AstPrimalPart . AstSlice i n . unAstPrimalPart
  treverse = AstPrimalPart . AstReverse . unAstPrimalPart
  ttranspose perm = AstPrimalPart . AstTranspose perm . unAstPrimalPart
  treshape sh = AstPrimalPart . astReshape sh . unAstPrimalPart
  tbuild1 k f = AstPrimalPart $ astBuild1Vectorize k (unAstPrimalPart . f)
  tgather sh t f = AstPrimalPart $ AstGather sh (unAstPrimalPart t)
                   $ funToAstIndex f  -- this introduces new variable names
  tcast = AstPrimalPart . AstCast . unAstPrimalPart

  tsumOfList = AstPrimalPart . AstSumOfList . map unAstPrimalPart
  tconst = AstPrimalPart . AstConst
  raddDynamic = undefined

  tconstant = id
  tprimalPart = id
  tdualPart _ = DummyDual
  tD u _ = u
  tScale _ _ = DummyDual

type instance IntOf AstNoVectorize = AstInt

type instance PrimalOf AstNoVectorize = AstNoVectorize

type instance DualOf AstNoVectorize = AstDualPart

type instance RankedOf AstNoVectorize = AstNoVectorize

type instance ShapedOf AstNoVectorize = AstShaped

instance RankedTensor AstNoVectorize where
  tlet a f =
    AstNoVectorize
    $ astLetFun (unAstNoVectorize a) (unAstNoVectorize . f . AstNoVectorize)

  tshape = shapeAst . unAstNoVectorize
  tminIndex0 = AstMinIndex1 . AstPrimalPart . unAstNoVectorize
  tmaxIndex0 = AstMaxIndex1 . AstPrimalPart . unAstNoVectorize
  tfloor = AstIntFloor . AstPrimalPart . unAstNoVectorize

  tindex v ix = AstNoVectorize $ AstIndex (unAstNoVectorize v) ix
  tsum = AstNoVectorize . AstSum . unAstNoVectorize
  tfromIndex0 i = AstNoVectorize $ AstConstant $ AstPrimalPart
                  $ AstIndex AstIota (singletonIndex i)
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstNoVectorize $ astScatter sh (unAstNoVectorize t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstNoVectorize . AstFromList . map unAstNoVectorize
  tfromVector = AstNoVectorize . AstFromVector . V.map unAstNoVectorize
  treplicate k = AstNoVectorize . AstReplicate k . unAstNoVectorize
  tappend u v =
    AstNoVectorize $ AstAppend (unAstNoVectorize u) (unAstNoVectorize v)
  tslice i n = AstNoVectorize . AstSlice i n . unAstNoVectorize
  treverse = AstNoVectorize . AstReverse . unAstNoVectorize
  ttranspose perm = AstNoVectorize . AstTranspose perm . unAstNoVectorize
  treshape sh = AstNoVectorize . astReshape sh . unAstNoVectorize
  tbuild1 k f = AstNoVectorize $ AstBuild1 k
                $ funToAstI  -- this introduces new variable names
                $ unAstNoVectorize . f
  tgather sh t f = AstNoVectorize $ AstGather sh (unAstNoVectorize t)
                   $ funToAstIndex f  -- this introduces new variable names
  tcast = AstNoVectorize . AstCast . unAstNoVectorize

  tsumOfList = AstNoVectorize . AstSumOfList . map unAstNoVectorize
  tconst = AstNoVectorize . AstConstant . AstPrimalPart . AstConst
  tconstBare = AstNoVectorize . AstConst
  raddDynamic = undefined

  tconstant = AstNoVectorize . astConstant . AstPrimalPart . unAstNoVectorize
  tprimalPart = id
  tdualPart = AstDualPart . unAstNoVectorize
  tD u u' = AstNoVectorize $ AstD (AstPrimalPart $ unAstNoVectorize u) u'
  tScale (AstNoVectorize s) (AstDualPart t) = AstDualPart $ s `tmult` t

type instance IntOf AstNoSimplify = AstInt

type instance PrimalOf AstNoSimplify = AstNoSimplify

type instance DualOf AstNoSimplify = AstDualPart

type instance RankedOf AstNoSimplify = AstNoSimplify

type instance ShapedOf AstNoSimplify = AstShaped

instance RankedTensor AstNoSimplify where
  tlet a f =
    AstNoSimplify
    $ astLetFunUnSimp (unAstNoSimplify a) (unAstNoSimplify . f . AstNoSimplify)

  tshape = shapeAst . unAstNoSimplify
  tminIndex0 = AstMinIndex1 . AstPrimalPart . unAstNoSimplify
  tmaxIndex0 = AstMaxIndex1 . AstPrimalPart . unAstNoSimplify
  tfloor = AstIntFloor . AstPrimalPart . unAstNoSimplify

  tindex v ix = AstNoSimplify $ AstIndex (unAstNoSimplify v) ix
  tsum = AstNoSimplify . AstSum . unAstNoSimplify
  tfromIndex0 i = AstNoSimplify $ AstConstant $ AstPrimalPart
                  $ AstIndex AstIota (singletonIndex i)
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = AstNoSimplify $ AstScatter sh (unAstNoSimplify t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = AstNoSimplify . AstFromList . map unAstNoSimplify
  tfromVector = AstNoSimplify . AstFromVector . V.map unAstNoSimplify
  treplicate k = AstNoSimplify . AstReplicate k . unAstNoSimplify
  tappend u v =
    AstNoSimplify $ AstAppend (unAstNoSimplify u) (unAstNoSimplify v)
  tslice i n = AstNoSimplify . AstSlice i n . unAstNoSimplify
  treverse = AstNoSimplify . AstReverse . unAstNoSimplify
  ttranspose perm = AstNoSimplify . AstTranspose perm . unAstNoSimplify
  treshape sh = AstNoSimplify . AstReshape sh . unAstNoSimplify
  tbuild1 k f = AstNoSimplify $ astBuild1Vectorize k (unAstNoSimplify . f)
  tgather sh t f = AstNoSimplify $ AstGather sh (unAstNoSimplify t)
                   $ funToAstIndex f  -- this introduces new variable names
  tcast = AstNoSimplify . AstCast . unAstNoSimplify

  tsumOfList = AstNoSimplify . AstSumOfList . map unAstNoSimplify
  tconst = AstNoSimplify . AstConstant . AstPrimalPart . AstConst
  tconstBare = AstNoSimplify . AstConst
  raddDynamic = undefined

  tconstant = AstNoSimplify . astConstant . AstPrimalPart . unAstNoSimplify
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  tprimalPart = id
  tdualPart = AstDualPart . unAstNoSimplify
  tD u u' = AstNoSimplify $ AstD (AstPrimalPart $ unAstNoSimplify u) u'
  tScale (AstNoSimplify s) (AstDualPart t) = AstDualPart $ s `tmult` t

astLetFunUnSimp :: (KnownNat n, KnownNat m, GoodScalar r)
                => AstRanked r n -> (AstRanked r n -> AstRanked r2 m)
                -> AstRanked r2 m
astLetFunUnSimp a f =
  let sh = shapeAst a
      (AstVarName var, ast) = funToAstR sh f
  in AstLet var a ast

type instance IntOf AstShaped = AstInt

type instance PrimalOf AstShaped = AstPrimalPartS

type instance DualOf AstShaped = AstDualPartS

type instance RankedOf AstShaped = AstRanked

type instance ShapedOf AstShaped = AstShaped

instance ShapedTensor AstShaped where
  slet a f = astLetFunS a f

  sminIndex0 = ShapedList.shapedNat . AstMinIndex1S . AstPrimalPartS
  smaxIndex0 = ShapedList.shapedNat . AstMaxIndex1S . AstPrimalPartS
  sfloor = AstIntFloorS . AstPrimalPartS

  sindex = AstIndexS
  ssum = AstSumS
  sfromIndex0 :: forall n r. KnownNat n
              => IntSh AstShaped n -> AstShaped r '[]
  sfromIndex0 i = AstConstantS $ AstPrimalPartS
                  $ AstIndexS (AstIotaS @n) (ShapedList.consShaped i ZSH)
    -- toInteger is not defined for Ast, hence a special implementation
  sscatter t f = AstScatterS t (funToAstIndexS f)  -- astScatter t (funToAstIndexS f)  -- introduces new vars

  sfromList = AstFromListS
  sfromVector = AstFromVectorS
  sreplicate = AstReplicateS
  sappend = AstAppendS
  sslice (_ :: Proxy i) Proxy = AstSliceS @i
  sreverse = AstReverseS
  stranspose (_ :: Proxy perm) = AstTransposeS @perm  -- astTranspose
  sreshape = AstReshapeS  -- astReshape
  sbuild1 = astBuild1VectorizeS
  sgather t f = AstGatherS t (funToAstIndexS f)  -- introduces new vars
  scast = AstCastS

  ssumOfList = AstSumOfListS
  sconst = AstConstantS . AstPrimalPartS . AstConstS
  sconstBare = AstConstS
  sletWrap = AstLetADShareS
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  saddDynamic :: forall sh r. (GoodScalar r, OS.Shape sh)
              => AstShaped r sh -> DynamicExists AstDynamic
              -> DynamicExists AstDynamic
  saddDynamic r (DynamicExists @_ @r2 d) = DynamicExists $
    if disDummy @AstRanked d then AstSToD r
    else case testEquality (typeRep @r) (typeRep @r2) of
      Just Refl -> case d of
        AstSToD AstIotaS -> AstSToD r
        AstSToD @sh2 (AstSumOfListS l) ->
          case sameShape @sh @sh2 of
            Just Refl -> AstSToD (AstSumOfListS (r : l))
            _ -> error "saddDynamic: type mismatch"
        AstSToD @sh2 v ->
          case sameShape @sh @sh2 of
            Just Refl -> AstSToD (AstSumOfListS [r, v])
            _ -> error "saddDynamic: type mismatch"
        AstRToD AstIota -> AstSToD r
        AstRToD @n2 (AstSumOfList l) ->
          case matchingRank @sh @n2 of
            Just Refl -> AstRToD (AstSumOfList (AstSToR r : l))
            _ -> error "saddDynamic: type mismatch"
        AstRToD @n2 v ->
          case matchingRank @sh @n2 of
            Just Refl -> AstRToD (AstSumOfList [AstSToR r, v])
            _ -> error "saddDynamic: type mismatch"
      _ -> error "saddDynamic: type mismatch"
  sregister = astRegisterFunS

  sconstant = AstConstantS  -- astConstant
  sprimalPart = AstPrimalPartS
  sdualPart = AstDualPartS
  sD = AstDS
  sScale (AstPrimalPartS s) (AstDualPartS t) = AstDualPartS $ s `smult` t

astLetFunS :: (OS.Shape sh, OS.Shape sh2, GoodScalar r)
          => AstShaped r sh -> (AstShaped r sh -> AstShaped r2 sh2)
          -> AstShaped r2 sh2
astLetFunS a f | astIsSmallS True a = f a
astLetFunS a f =
  let (AstVarName var, ast) = funToAstS f
  in AstLetS var a ast  -- astLet var a ast  -- safe, because subsitution ruled out above

astBuild1VectorizeS :: (KnownNat n, OS.Shape sh, GoodScalar r)
                    => (IntSh AstShaped n -> AstShaped r sh)
                    -> AstShaped r (n ': sh)
astBuild1VectorizeS f =
  build1VectorizeS $ funToAstI (f . ShapedList.shapedNat)

type instance IntOf AstPrimalPartS = AstInt

type instance PrimalOf AstPrimalPartS = AstPrimalPartS

type instance DualOf AstPrimalPartS = DummyDual

type instance RankedOf AstPrimalPartS = AstPrimalPart

type instance ShapedOf AstPrimalPartS = AstPrimalPartS

instance ShapedTensor AstPrimalPartS where
  slet a f =
    AstPrimalPartS
    $ astLetFunS (unAstPrimalPartS a) (unAstPrimalPartS . f . AstPrimalPartS)

  sminIndex0 = ShapedList.shapedNat . AstMinIndex1S
  smaxIndex0 = ShapedList.shapedNat . AstMaxIndex1S
  sfloor = AstIntFloorS

  sindex v ix = AstPrimalPartS $ AstIndexS (unAstPrimalPartS v) ix
  ssum = AstPrimalPartS . AstSumS . unAstPrimalPartS
  sfromIndex0 :: forall n r. KnownNat n
              => IntSh AstShaped n -> AstPrimalPartS r '[]
  sfromIndex0 i = AstPrimalPartS
                  $ AstIndexS (AstIotaS @n) (ShapedList.consShaped i ZSH)
    -- toInteger is not defined for Ast, hence a special implementation
  sscatter t f = AstPrimalPartS $ AstScatterS (unAstPrimalPartS t)
                 $ funToAstIndexS f  -- astScatter  -- introduces new vars

  sfromList = AstPrimalPartS . AstFromListS . map unAstPrimalPartS
  sfromVector = AstPrimalPartS . AstFromVectorS . V.map unAstPrimalPartS
  sreplicate = AstPrimalPartS . AstReplicateS . unAstPrimalPartS
  sappend u v =
    AstPrimalPartS $ AstAppendS (unAstPrimalPartS u) (unAstPrimalPartS v)
  sslice (_ :: Proxy i) Proxy = AstPrimalPartS . AstSliceS @i . unAstPrimalPartS
  sreverse = AstPrimalPartS . AstReverseS . unAstPrimalPartS
  stranspose (_ :: Proxy perm) =
    AstPrimalPartS . AstTransposeS @perm . unAstPrimalPartS  -- astTranspose
  sreshape = AstPrimalPartS . AstReshapeS . unAstPrimalPartS  -- astReshape
  sbuild1 f = AstPrimalPartS $ astBuild1VectorizeS (unAstPrimalPartS . f)
  sgather t f = AstPrimalPartS $ AstGatherS (unAstPrimalPartS t)
                $ funToAstIndexS f  -- introduces new vars
  scast = AstPrimalPartS . AstCastS . unAstPrimalPartS

  ssumOfList = AstPrimalPartS . AstSumOfListS . map unAstPrimalPartS
  sconst = AstPrimalPartS . AstConstS
  saddDynamic = undefined

  sconstant = id
  sprimalPart = id
  sdualPart _ = DummyDual
  sD u _ = u
  sScale _ _ = DummyDual
