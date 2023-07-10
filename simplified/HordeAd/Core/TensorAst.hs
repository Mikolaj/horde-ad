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

import           Control.Arrow (second)
import qualified Data.Array.Shape as OS
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality (gcastWith, testEquality, (:~:) (Refl))
import qualified Data.Vector.Generic as V
import           GHC.TypeLits
  (KnownNat, SomeNat (..), sameNat, someNatVal, type (+))
import           Type.Reflection (typeRep)
import           Unsafe.Coerce (unsafeCoerce)

import           HordeAd.Core.Ast
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.AstVectorize
import           HordeAd.Core.ShapedList (ShapedList (..))
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape)

instance RankedTensor AstRanked where
  tlet a f = astLetFun a f

  tshape = shapeAst
  tminIndex = AstMinIndex . astPrimalPart
  tmaxIndex = AstMaxIndex . astPrimalPart
  tfloor = AstFloor . astPrimalPart

  tindex = AstIndex
  tsum = AstSum
  tfromIndex0 i = AstConstant $ astPrimalPart
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
  tletWrap l u = if nullADShare l then u else AstLetADShare l u
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  raddDynamic :: forall n r. (GoodScalar r, KnownNat n)
              => AstRanked r n -> DynamicExists AstDynamic
              -> DynamicExists AstDynamic
  raddDynamic r (DynamicExists @r2 d) = DynamicExists $
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

  tconstant = AstConstant
  tprimalPart = astPrimalPart
  tdualPart = AstDualPart
  tD = AstD  -- TODO: simplify when it's know that dual part is AstConstant
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

instance ConvertTensor AstPrimalPart AstPrimalPartS where
  tfromD = astPrimalPart . tfromD
  tfromS = astPrimalPart . tfromS . unAstPrimalPartS
  dfromR = dfromR . unAstPrimalPart
  dfromS = dfromS . unAstPrimalPartS
  sfromR = astPrimalPartS . sfromR . unAstPrimalPart
  sfromD = astPrimalPartS . sfromD
  ddummy = ddummy @AstRanked
  disDummy = disDummy @AstRanked
  dshape = dshape @AstRanked

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
      genVar (DynamicExists @r2 (AstRToD t)) =
        let sh = shapeAst t
            (AstVarName var, ast) = funToAstR sh id
        in (var, DynamicExists @r2 $ AstRToD ast)
      genVar (DynamicExists @r2 (AstSToD @sh _t)) =
        let (AstVarName var, ast) = funToAstS @sh id
        in (var, DynamicExists @r2 $ AstSToD ast)
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

instance RankedTensor AstPrimalPart where
  tlet a f =
    astPrimalPart
    $ astLetFun (unAstPrimalPart a) (unAstPrimalPart . f . astPrimalPart)

  tshape = shapeAst . unAstPrimalPart
  tminIndex = AstPrimalPart . AstMinIndex
  tmaxIndex = AstPrimalPart . AstMaxIndex
  tfloor = AstPrimalPart . AstFloor

  tindex v ix = astPrimalPart $ AstIndex (unAstPrimalPart v) ix
  tsum = astPrimalPart . AstSum . unAstPrimalPart
  tfromIndex0 i = astPrimalPart
                  $ AstIndex AstIota (singletonIndex i)
    -- toInteger is not defined for Ast, hence a special implementation
  tscatter sh t f = astPrimalPart $ astScatter sh (unAstPrimalPart t)
                    $ funToAstIndex f  -- this introduces new variable names

  tfromList = astPrimalPart . AstFromList . map unAstPrimalPart
  tfromVector = astPrimalPart . AstFromVector . V.map unAstPrimalPart
  treplicate k = astPrimalPart . AstReplicate k . unAstPrimalPart
  tappend u v =
    astPrimalPart $ AstAppend (unAstPrimalPart u) (unAstPrimalPart v)
  tslice i n = astPrimalPart . AstSlice i n . unAstPrimalPart
  treverse = astPrimalPart . AstReverse . unAstPrimalPart
  ttranspose perm = astPrimalPart . astTranspose perm . unAstPrimalPart
  treshape sh = astPrimalPart . astReshape sh . unAstPrimalPart
  tbuild1 k f = astPrimalPart $ astBuild1Vectorize k (unAstPrimalPart . f)
  tgather sh t f = astPrimalPart $ AstGather sh (unAstPrimalPart t)
                   $ funToAstIndex f  -- this introduces new variable names
  tcast = astPrimalPart . AstCast . unAstPrimalPart

  tsumOfList = astPrimalPart . AstSumOfList . map unAstPrimalPart
  tconst = AstPrimalPart . AstConst
  tletWrap l u = if nullADShare l then u
                 else astPrimalPart $ AstLetADShare l (unAstPrimalPart u)
  raddDynamic (AstPrimalPart r) d = raddDynamic r d
  tregister r l = second astPrimalPart $ astRegisterFun (unAstPrimalPart r) l

  tconstant = id
  tprimalPart = id
  tdualPart _ = DummyDual
  tD u _ = u
  tScale _ _ = DummyDual

instance RankedTensor AstNoVectorize where
  tlet a f =
    AstNoVectorize
    $ astLetFun (unAstNoVectorize a) (unAstNoVectorize . f . AstNoVectorize)

  tshape = shapeAst . unAstNoVectorize
  tminIndex = AstNoVectorize . AstMinIndex . astPrimalPart . unAstNoVectorize
  tmaxIndex = AstNoVectorize . AstMaxIndex . astPrimalPart . unAstNoVectorize
  tfloor = AstNoVectorize . AstFloor . astPrimalPart . unAstNoVectorize

  tindex v ix = AstNoVectorize $ AstIndex (unAstNoVectorize v) ix
  tsum = AstNoVectorize . AstSum . unAstNoVectorize
  tfromIndex0 i = AstNoVectorize $ AstConstant $ astPrimalPart
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

  tconstant = AstNoVectorize . AstConstant
  tprimalPart = astPrimalPart . unAstNoVectorize
  tdualPart = AstDualPart . unAstNoVectorize
  tD u u' = AstNoVectorize $ AstD u u'
  tScale (AstPrimalPart s) (AstDualPart t) = AstDualPart $ s `tmult` t

instance RankedTensor AstNoSimplify where
  tlet a f =
    AstNoSimplify
    $ astLetFunUnSimp (unAstNoSimplify a) (unAstNoSimplify . f . AstNoSimplify)

  tshape = shapeAst . unAstNoSimplify
  tminIndex = AstNoSimplify . AstMinIndex . astPrimalPart . unAstNoSimplify
  tmaxIndex = AstNoSimplify . AstMaxIndex . astPrimalPart . unAstNoSimplify
  tfloor = AstNoSimplify . AstFloor . astPrimalPart . unAstNoSimplify

  tindex v ix = AstNoSimplify $ AstIndex (unAstNoSimplify v) ix
  tsum = AstNoSimplify . AstSum . unAstNoSimplify
  tfromIndex0 i = AstNoSimplify $ AstConstant $ astPrimalPart
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

  tconstant = AstNoSimplify . AstConstant
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  tprimalPart = astPrimalPart . unAstNoSimplify
  tdualPart = AstDualPart . unAstNoSimplify
  tD u u' = AstNoSimplify $ AstD u u'
  tScale (AstPrimalPart s) (AstDualPart t) = AstDualPart $ s `tmult` t

astLetFunUnSimp :: (KnownNat n, KnownNat m, GoodScalar r)
                => AstRanked r n -> (AstRanked r n -> AstRanked r2 m)
                -> AstRanked r2 m
astLetFunUnSimp a f =
  let sh = shapeAst a
      (AstVarName var, ast) = funToAstR sh f
  in AstLet var a ast

instance ShapedTensor AstShaped where
  slet a f = astLetFunS a f

  sminIndex = AstMinIndexS . astPrimalPartS
  smaxIndex = AstMaxIndexS . astPrimalPartS
  sfloor = AstFloorS . astPrimalPartS

  sindex = AstIndexS
  ssum = AstSumS
  sfromIndex0 :: forall n r. KnownNat n
              => IntSh AstShaped n -> AstShaped r '[]
  sfromIndex0 i = AstConstantS $ astPrimalPartS
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
  sletWrap l u = if nullADShare l then u else AstLetADShareS l u
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  saddDynamic :: forall sh r. (GoodScalar r, OS.Shape sh)
              => AstShaped r sh -> DynamicExists AstDynamic
              -> DynamicExists AstDynamic
  saddDynamic r (DynamicExists @r2 d) = DynamicExists $
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

  sconstant = AstConstantS
  sprimalPart = astPrimalPartS
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

instance ShapedTensor AstPrimalPartS where
  slet a f =
    astPrimalPartS
    $ astLetFunS (unAstPrimalPartS a) (unAstPrimalPartS . f . astPrimalPartS)

  sminIndex = AstPrimalPartS . AstMinIndexS
  smaxIndex = AstPrimalPartS . AstMaxIndexS
  sfloor = AstPrimalPartS . AstFloorS

  sindex v ix = astPrimalPartS $ AstIndexS (unAstPrimalPartS v) ix
  ssum = astPrimalPartS . AstSumS . unAstPrimalPartS
  sfromIndex0 :: forall n r. KnownNat n
              => IntSh AstShaped n -> AstPrimalPartS r '[]
  sfromIndex0 i = astPrimalPartS
                  $ AstIndexS (AstIotaS @n) (ShapedList.consShaped i ZSH)
    -- toInteger is not defined for Ast, hence a special implementation
  sscatter t f = astPrimalPartS $ AstScatterS (unAstPrimalPartS t)
                 $ funToAstIndexS f  -- astScatter  -- introduces new vars

  sfromList = astPrimalPartS . AstFromListS . map unAstPrimalPartS
  sfromVector = astPrimalPartS . AstFromVectorS . V.map unAstPrimalPartS
  sreplicate = astPrimalPartS . AstReplicateS . unAstPrimalPartS
  sappend u v =
    astPrimalPartS $ AstAppendS (unAstPrimalPartS u) (unAstPrimalPartS v)
  sslice (_ :: Proxy i) Proxy = astPrimalPartS . AstSliceS @i . unAstPrimalPartS
  sreverse = astPrimalPartS . AstReverseS . unAstPrimalPartS
  stranspose (_ :: Proxy perm) =
    astPrimalPartS . AstTransposeS @perm . unAstPrimalPartS  -- astTranspose
  sreshape = astPrimalPartS . AstReshapeS . unAstPrimalPartS  -- astReshape
  sbuild1 f = astPrimalPartS $ astBuild1VectorizeS (unAstPrimalPartS . f)
  sgather t f = astPrimalPartS $ AstGatherS (unAstPrimalPartS t)
                $ funToAstIndexS f  -- introduces new vars
  scast = astPrimalPartS . AstCastS . unAstPrimalPartS

  ssumOfList = astPrimalPartS . AstSumOfListS . map unAstPrimalPartS
  sconst = AstPrimalPartS . AstConstS
  sletWrap l u = if nullADShare l then u
                 else astPrimalPartS $ AstLetADShareS l (unAstPrimalPartS u)
  saddDynamic (AstPrimalPartS r) d = saddDynamic r d
  sregister r l = second astPrimalPartS $ astRegisterFunS (unAstPrimalPartS r) l

  sconstant = id
  sprimalPart = id
  sdualPart _ = DummyDual
  sD u _ = u
  sScale _ _ = DummyDual
