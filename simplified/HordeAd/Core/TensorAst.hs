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
import qualified HordeAd.Core.ShapedList as ShapedList
import           HordeAd.Core.SizedIndex
import           HordeAd.Core.TensorClass
import           HordeAd.Core.Types
import           HordeAd.Internal.OrthotopeOrphanInstances
  (matchingRank, sameShape)


-- * Unlawful boolean instances of ranked AST; they are lawful modulo evaluation

type instance BoolOf (AstRanked s) = AstBool

instance IfF (AstRanked s) where
  ifF = astCond

instance AstSpan s => EqF (AstRanked s) where
  v ==. u = AstRel EqOp [astSpanPrimal v, astSpanPrimal u]
  v /=. u = AstRel NeqOp [astSpanPrimal v, astSpanPrimal u]

instance AstSpan s => OrdF (AstRanked s) where
  AstConst u <. AstConst v = AstBoolConst $ u < v  -- common in indexing
  v <. u = AstRel LsOp [astSpanPrimal v, astSpanPrimal u]
  AstConst u <=. AstConst v = AstBoolConst $ u <= v  -- common in indexing
  v <=. u = AstRel LeqOp [astSpanPrimal v, astSpanPrimal u]
  AstConst u >. AstConst v = AstBoolConst $ u > v  -- common in indexing
  v >. u = AstRel GtOp [astSpanPrimal v, astSpanPrimal u]
  AstConst u >=. AstConst v = AstBoolConst $ u >= v  -- common in indexing
  v >=. u = AstRel GeqOp [astSpanPrimal v, astSpanPrimal u]


-- * Unlawful boolean instances of shaped AST; they are lawful modulo evaluation

type instance BoolOf (AstShaped s) = AstBool

instance IfF (AstShaped s) where
  ifF = astCondS

instance AstSpan s => EqF (AstShaped s) where
  v ==. u = AstRelS EqOp [astSpanPrimalS v, astSpanPrimalS u]
  v /=. u = AstRelS NeqOp [astSpanPrimalS v, astSpanPrimalS u]

instance AstSpan s => OrdF (AstShaped s) where
  AstConstS u <. AstConstS v = AstBoolConst $ u < v  -- common in indexing
  v <. u = AstRelS LsOp [astSpanPrimalS v, astSpanPrimalS u]
  AstConstS u <=. AstConstS v = AstBoolConst $ u <= v  -- common in indexing
  v <=. u = AstRelS LeqOp [astSpanPrimalS v, astSpanPrimalS u]
  AstConstS u >. AstConstS v = AstBoolConst $ u > v  -- common in indexing
  v >. u = AstRelS GtOp [astSpanPrimalS v, astSpanPrimalS u]
  AstConstS u >=. AstConstS v = AstBoolConst $ u >= v  -- common in indexing
  v >=. u = AstRelS GeqOp [astSpanPrimalS v, astSpanPrimalS u]


-- * Ranked tensor AST instances

instance AstSpan s
         => RankedTensor (AstRanked s) where
  tlet a f = astLetFun a f

  tshape = shapeAst
  tminIndex = fromPrimal . AstMinIndex . astSpanPrimal
  tmaxIndex = fromPrimal . AstMaxIndex . astSpanPrimal
  tfloor = fromPrimal . AstFloor . astSpanPrimal

  tiota = fromPrimal AstIota
  tindex = AstIndex
  tsum = astSum
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
  tfromIntegral = fromPrimal . AstFromIntegral . astSpanPrimal

  tsumOfList = AstSumOfList
  tconst = fromPrimal . AstConst
  tconstBare = fromPrimal . AstConst
  tletWrap l u = if nullADShare l then u
                 else fromPrimal $ AstLetADShare l (astSpanPrimal u)
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  tletUnwrap u = case u of
    AstLetADShare l t -> (l, t)
    AstConstant (AstLetADShare l t) -> (l, AstConstant t)
    _ -> (emptyADShare, u)
  raddDynamic :: forall n r. (GoodScalar r, KnownNat n)
              => AstRanked s r n -> DynamicExists (AstDynamic s)
              -> DynamicExists (AstDynamic s)
  raddDynamic r (DynamicExists @r2 d) = DynamicExists $
    if disDummy @(AstRanked s) d then AstRToD r
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

  tconstant = fromPrimal
  tprimalPart = astSpanPrimal
  tdualPart = astSpanDual
  tD = astSpanD
  tScale s t = astDualPart $ AstConstant s `tmult` AstD (tzero (tshape s)) t

instance AstSpan s => ConvertTensor (AstRanked s) (AstShaped s) where
  tfromD = astFromDynamic
  tfromS (AstVarS @sh (AstVarName var)) =
    let sh = OS.shapeT @sh
    in case someNatVal $ toInteger $ length sh of
      Just (SomeNat @p _proxy) ->
        gcastWith (unsafeCoerce Refl :: OS.Rank sh :~: p) $
        AstVar (listShapeToShape sh) (AstVarName var)
      Nothing -> error "tfromS: impossible someNatVal error"
  tfromS (AstRToS t) = t
  tfromS t = AstSToR t
--  dfromR (AstDToR t) = t
  dfromR t = AstRToD t
--  dfromS (AstDToS t) = t
  dfromS t = AstSToD t
  sfromR :: forall sh r. (OS.Shape sh, KnownNat (OS.Rank sh))
         => AstRanked s r (OS.Rank sh) -> AstShaped s r sh
  sfromR (AstVar _sh (AstVarName var)) = AstVarS (AstVarName var)
  sfromR (AstSToR @sh1 t) =
    case sameShape @sh1 @sh of
      Just Refl -> t
      _ -> error "sfromR: different ranks in SToD(DToS)"
  sfromR t = AstRToS t
  sfromD = astFromDynamicS
  ddummy = AstRToD $ fromPrimal AstIota
  disDummy t = case t of
    AstRToD AstIota -> True
    AstSToD AstIotaS -> True
    _ -> False
  dshape (AstRToD v) = shapeToList $ shapeAst v
  dshape (AstSToD @sh _) = OS.shapeT @sh

instance AstSpan s
         => DomainsTensor (AstRanked s) (AstShaped s) (AstDomains s) where
  dmkDomains = AstDomains
  -- The operations below, for this instance, are not used ATM.
  -- They may be used once trev is a method of Tensor.
  rletDomainsOf = astLetDomainsFun
  rletToDomainsOf = astDomainsLetFun
  sletDomainsOf = undefined
  sletToDomainsOf = undefined

astSpanPrimal :: forall s r n. (KnownNat n, GoodScalar r, AstSpan s)
              => AstRanked s r n -> AstRanked AstPrimal r n
astSpanPrimal t | Just Refl <- sameAstSpan @s @AstPrimal = t
astSpanPrimal _ | Just Refl <- sameAstSpan @s @AstDual =
  error "astSpanPrimal: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimal t | Just Refl <- sameAstSpan @s @AstFull = case t of
  AstConstant v -> v
  AstD u _ -> u
  _ -> astPrimalPart t
astSpanPrimal _ = error "a spuriuos case for pattern match coverage"

astSpanDual :: forall s r n. (KnownNat n, GoodScalar r, AstSpan s)
            => AstRanked s r n -> AstRanked AstDual r n
astSpanDual t | Just Refl <- sameAstSpan @s @AstPrimal =
  AstDualPart $ AstConstant t  -- this is nil; likely to happen
astSpanDual t | Just Refl <- sameAstSpan @s @AstDual = t
astSpanDual t | Just Refl <- sameAstSpan @s @AstFull = astDualPart t
astSpanDual _ = error "a spuriuos case for pattern match coverage"

astSpanD :: forall s r n. AstSpan s
         => AstRanked AstPrimal r n -> AstRanked AstDual r n -> AstRanked s r n
astSpanD u _ | Just Refl <- sameAstSpan @s @AstPrimal = u
astSpanD _ u' | Just Refl <- sameAstSpan @s @AstDual = u'
astSpanD u u' | Just Refl <- sameAstSpan @s @AstFull = AstD u u'
astSpanD _ _ = error "a spuriuos case for pattern match coverage"

astLetFun :: (KnownNat n, KnownNat m, GoodScalar r, GoodScalar r2, AstSpan s)
          => AstRanked s r n -> (AstRanked s r n -> AstRanked s r2 m)
          -> AstRanked s r2 m
astLetFun a f | astIsSmall True a = f a
astLetFun a f =
  let sh = shapeAst a
      (var, ast) = funToAstR sh f
  in astLet var a ast  -- safe, because subsitution ruled out above

astLetDomainsFun
  :: forall m s r. AstSpan s
  => AstDomains s -> (AstDomains s -> AstRanked s r m) -> AstRanked s r m
astLetDomainsFun a f =
  let genVar :: DynamicExists (AstDynamic s)
                -> (AstVarId s, DynamicExists (AstDynamic s))
      genVar (DynamicExists @r2 (AstRToD t)) =
        let sh = shapeAst t
            (AstVarName var, ast) = funToAstR sh id
        in (var, DynamicExists @r2 $ AstRToD ast)
      genVar (DynamicExists @r2 (AstSToD @sh _t)) =
        let (AstVarName var, ast) = funToAstS @sh id
        in (var, DynamicExists @r2 $ AstSToD ast)
      (vars, asts) = V.unzip $ V.map genVar (unwrapAstDomains a)
  in AstLetDomains vars a (f $ AstDomains asts)

astDomainsLetFun :: (KnownNat n, GoodScalar r, AstSpan s)
                 => AstRanked s r n -> (AstRanked s r n -> AstDomains s)
                 -> AstDomains s
astDomainsLetFun a f | astIsSmall True a = f a
astDomainsLetFun a f =
  let sh = shapeAst a
      (var, ast) = funToAstR sh id
  in astDomainsLet var a (f ast)  -- safe, because subsitution ruled out above

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize :: (KnownNat n, GoodScalar r, AstSpan s)
                   => Int -> (AstInt -> AstRanked s r n) -> AstRanked s r (1 + n)
astBuild1Vectorize k f = build1Vectorize k $ funToAstI f


-- * Shaped tensor AST instances

instance AstSpan s
         => ShapedTensor (AstShaped s) where
  slet a f = astLetFunS a f

  sminIndex = fromPrimalS . AstMinIndexS . astSpanPrimalS
  smaxIndex = fromPrimalS . AstMaxIndexS . astSpanPrimalS
  sfloor = fromPrimalS . AstFloorS . astSpanPrimalS

  siota = fromPrimalS AstIotaS
  sindex = AstIndexS
  ssum = astSumS
  sscatter t f = astScatterS t (funToAstIndexS f)  -- introduces new vars

  sfromList = AstFromListS
  sfromVector = AstFromVectorS
  sreplicate = AstReplicateS
  sappend = AstAppendS
  sslice (_ :: Proxy i) Proxy = AstSliceS @i
  sreverse = AstReverseS
  stranspose (_ :: Proxy perm) = astTransposeS @perm
  sreshape = astReshapeS
  sbuild1 = astBuild1VectorizeS
  sgather t f = AstGatherS t (funToAstIndexS f)  -- introduces new vars
  scast = AstCastS
  sfromIntegral = fromPrimalS . AstFromIntegralS . astSpanPrimalS

  ssumOfList = AstSumOfListS
  sconst = fromPrimalS . AstConstS
  sconstBare = fromPrimalS . AstConstS
  sletWrap l u = if nullADShare l then u
                 else fromPrimalS $ AstLetADShareS l (astSpanPrimalS u)
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  sletUnwrap u = case u of
    AstLetADShareS l t -> (l, t)
    AstConstantS (AstLetADShareS l t) -> (l, AstConstantS t)
    _ -> (emptyADShare, u)
  saddDynamic :: forall sh r. (GoodScalar r, OS.Shape sh)
              => AstShaped s r sh -> DynamicExists (AstDynamic s)
              -> DynamicExists (AstDynamic s)
  saddDynamic r (DynamicExists @r2 d) = DynamicExists $
    if disDummy @(AstRanked s) d then AstSToD r
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

  sconstant = fromPrimalS
  sprimalPart = astSpanPrimalS
  sdualPart = astSpanDualS
  sD = astSpanDS
  sScale s t = astDualPartS $ AstConstantS s `smult` AstDS 0 t

astSpanPrimalS :: forall s r sh. (OS.Shape sh, GoodScalar r, AstSpan s)
               => AstShaped s r sh -> AstShaped AstPrimal r sh
astSpanPrimalS t | Just Refl <- sameAstSpan @s @AstPrimal = t
astSpanPrimalS _ | Just Refl <- sameAstSpan @s @AstDual =
  error "astSpanPrimalS: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimalS t | Just Refl <- sameAstSpan @s @AstFull = case t of
  AstConstantS v -> v
  AstDS u _ -> u
  _ -> astPrimalPartS t
astSpanPrimalS _ = error "a spuriuos case for pattern match coverage"

astSpanDualS :: forall s r sh. (OS.Shape sh, GoodScalar r, AstSpan s)
             => AstShaped s r sh -> AstShaped AstDual r sh
astSpanDualS t | Just Refl <- sameAstSpan @s @AstPrimal =
  AstDualPartS $ AstConstantS t  -- this is nil; likely to happen
astSpanDualS t | Just Refl <- sameAstSpan @s @AstDual = t
astSpanDualS t | Just Refl <- sameAstSpan @s @AstFull = astDualPartS t
astSpanDualS _ = error "a spuriuos case for pattern match coverage"

astSpanDS :: forall s r sh. AstSpan s
          => AstShaped AstPrimal r sh -> AstShaped AstDual r sh
          -> AstShaped s r sh
astSpanDS u _ | Just Refl <- sameAstSpan @s @AstPrimal = u
astSpanDS _ u' | Just Refl <- sameAstSpan @s @AstDual = u'
astSpanDS u u' | Just Refl <- sameAstSpan @s @AstFull = AstDS u u'
astSpanDS _ _ = error "a spuriuos case for pattern match coverage"

astLetFunS :: (OS.Shape sh, OS.Shape sh2, GoodScalar r, AstSpan s)
          => AstShaped s r sh -> (AstShaped s r sh -> AstShaped s r2 sh2)
          -> AstShaped s r2 sh2
astLetFunS a f | astIsSmallS True a = f a
astLetFunS a f =
  let (var, ast) = funToAstS f
  in AstLetS var a ast  -- astLet var a ast  -- safe, because subsitution ruled out above

astBuild1VectorizeS :: (KnownNat n, OS.Shape sh, GoodScalar r, AstSpan s)
                    => (IntSh (AstShaped AstPrimal) n -> AstShaped s r sh)
                    -> AstShaped s r (n ': sh)
astBuild1VectorizeS f =
  build1VectorizeS $ funToAstI (f . ShapedList.shapedNat)


-- * The auxiliary AstNoVectorize and AstNoSimplify instances, for tests

type instance BoolOf (AstNoVectorize s) = AstBool

deriving instance IfF (AstNoVectorize s)
deriving instance AstSpan s => EqF (AstNoVectorize s)
deriving instance AstSpan s => OrdF (AstNoVectorize s)
deriving instance Eq ((AstNoVectorize s) r n)
deriving instance Ord ((AstNoVectorize s) r n)
deriving instance Num (AstRanked s r n) => Num ((AstNoVectorize s) r n)
deriving instance (Real (AstRanked s r n))
                   => Real ((AstNoVectorize s) r n)
deriving instance Enum (AstRanked s r n) => Enum ((AstNoVectorize s) r n)
deriving instance (Integral (AstRanked s r n))
                  => Integral ((AstNoVectorize s) r n)
deriving instance Fractional (AstRanked s r n)
                  => Fractional ((AstNoVectorize s) r n)
deriving instance Floating (AstRanked s r n) => Floating ((AstNoVectorize s) r n)
deriving instance (RealFrac (AstRanked s r n))
                  => RealFrac ((AstNoVectorize s) r n)
deriving instance (RealFloat (AstRanked s r n))
                  => RealFloat ((AstNoVectorize s) r n)

type instance BoolOf (AstNoSimplify s) = AstBool

deriving instance IfF (AstNoSimplify s)
deriving instance AstSpan s => EqF (AstNoSimplify s)
deriving instance AstSpan s => OrdF (AstNoSimplify s)
deriving instance Eq ((AstNoSimplify s) r n)
deriving instance Ord ((AstNoSimplify s) r n)
deriving instance Num (AstRanked s r n) => Num ((AstNoSimplify s) r n)
deriving instance (Real (AstRanked s r n))
                  => Real ((AstNoSimplify s) r n)
deriving instance Enum (AstRanked s r n) => Enum ((AstNoSimplify s) r n)
deriving instance (Integral (AstRanked s r n))
                  => Integral ((AstNoSimplify s) r n)
deriving instance Fractional (AstRanked s r n) => Fractional ((AstNoSimplify s) r n)
deriving instance Floating (AstRanked s r n) => Floating ((AstNoSimplify s) r n)
deriving instance (RealFrac (AstRanked s r n))
                  => RealFrac ((AstNoSimplify s) r n)
deriving instance (RealFloat (AstRanked s r n))
                  => RealFloat ((AstNoSimplify s) r n)

instance AstSpan s
         => RankedTensor (AstNoVectorize s) where
  tlet a f =
    AstNoVectorize
    $ astLetFun (unAstNoVectorize a) (unAstNoVectorize . f . AstNoVectorize)

  tshape = shapeAst . unAstNoVectorize
  tminIndex = AstNoVectorize . fromPrimal . AstMinIndex . astSpanPrimal . unAstNoVectorize
  tmaxIndex = AstNoVectorize . fromPrimal . AstMaxIndex . astSpanPrimal . unAstNoVectorize
  tfloor = AstNoVectorize . fromPrimal . AstFloor . astSpanPrimal . unAstNoVectorize

  tiota = AstNoVectorize . fromPrimal $ AstIota
  tindex v ix = AstNoVectorize $ AstIndex (unAstNoVectorize v) ix
  tsum = AstNoVectorize . AstSum . unAstNoVectorize
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
  tfromIntegral =
    AstNoVectorize . fromPrimal . AstFromIntegral . astSpanPrimal . unAstNoVectorize

  tsumOfList = AstNoVectorize . AstSumOfList . map unAstNoVectorize
  tconst = AstNoVectorize . fromPrimal . AstConst
  tconstBare = AstNoVectorize . fromPrimal . AstConst
  raddDynamic = undefined

  tconstant = AstNoVectorize . fromPrimal
  tprimalPart = astSpanPrimal . unAstNoVectorize
  tdualPart = astSpanDual . unAstNoVectorize
  tD u u' = AstNoVectorize $ astSpanD u u'
  tScale s t = astSpanDual s `tmult` t

instance AstSpan s
         => RankedTensor (AstNoSimplify s) where
  tlet a f =
    AstNoSimplify
    $ astLetFunUnSimp (unAstNoSimplify a) (unAstNoSimplify . f . AstNoSimplify)

  tshape = shapeAst . unAstNoSimplify
  tminIndex = AstNoSimplify . fromPrimal . AstMinIndex . astSpanPrimal . unAstNoSimplify
  tmaxIndex = AstNoSimplify . fromPrimal . AstMaxIndex . astSpanPrimal . unAstNoSimplify
  tfloor = AstNoSimplify . fromPrimal . AstFloor . astSpanPrimal . unAstNoSimplify

  tiota = AstNoSimplify . fromPrimal $ AstIota
  tindex v ix = AstNoSimplify $ AstIndex (unAstNoSimplify v) ix
  tsum = AstNoSimplify . AstSum . unAstNoSimplify
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
  tfromIntegral =
    AstNoSimplify . fromPrimal . AstFromIntegral . astSpanPrimal . unAstNoSimplify

  tsumOfList = AstNoSimplify . AstSumOfList . map unAstNoSimplify
  tconst = AstNoSimplify . fromPrimal . AstConst
  tconstBare = AstNoSimplify . fromPrimal . AstConst
  raddDynamic = undefined

  tconstant = AstNoSimplify . fromPrimal
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  tprimalPart = astSpanPrimal . unAstNoSimplify
  tdualPart = astSpanDual . unAstNoSimplify
  tD u u' = AstNoSimplify $ astSpanD u u'
  tScale s t = astSpanDual s `tmult` t

astLetFunUnSimp :: (KnownNat n, KnownNat m, GoodScalar r, AstSpan s)
                => AstRanked s r n -> (AstRanked s r n -> AstRanked s r2 m)
                -> AstRanked s r2 m
astLetFunUnSimp a f =
  let sh = shapeAst a
      (var, ast) = funToAstR sh f
  in AstLet var a ast
