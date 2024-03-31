{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Tensor class instances for AST terms. Most of these instances
-- vectorize any terms starting with the build constructor.
-- The AST term instances can be used as building blocks for 'ADVal'
-- instances defined in "TensorADVal" but may also be used standalone.
module HordeAd.Core.TensorAst
  ( revProduceArtifactH
  , forwardPassByInterpretation
  , revArtifactFromForwardPass, revProduceArtifact
  , fwdArtifactFromForwardPass, fwdProduceArtifact
  ) where

import Prelude

import           Control.Exception.Assert.Sugar
import qualified Data.Array.RankedS as OR
import qualified Data.Array.Shape as Sh
import qualified Data.Array.ShapedS as OS
import           Data.Bifunctor.Flip
import qualified Data.EnumMap.Strict as EM
import           Data.Proxy (Proxy (Proxy))
import           Data.Type.Equality ((:~:) (Refl))
import qualified Data.Vector as Data.NonStrict.Vector
import qualified Data.Vector.Generic as V
import           GHC.TypeLits (KnownNat, type (+))
import           System.IO.Unsafe (unsafePerformIO)

import           HordeAd.Core.Adaptor
import           HordeAd.Core.Ast
import           HordeAd.Core.AstEnv
import           HordeAd.Core.AstFreshId
import           HordeAd.Core.AstInline
import           HordeAd.Core.AstInterpret
import           HordeAd.Core.AstSimplify
import           HordeAd.Core.AstTools
import           HordeAd.Core.AstVectorize
import           HordeAd.Core.Delta
import           HordeAd.Core.DualNumber
import           HordeAd.Core.HVector
import           HordeAd.Core.HVectorOps
import           HordeAd.Core.IsPrimal
import           HordeAd.Core.TensorADVal (unADValHVector)
import           HordeAd.Core.TensorClass
import           HordeAd.Core.TensorConcrete ()
import           HordeAd.Core.Types
import qualified HordeAd.Util.ShapedList as ShapedList
import           HordeAd.Util.SizedList

-- * Symbolic reverse and forward derivative computation

revProduceArtifactH
  :: forall r y g astvals.
     ( AdaptableHVector (AstRanked FullSpan) (g r y)
     , AdaptableHVector (AstRanked FullSpan) astvals
     , TermValue astvals )
  => Bool -> (astvals -> g r y) -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> Value astvals -> VoidHVector
  -> ( AstArtifactRev (HVectorPseudoTensor (AstRaw PrimalSpan)) Float '()
     , Dual (HVectorPseudoTensor (AstRaw PrimalSpan)) Float '() )
{-# INLINE revProduceArtifactH #-}
revProduceArtifactH hasDt f envInit vals0 =
  let g :: HVector (AstRanked FullSpan)
        -> HVectorPseudoTensor (AstRanked FullSpan) Float '()
      g !hv = HVectorPseudoTensor
              $ toHVectorOf $ f $ parseHVector (fromValue vals0) hv
  in revArtifactFromForwardPass hasDt (forwardPassByInterpretation g envInit)

forwardPassByInterpretation
  :: (HVector (AstRanked FullSpan)
      -> HVectorPseudoTensor (AstRanked FullSpan) r y)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> HVector (AstRaw PrimalSpan)
  -> [AstDynamicVarName]
  -> HVector (AstRanked FullSpan)
  -> ADVal (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
{-# INLINE forwardPassByInterpretation #-}
forwardPassByInterpretation g envInit hVectorPrimal vars hVector =
  let deltaInputs = generateDeltaInputs hVectorPrimal
      varInputs = makeADInputs hVectorPrimal deltaInputs
      HVectorPseudoTensor ast = g hVector
      env = foldr extendEnvD envInit $ zip vars $ V.toList varInputs
      (ll, as, as') = unADValHVector $ interpretAstHVector env ast
  in dDnotShared (flattenADShare $ V.toList ll)
                 (HVectorPseudoTensor $ dmkHVector as)
                 (HVectorPseudoTensor $ HToH as')

revArtifactFromForwardPass
  :: Bool
  -> (HVector (AstRaw PrimalSpan)
      -> [AstDynamicVarName]
      -> HVector (AstRanked FullSpan)
      -> ADVal (HVectorPseudoTensor (AstRaw PrimalSpan)) r y)
  -> VoidHVector
  -> ( AstArtifactRev (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
     , Dual (HVectorPseudoTensor (AstRaw PrimalSpan)) r y )
{-# INLINE revArtifactFromForwardPass #-}
revArtifactFromForwardPass hasDt forwardPass parameters0 =
  let -- Bangs and the compound function to fix the numbering of variables
      -- for pretty-printing and prevent sharing the impure values/effects
      -- in tests that reset the impure counters.
      !(!varsPrimal, hVectorPrimal, vars, hVector) =
        funToAstRev parameters0 in
  let -- Evaluate completely after terms constructed, to free memory
      -- before gradientFromDelta allocates new memory and new FFI is started.
      !(D l (HVectorPseudoTensor primalBody) delta) =
        forwardPass hVectorPrimal vars hVector
      domsB = shapeAstHVector $ unAstRawWrap primalBody
  in fun1DToAst domsB $ \ !varsDt !astsDt ->
    let mdt = if hasDt
              then Just $ rawHVector astsDt
              else Nothing
        !gradient =
          gradientFromDeltaH
            parameters0 (HVectorPseudoTensor primalBody) mdt delta
        unGradient = dunlet (dmkHVector gradient)
        unPrimal = dunlet primalBody
    in ( ((varsDt, varsPrimal), unGradient, HVectorPseudoTensor unPrimal)
       , delta )

revProduceArtifact
  :: Bool
  -> (HVector (AstRanked FullSpan)
      -> HVectorPseudoTensor (AstRanked FullSpan) r y)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> VoidHVector
  -> ( AstArtifactRev (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
     , Dual (HVectorPseudoTensor (AstRaw PrimalSpan)) r y )
{-# INLINE revProduceArtifact #-}
revProduceArtifact hasDt g envInit =
  revArtifactFromForwardPass hasDt (forwardPassByInterpretation g envInit)

fwdArtifactFromForwardPass
  :: (HVector (AstRaw PrimalSpan)
      -> [AstDynamicVarName]
      -> HVector (AstRanked FullSpan)
      -> ADVal (HVectorPseudoTensor (AstRaw PrimalSpan)) r y)
  -> VoidHVector
  -> ( AstArtifactFwd (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
     , Dual (HVectorPseudoTensor (AstRaw PrimalSpan)) r y )
{-# INLINE fwdArtifactFromForwardPass #-}
fwdArtifactFromForwardPass forwardPass parameters0 =
  let !(!varsPrimalDs, hVectorDs, varsPrimal, hVectorPrimal, vars, hVector) =
        funToAstFwd parameters0 in
  let !(D l (HVectorPseudoTensor primalBody) delta) =
        forwardPass hVectorPrimal vars hVector in
  let !(HVectorPseudoTensor derivative) =
        derivativeFromDeltaH (V.length parameters0) delta hVectorDs
      unDerivative = HVectorPseudoTensor $ dunlet derivative
      unPrimal = HVectorPseudoTensor $ dunlet primalBody
  in ( ((varsPrimalDs, varsPrimal), unDerivative, unPrimal)
     , delta )

fwdProduceArtifact
  :: (HVector (AstRanked FullSpan)
      -> HVectorPseudoTensor (AstRanked FullSpan) r y)
  -> AstEnv (ADVal (AstRaw PrimalSpan))
  -> VoidHVector
  -> ( AstArtifactFwd (HVectorPseudoTensor (AstRaw PrimalSpan)) r y
     , Dual (HVectorPseudoTensor (AstRaw PrimalSpan)) r y )
{-# INLINE fwdProduceArtifact #-}
fwdProduceArtifact g envInit =
  fwdArtifactFromForwardPass (forwardPassByInterpretation g envInit)


-- * Unlawful boolean instances of ranked AST; they are lawful modulo evaluation

type instance SimpleBoolOf (AstRanked s) = AstBool

instance AstSpan s => EqF (AstRanked s) where
  v ==. u = (emptyADShare, AstRel EqOp (astSpanPrimal v) (astSpanPrimal u))
  v /=. u = (emptyADShare, AstRel NeqOp (astSpanPrimal v) (astSpanPrimal u))

instance AstSpan s => OrdF (AstRanked s) where
  AstConst u <. AstConst v = (emptyADShare, AstBoolConst $ u < v)
    -- common in indexing
  v <. u = (emptyADShare, AstRel LsOp (astSpanPrimal v) (astSpanPrimal u))
  AstConst u <=. AstConst v = (emptyADShare, AstBoolConst $ u <= v)
    -- common in indexing
  v <=. u = (emptyADShare, AstRel LeqOp (astSpanPrimal v) (astSpanPrimal u))
  AstConst u >. AstConst v = (emptyADShare, AstBoolConst $ u > v)
    -- common in indexing
  v >. u = (emptyADShare, AstRel GtOp (astSpanPrimal v) (astSpanPrimal u))
  AstConst u >=. AstConst v = (emptyADShare, AstBoolConst $ u >= v)
    -- common in indexing
  v >=. u = (emptyADShare, AstRel GeqOp (astSpanPrimal v) (astSpanPrimal u))

instance IfF (AstRanked s) where
  ifF (_, b) = astCond b


-- * Unlawful boolean instances of shaped AST; they are lawful modulo evaluation

type instance SimpleBoolOf (AstShaped s) = AstBool

instance AstSpan s => EqF (AstShaped s) where
  v ==. u = (emptyADShare, AstRelS EqOp (astSpanPrimalS v) (astSpanPrimalS u))
  v /=. u = (emptyADShare, AstRelS NeqOp (astSpanPrimalS v) (astSpanPrimalS u))

instance AstSpan s => OrdF (AstShaped s) where
  AstConstS u <. AstConstS v = (emptyADShare, AstBoolConst $ u < v)
    -- common in indexing
  v <. u = (emptyADShare, AstRelS LsOp (astSpanPrimalS v) (astSpanPrimalS u))
  AstConstS u <=. AstConstS v = (emptyADShare, AstBoolConst $ u <= v)
    -- common in indexing
  v <=. u = (emptyADShare, AstRelS LeqOp (astSpanPrimalS v) (astSpanPrimalS u))
  AstConstS u >. AstConstS v = (emptyADShare, AstBoolConst $ u > v)
    -- common in indexing
  v >. u = (emptyADShare, AstRelS GtOp (astSpanPrimalS v) (astSpanPrimalS u))
  AstConstS u >=. AstConstS v = (emptyADShare, AstBoolConst $ u >= v)
    -- common in indexing
  v >=. u = (emptyADShare, AstRelS GeqOp (astSpanPrimalS v) (astSpanPrimalS u))

instance IfF (AstShaped s) where
  ifF (_, b) = astCondS b


-- * Ranked tensor AST instances

instance (GoodScalar r, KnownNat n, RankedTensor (AstRanked s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AstRanked s r n) where
  {-# SPECIALIZE instance
      (KnownNat n, AstSpan s)
      => AdaptableHVector (AstRanked s) (AstRanked s Double n) #-}
  toHVector = V.singleton . DynamicRanked
  fromHVector _aInit = fromHVectorR

instance DualNumberValue (AstRanked PrimalSpan r n) where
  type DValue (AstRanked PrimalSpan r n) = Flip OR.Array r n
  fromDValue t = fromPrimal $ AstConst $ runFlip t

instance TermValue (AstRanked FullSpan r n) where
  type Value (AstRanked FullSpan r n) = Flip OR.Array r n
  fromValue t = fromPrimal $ AstConst $ runFlip t

instance AstSpan s => RankedTensor (AstRanked s) where
  rlet = astLetFun

  rshape = shapeAst
  rminIndex = fromPrimal . AstMinIndex . astSpanPrimal
  rmaxIndex = fromPrimal . AstMaxIndex . astSpanPrimal
  rfloor = fromPrimal . AstFloor . astSpanPrimal

  riota = fromPrimal AstIota
  rindex = astIndexStep
  rsum = astSum
  rscatter sh t f = astScatter sh t (funToAstIndex f)  -- introduces new vars

  rfromList = astFromList
  rfromVector = astFromVector
  rreplicate = astReplicate
  rappend = astAppend
  rslice = astSlice
  rreverse = astReverse
  rtranspose = astTranspose
  rreshape = astReshape
  rbuild1 = astBuild1Vectorize
  rgather sh t f = astGatherStep sh t (funToAstIndex f)  -- introduces new vars
  rcast = astCast
  rfromIntegral = fromPrimal . astFromIntegral . astSpanPrimal
  rconst = fromPrimal . AstConst
  rletHVectorIn = astLetHVectorInFun
  rletHFunIn = astLetHFunInFun
  rfromS = astRFromS

  rshare a@(AstShare{}) = a
  rshare a | astIsSmall True a = a
  rshare a = fun1RToAst $ \ !var -> AstShare var a

  rconstant = fromPrimal
  rprimalPart = astSpanPrimal
  rdualPart = astSpanDual
  rD = astSpanD
  rScale s t = astDualPart $ AstConstant s * AstD (rzero (rshape s)) t

astLetHVectorInFun
  :: forall n s r. (KnownNat n, GoodScalar r, AstSpan s)
  => AstHVector s -> (HVector (AstRanked s) -> AstRanked s r n)
  -> AstRanked s r n
{-# INLINE astLetHVectorInFun #-}
astLetHVectorInFun a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorIn vars a (f asts)

astLetHFunInFun
  :: AstHFun -> (AstHFun -> AstRanked s r n)
  -> AstRanked s r n
{-# INLINE astLetHFunInFun #-}
astLetHFunInFun a f =
  let shss = domainShapesAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunIn var a (f ast)

astSpanPrimal :: forall s r n. (KnownNat n, GoodScalar r, AstSpan s)
              => AstRanked s r n -> AstRanked PrimalSpan r n
astSpanPrimal t | Just Refl <- sameAstSpan @s @PrimalSpan = t
astSpanPrimal _ | Just Refl <- sameAstSpan @s @DualSpan =
  error "astSpanPrimal: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimal t | Just Refl <- sameAstSpan @s @FullSpan = astPrimalPart t
astSpanPrimal _ = error "a spuriuos case for pattern match coverage"

astSpanDual :: forall s r n. (KnownNat n, GoodScalar r, AstSpan s)
            => AstRanked s r n -> AstRanked DualSpan r n
astSpanDual t | Just Refl <- sameAstSpan @s @PrimalSpan =
  AstDualPart $ AstConstant t  -- this is nil; likely to happen
astSpanDual t | Just Refl <- sameAstSpan @s @DualSpan = t
astSpanDual t | Just Refl <- sameAstSpan @s @FullSpan = astDualPart t
astSpanDual _ = error "a spuriuos case for pattern match coverage"

astSpanD :: forall s r n. AstSpan s
         => AstRanked PrimalSpan r n -> AstRanked DualSpan r n
         -> AstRanked s r n
astSpanD u _ | Just Refl <- sameAstSpan @s @PrimalSpan = u
astSpanD _ u' | Just Refl <- sameAstSpan @s @DualSpan = u'
astSpanD u u' | Just Refl <- sameAstSpan @s @FullSpan = AstD u u'
astSpanD _ _ = error "a spuriuos case for pattern match coverage"

astLetFun :: (KnownNat n, KnownNat m, GoodScalar r, GoodScalar r2, AstSpan s)
          => AstRanked s r n -> (AstRanked s r n -> AstRanked s r2 m)
          -> AstRanked s r2 m
astLetFun a f | astIsSmall True a = f a
astLetFun a f =
  let sh = shapeAst a
      (var, ast) = funToAstR sh f
  in astLet var a ast  -- safe, because subsitution ruled out above

-- This is a vectorizing combinator that also simplifies
-- the terms touched during vectorization, but not any others.
-- Due to how the Ast instance of Tensor is defined above, vectorization
-- works bottom-up, which removes the need to backtrack in the vectorization
-- pass or repeat until a fixed point is reached.
-- This combinator also introduces new variable names.
astBuild1Vectorize :: (KnownNat n, GoodScalar r, AstSpan s)
                   => Int -> (AstInt -> AstRanked s r n)
                   -> AstRanked s r (1 + n)
astBuild1Vectorize k f = build1Vectorize k $ funToAstI f


-- * Shaped tensor AST instances

instance (GoodScalar r, Sh.Shape sh, ShapedTensor (AstShaped s), AstSpan s)
         => AdaptableHVector (AstRanked s) (AstShaped s r sh) where
  toHVector = V.singleton . DynamicShaped
  fromHVector _aInit = fromHVectorS

instance DualNumberValue (AstShaped PrimalSpan r sh) where
  type DValue (AstShaped PrimalSpan r sh) = Flip OS.Array r sh
  fromDValue t = fromPrimalS $ AstConstS $ runFlip t

instance TermValue (AstShaped FullSpan r sh) where
  type Value (AstShaped FullSpan r sh) = Flip OS.Array r sh
  fromValue t = fromPrimalS $ AstConstS $ runFlip t

instance AstSpan s => ShapedTensor (AstShaped s) where
  slet = astLetFunS

  sminIndex = fromPrimalS . AstMinIndexS . astSpanPrimalS
  smaxIndex = fromPrimalS . AstMaxIndexS . astSpanPrimalS
  sfloor = fromPrimalS . AstFloorS . astSpanPrimalS

  siota = fromPrimalS AstIotaS
  sindex = astIndexStepS
  ssum = astSumS
  sscatter t f = astScatterS t (funToAstIndexS f)  -- introduces new vars

  sfromList = astFromListS
  sfromVector = astFromVectorS
  sreplicate = astReplicateS
  sappend = astAppendS
  sslice (_ :: Proxy i) Proxy = astSliceS @i
  sreverse = astReverseS
  stranspose (_ :: Proxy perm) = astTransposeS @perm
  sreshape = astReshapeS
  sbuild1 = astBuild1VectorizeS
  sgather t f = astGatherStepS t (funToAstIndexS f)  -- introduces new vars
  scast = astCastS
  sfromIntegral = fromPrimalS . astFromIntegralS . astSpanPrimalS
  sconst = fromPrimalS . AstConstS
  sletHVectorIn = astLetHVectorInFunS
  sletHFunIn = astLetHFunInFunS
  sfromR = astSFromR

  sshare a@(AstShareS{}) = a
  sshare a | astIsSmallS True a = a
  sshare a = fun1SToAst $ \ !var -> AstShareS var a

  sconstant = fromPrimalS
  sprimalPart = astSpanPrimalS
  sdualPart = astSpanDualS
  sD = astSpanDS
  sScale s t = astDualPartS $ AstConstantS s * AstDS 0 t

astLetHVectorInFunS
  :: forall sh s r. (Sh.Shape sh, GoodScalar r, AstSpan s)
  => AstHVector s -> (HVector (AstRanked s) -> AstShaped s r sh)
  -> AstShaped s r sh
{-# INLINE astLetHVectorInFunS #-}
astLetHVectorInFunS a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorInS vars a (f asts)

astLetHFunInFunS
  :: AstHFun -> (AstHFun -> AstShaped s r sh)
  -> AstShaped s r sh
{-# INLINE astLetHFunInFunS #-}
astLetHFunInFunS a f =
  let shss = domainShapesAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunInS var a (f ast)

astSpanPrimalS :: forall s r sh. (Sh.Shape sh, GoodScalar r, AstSpan s)
               => AstShaped s r sh -> AstShaped PrimalSpan r sh
astSpanPrimalS t | Just Refl <- sameAstSpan @s @PrimalSpan = t
astSpanPrimalS _ | Just Refl <- sameAstSpan @s @DualSpan =
  error "astSpanPrimalS: can't recover primal from dual"
    -- or we could return zero, but this is unlikely to happen
    -- except by user error
astSpanPrimalS t | Just Refl <- sameAstSpan @s @FullSpan = astPrimalPartS t
astSpanPrimalS _ = error "a spuriuos case for pattern match coverage"

astSpanDualS :: forall s r sh. (Sh.Shape sh, GoodScalar r, AstSpan s)
             => AstShaped s r sh -> AstShaped DualSpan r sh
astSpanDualS t | Just Refl <- sameAstSpan @s @PrimalSpan =
  AstDualPartS $ AstConstantS t  -- this is nil; likely to happen
astSpanDualS t | Just Refl <- sameAstSpan @s @DualSpan = t
astSpanDualS t | Just Refl <- sameAstSpan @s @FullSpan = astDualPartS t
astSpanDualS _ = error "a spuriuos case for pattern match coverage"

astSpanDS :: forall s r sh. AstSpan s
          => AstShaped PrimalSpan r sh -> AstShaped DualSpan r sh
          -> AstShaped s r sh
astSpanDS u _ | Just Refl <- sameAstSpan @s @PrimalSpan = u
astSpanDS _ u' | Just Refl <- sameAstSpan @s @DualSpan = u'
astSpanDS u u' | Just Refl <- sameAstSpan @s @FullSpan = AstDS u u'
astSpanDS _ _ = error "a spuriuos case for pattern match coverage"

astLetFunS :: ( Sh.Shape sh, Sh.Shape sh2, GoodScalar r, GoodScalar r2
              , AstSpan s )
          => AstShaped s r sh -> (AstShaped s r sh -> AstShaped s r2 sh2)
          -> AstShaped s r2 sh2
astLetFunS a f | astIsSmallS True a = f a
astLetFunS a f =
  let (var, ast) = funToAstS f
  in astLetS var a ast  -- safe, because subsitution ruled out above

astBuild1VectorizeS :: (KnownNat n, Sh.Shape sh, GoodScalar r, AstSpan s)
                    => (IntSh (AstShaped PrimalSpan) n -> AstShaped s r sh)
                    -> AstShaped s r (n ': sh)
astBuild1VectorizeS f =
  build1VectorizeS $ funToAstI (f . ShapedList.shapedNat)


-- * HVectorTensor instance

instance DualNumberValue (DynamicTensor (AstRanked PrimalSpan)) where
  type DValue (DynamicTensor (AstRanked PrimalSpan)) =
    DynamicTensor (Flip OR.Array)
  fromDValue = \case
    DynamicRanked t -> DynamicRanked $ fromPrimal $ AstConst $ runFlip t
    DynamicShaped t -> DynamicShaped $ fromPrimalS $ AstConstS $ runFlip t
    DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
    DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2

instance TermValue (DynamicTensor (AstRanked FullSpan)) where
  type Value (DynamicTensor (AstRanked FullSpan)) =
    DynamicTensor (Flip OR.Array)
  fromValue = \case
    DynamicRanked t -> DynamicRanked $ fromPrimal $ AstConst $ runFlip t
    DynamicShaped t -> DynamicShaped $ fromPrimalS $ AstConstS $ runFlip t
    DynamicRankedDummy p1 p2 -> DynamicRankedDummy p1 p2
    DynamicShapedDummy p1 p2 -> DynamicShapedDummy p1 p2

instance AstSpan s => AdaptableHVector (AstRanked s) (AstHVector s) where
  toHVector = undefined  -- impossible without losing sharing
  toHVectorOf = id  -- but this is possible
  fromHVector aInit params =
    let (portion, rest) = V.splitAt (V.length $ shapeAstHVector aInit) params
    in Just (AstMkHVector portion, rest)

instance DualNumberValue (AstHVector PrimalSpan) where
  type DValue (AstHVector PrimalSpan) = HVector (Flip OR.Array)
  fromDValue t = AstMkHVector $ V.map fromDValue t

-- HVector causes overlap and violation of injectivity,
-- hence Data.NonStrict.Vector. Injectivity is crucial to limit the number
-- of type applications the library user has to supply.
instance TermValue (AstHVector FullSpan) where
  type Value (AstHVector FullSpan) =
    Data.NonStrict.Vector.Vector (DynamicTensor (Flip OR.Array))
  fromValue t = AstMkHVector $ V.convert $ V.map fromValue t

instance AdaptableHVector (AstRanked FullSpan)
                          (HVectorPseudoTensor (AstRanked FullSpan) r y) where
  toHVector = undefined  -- impossible without losing sharing
  toHVectorOf = unHVectorPseudoTensor  -- but this is possible
  fromHVector (HVectorPseudoTensor aInit) params =
    let (portion, rest) = V.splitAt (V.length $ shapeAstHVector aInit) params
    in Just (HVectorPseudoTensor $ AstMkHVector portion, rest)

instance TermValue (HVectorPseudoTensor (AstRanked FullSpan) r y) where
  type Value (HVectorPseudoTensor (AstRanked FullSpan) r y) =
    HVectorPseudoTensor (Flip OR.Array) r y
  fromValue (HVectorPseudoTensor t) =
    HVectorPseudoTensor $ AstMkHVector $ V.map fromValue t

instance forall s. AstSpan s => HVectorTensor (AstRanked s) (AstShaped s) where
  dshape = shapeAstHVector
  dmkHVector = AstMkHVector
  dlambda shss f = AstLambda
                   $ fun1LToAst shss $ \ !vvars !ll -> (vvars, unHFun f ll)
  dHApply = astHApply
  dunHVector (AstMkHVector l) = l
  dunHVector hVectorOf =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: ShapeInt n) ->
              DynamicRanked @r @n $ AstProject hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstProjectS hVectorOf i
    in V.imap f $ shapeAstHVector hVectorOf
  dletHVectorInHVector = astLetHVectorInHVectorFun
  dletHFunInHVector = astLetHFunInHVectorFun
  rletInHVector = astLetInHVectorFun
  sletInHVector = astLetInHVectorFunS
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  -- In this instance, these three ops are only used for some rare tests that
  -- use the non-symbolic pipeline to compute a symbolic
  -- value of the derivative at a particular fixed input.
  -- The limitation of AstRaw as a newtype make it impossible
  -- to switch the tests from AstRanked to AstRaw.
  dunlet =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> unletAstHVector6
      _ -> error "dunlet: used not at PrimalSpan"
  -- These and many similar bangs are necessary to ensure variable IDs
  -- are generated in the expected order, resulting in nesting of lets
  -- occuring in the correct order and so no scoping errors.
  dshare a@(AstShareHVector{}) = a
  dshare a =
    let shs = shapeAstHVector a
    in fun1XToAst shs $ \ !vars -> AstShareHVector vars a
  dbuild1 = astBuildHVector1Vectorize
  rrev :: (GoodScalar r, KnownNat n)
       => (forall f. ADReady f => HVector f -> f r n)
       -> VoidHVector
       -> HVector (AstRanked s)
       -> AstHVector s
  rrev f parameters0 =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new @parmeters@, which is much better than computing anew.
    let !(!((!_varsDt, !vars), !gradient, !_primal), _delta) =
          revProduceArtifactH @_ @_ @(AstRanked FullSpan)
                              False f EM.empty
                              (V.map dynamicFromVoid parameters0)
                              parameters0
    in \parameters -> assert (voidHVectorMatches parameters0 parameters) $
      let env = extendEnvHVector @(AstRanked s) vars parameters EM.empty
      in simplifyAstHVector5 $ interpretAstHVector env $ unAstRawWrap gradient
        -- this interpretation both substitutes parameters for the variables and
        -- reinterprets @PrimalSpan@ terms in @s@ terms;
        -- we could shortcut when @s@ is @PrimalSpan@ and @parameters@
        -- are the same variables, but it's a very special case;
        -- a faster implementation would be via AstHApply, but this tests
        -- a slightly different code path, so let's keep it
  drevDt :: VoidHVector
         -> HFun
         -> AstHFun
  drevDt shs f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let g :: HVector (AstRanked FullSpan)
          -> HVectorPseudoTensor (AstRanked FullSpan) r y
        g !hv = HVectorPseudoTensor $ unHFun f [hv]
        (((varsDt, vars), gradient, _primal), _delta) =
          revProduceArtifact True g EM.empty shs
     in AstLambda ([varsDt, vars], simplifyAstHVector5 $ unAstRawWrap gradient)
  dfwd :: VoidHVector
       -> HFun
       -> AstHFun
  dfwd shs f =
    -- This computes the (AST of) derivative of f once and interprets it again
    -- for each new tensor of arguments, which is better than computing it anew.
    let g :: HVector (AstRanked FullSpan)
          -> HVectorPseudoTensor (AstRanked FullSpan) r y
        g !hv = HVectorPseudoTensor $ unHFun f [hv]
        (((varsDt, vars), derivative, _primal), _delta) =
          fwdProduceArtifact g EM.empty shs
     in AstLambda ( [varsDt, vars]
                  , simplifyAstHVector5 $ unAstRawWrap
                    $ unHVectorPseudoTensor derivative )
  dmapAccumRDer
    :: Proxy (AstRanked s)
    -> SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> AstHFun
    -> AstHFun
    -> AstHFun
    -> AstHVector s
    -> AstHVector s
    -> AstHVector s
  dmapAccumRDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstMapAccumRDer k accShs bShs eShs f df rf acc0 es
  dmapAccumLDer
    :: Proxy (AstRanked s)
    -> SNat k
    -> VoidHVector
    -> VoidHVector
    -> VoidHVector
    -> AstHFun
    -> AstHFun
    -> AstHFun
    -> AstHVector s
    -> AstHVector s
    -> AstHVector s
  dmapAccumLDer _ !k !accShs !bShs !eShs f df rf acc0 es =
    AstMapAccumLDer k accShs bShs eShs f df rf acc0 es

astLetHVectorInHVectorFun
  :: AstSpan s
  => AstHVector s -> (HVector (AstRanked s) -> AstHVector s)
  -> AstHVector s
{-# INLINE astLetHVectorInHVectorFun #-}
astLetHVectorInHVectorFun a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    astLetHVectorInHVector vars a (f asts)

astLetHFunInHVectorFun
  :: AstHFun -> (AstHFun -> AstHVector s)
  -> AstHVector s
{-# INLINE astLetHFunInHVectorFun #-}
astLetHFunInHVectorFun a f =
  let shss = domainShapesAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> astLetHFunInHVector var a (f ast)

astLetInHVectorFun :: (KnownNat n, GoodScalar r, AstSpan s)
                   => AstRanked s r n -> (AstRanked s r n -> AstHVector s)
                   -> AstHVector s
{-# NOINLINE astLetInHVectorFun #-}
astLetInHVectorFun a f | astIsSmall True a = f a
astLetInHVectorFun a f = unsafePerformIO $ do  -- the id causes trouble
  let sh = shapeAst a
  (!var, _, !ast) <- funToAstIOR sh id
  return $! astLetInHVector var a (f ast)
              -- safe because subsitution ruled out above

astLetInHVectorFunS :: (Sh.Shape sh, GoodScalar r, AstSpan s)
                    => AstShaped s r sh -> (AstShaped s r sh -> AstHVector s)
                    -> AstHVector s
{-# NOINLINE astLetInHVectorFunS #-}
astLetInHVectorFunS a f | astIsSmallS True a = f a
astLetInHVectorFunS a f = unsafePerformIO $ do  -- the id causes trouble
  (!var, _, !ast) <- funToAstIOS id
  return $! astLetInHVectorS var a (f ast)
              -- safe because subsitution ruled out above

astBuildHVector1Vectorize
  :: AstSpan s
  => SNat k -> (AstInt -> AstHVector s) -> AstHVector s
astBuildHVector1Vectorize k f = build1VectorizeHVector k $ funToAstI f

-- This specialization is not possible where the functions are defined,
-- but is possible here:
{-# SPECIALIZE gradientFromDeltaH
  :: VoidHVector
  -> HVectorPseudoTensor (AstRanked PrimalSpan) Double y
  -> Maybe (HVector (AstRanked PrimalSpan))
  -> HVectorPseudoTensor (DeltaR (AstRanked PrimalSpan)) Double y
  -> HVector (AstRanked PrimalSpan) #-}
{-# SPECIALIZE evalFromnMap
  :: EvalState (AstRanked PrimalSpan) -> EvalState (AstRanked PrimalSpan) #-}


-- * The AstRaw, AstNoVectorize and AstNoSimplify instances

type instance SimpleBoolOf (AstRaw s) = AstBool

deriving instance IfF (AstRaw s)
deriving instance AstSpan s => EqF (AstRaw s)
deriving instance AstSpan s => OrdF (AstRaw s)
deriving instance Eq (AstRaw s r n)
deriving instance Ord (AstRaw s r n)
deriving instance Num (AstRanked s r n) => Num (AstRaw s r n)
deriving instance (Real (AstRanked s r n))
                   => Real (AstRaw s r n)
deriving instance Enum (AstRanked s r n) => Enum (AstRaw s r n)
deriving instance (Integral (AstRanked s r n))
                  => Integral (AstRaw s r n)
deriving instance Fractional (AstRanked s r n)
                  => Fractional (AstRaw s r n)
deriving instance Floating (AstRanked s r n)
                  => Floating (AstRaw s r n)
deriving instance (RealFrac (AstRanked s r n))
                  => RealFrac (AstRaw s r n)
deriving instance (RealFloat (AstRanked s r n))
                  => RealFloat (AstRaw s r n)

type instance SimpleBoolOf (AstRawS s) = AstBool

deriving instance IfF (AstRawS s)
deriving instance AstSpan s => EqF (AstRawS s)
deriving instance AstSpan s => OrdF (AstRawS s)
deriving instance Eq ((AstRawS s) r sh)
deriving instance Ord ((AstRawS s) r sh)
deriving instance Num (AstShaped s r sh) => Num (AstRawS s r sh)
deriving instance (Real (AstShaped s r sh))
                   => Real (AstRawS s r sh)
deriving instance Enum (AstShaped s r sh) => Enum (AstRawS s r sh)
deriving instance (Integral (AstShaped s r sh))
                  => Integral (AstRawS s r sh)
deriving instance Fractional (AstShaped s r sh)
                  => Fractional (AstRawS s r sh)
deriving instance Floating (AstShaped s r sh)
                  => Floating (AstRawS s r sh)
deriving instance (RealFrac (AstShaped s r sh))
                  => RealFrac (AstRawS s r sh)
deriving instance (RealFloat (AstShaped s r sh))
                  => RealFloat (AstRawS s r sh)

type instance SimpleBoolOf (AstNoVectorize s) = AstBool

deriving instance IfF (AstNoVectorize s)
deriving instance AstSpan s => EqF (AstNoVectorize s)
deriving instance AstSpan s => OrdF (AstNoVectorize s)
deriving instance Eq (AstNoVectorize s r n)
deriving instance Ord (AstNoVectorize s r n)
deriving instance Num (AstRanked s r n) => Num (AstNoVectorize s r n)
deriving instance (Real (AstRanked s r n))
                   => Real (AstNoVectorize s r n)
deriving instance Enum (AstRanked s r n) => Enum (AstNoVectorize s r n)
deriving instance (Integral (AstRanked s r n))
                  => Integral (AstNoVectorize s r n)
deriving instance Fractional (AstRanked s r n)
                  => Fractional (AstNoVectorize s r n)
deriving instance Floating (AstRanked s r n)
                  => Floating (AstNoVectorize s r n)
deriving instance (RealFrac (AstRanked s r n))
                  => RealFrac (AstNoVectorize s r n)
deriving instance (RealFloat (AstRanked s r n))
                  => RealFloat (AstNoVectorize s r n)

type instance SimpleBoolOf (AstNoVectorizeS s) = AstBool

deriving instance IfF (AstNoVectorizeS s)
deriving instance AstSpan s => EqF (AstNoVectorizeS s)
deriving instance AstSpan s => OrdF (AstNoVectorizeS s)
deriving instance Eq ((AstNoVectorizeS s) r sh)
deriving instance Ord ((AstNoVectorizeS s) r sh)
deriving instance Num (AstShaped s r sh) => Num (AstNoVectorizeS s r sh)
deriving instance (Real (AstShaped s r sh))
                   => Real (AstNoVectorizeS s r sh)
deriving instance Enum (AstShaped s r sh) => Enum (AstNoVectorizeS s r sh)
deriving instance (Integral (AstShaped s r sh))
                  => Integral (AstNoVectorizeS s r sh)
deriving instance Fractional (AstShaped s r sh)
                  => Fractional (AstNoVectorizeS s r sh)
deriving instance Floating (AstShaped s r sh)
                  => Floating (AstNoVectorizeS s r sh)
deriving instance (RealFrac (AstShaped s r sh))
                  => RealFrac (AstNoVectorizeS s r sh)
deriving instance (RealFloat (AstShaped s r sh))
                  => RealFloat (AstNoVectorizeS s r sh)

type instance SimpleBoolOf (AstNoSimplify s) = AstBool

deriving instance IfF (AstNoSimplify s)
deriving instance AstSpan s => EqF (AstNoSimplify s)
deriving instance AstSpan s => OrdF (AstNoSimplify s)
deriving instance Eq (AstNoSimplify s r n)
deriving instance Ord (AstNoSimplify s r n)
deriving instance Num (AstRanked s r n) => Num (AstNoSimplify s r n)
deriving instance (Real (AstRanked s r n))
                  => Real (AstNoSimplify s r n)
deriving instance Enum (AstRanked s r n) => Enum (AstNoSimplify s r n)
deriving instance (Integral (AstRanked s r n))
                  => Integral (AstNoSimplify s r n)
deriving instance Fractional (AstRanked s r n)
                  => Fractional (AstNoSimplify s r n)
deriving instance Floating (AstRanked s r n)
                  => Floating (AstNoSimplify s r n)
deriving instance (RealFrac (AstRanked s r n))
                  => RealFrac (AstNoSimplify s r n)
deriving instance (RealFloat (AstRanked s r n))
                  => RealFloat (AstNoSimplify s r n)

type instance SimpleBoolOf (AstNoSimplifyS s) = AstBool

deriving instance IfF (AstNoSimplifyS s)
deriving instance AstSpan s => EqF (AstNoSimplifyS s)
deriving instance AstSpan s => OrdF (AstNoSimplifyS s)
deriving instance Eq (AstNoSimplifyS s r sh)
deriving instance Ord (AstNoSimplifyS s r sh)
deriving instance Num (AstShaped s r sh) => Num (AstNoSimplifyS s r sh)
deriving instance (Real (AstShaped s r sh))
                  => Real (AstNoSimplifyS s r sh)
deriving instance Enum (AstShaped s r sh) => Enum (AstNoSimplifyS s r sh)
deriving instance (Integral (AstShaped s r sh))
                  => Integral (AstNoSimplifyS s r sh)
deriving instance Fractional (AstShaped s r sh)
                  => Fractional (AstNoSimplifyS s r sh)
deriving instance Floating (AstShaped s r sh)
                  => Floating (AstNoSimplifyS s r sh)
deriving instance (RealFrac (AstShaped s r sh))
                  => RealFrac (AstNoSimplifyS s r sh)
deriving instance (RealFloat (AstShaped s r sh))
                  => RealFloat (AstNoSimplifyS s r sh)

instance AstSpan s => RankedTensor (AstRaw s) where
  rlet a f = AstRaw $ astLetFunRaw (unAstRaw a) (unAstRaw . f . AstRaw)
  rshape = shapeAst . unAstRaw
  rminIndex = AstRaw . fromPrimal . AstMinIndex . astSpanPrimal . unAstRaw
  rmaxIndex = AstRaw . fromPrimal . AstMaxIndex . astSpanPrimal . unAstRaw
  rfloor = AstRaw . fromPrimal . AstFloor . astSpanPrimal . unAstRaw
  riota = AstRaw . fromPrimal $ AstIota
  rindex v ix = AstRaw $ AstIndex (unAstRaw v) (unAstRaw <$> ix)
  rsum = AstRaw . AstSum . unAstRaw
  rscatter sh t f = AstRaw $ AstScatter sh (unAstRaw t)
                    $ funToAstIndex (fmap unAstRaw . f . fmap AstRaw)
                        -- this introduces new variable names
  rfromList = AstRaw . AstFromList . map unAstRaw
  rfromVector = AstRaw . AstFromVector . V.map unAstRaw
  rreplicate k = AstRaw . AstReplicate k . unAstRaw
  rappend u v = AstRaw $ AstAppend (unAstRaw u) (unAstRaw v)
  rslice i n = AstRaw . AstSlice i n . unAstRaw
  rreverse = AstRaw . AstReverse . unAstRaw
  rtranspose perm = AstRaw . AstTranspose perm . unAstRaw
  rreshape sh = AstRaw . AstReshape sh . unAstRaw
  rbuild1 k f = AstRaw $ AstBuild1 k
                $ funToAstI  -- this introduces new variable names
                $ unAstRaw . f . AstRaw
  rgather sh t f = AstRaw $ AstGather sh (unAstRaw t)
                   $ funToAstIndex (fmap unAstRaw . f . fmap AstRaw)
                       -- this introduces new variable names
  rcast = AstRaw . AstCast . unAstRaw
  rfromIntegral =
    AstRaw . fromPrimal . AstFromIntegral . astSpanPrimal . unAstRaw
  rconst = AstRaw . fromPrimal . AstConst
  rletHVectorIn a f =
    AstRaw $ astLetHVectorInFunRaw (unAstRawWrap a) (unAstRaw . f . rawHVector)
  rletHFunIn a f = AstRaw $ astLetHFunInFunRaw a (unAstRaw . f)
  rfromS = AstRaw . AstRFromS . unAstRawS

  rletWrap l u | Just Refl <- sameAstSpan @s @PrimalSpan =
    if nullADShare l then u else AstRaw $ AstLetADShare l (unAstRaw u)
  rletWrap _ _ = error "rletWrap: wrong span"
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  rletUnwrap u = case unAstRaw u of
    AstLetADShare l t -> (l, AstRaw t)
    AstConstant (AstLetADShare l t) -> (l, AstRaw $ AstConstant t)
    _ -> (emptyADShare, u)
  -- For convenience and simplicity we define this for all spans,
  -- but it can only ever be used for PrimalSpan.
  rshare a@(AstRaw (AstShare{})) = a
  rshare a | astIsSmall True (unAstRaw a) = a
  rshare a = AstRaw $ fun1RToAst $ \ !var -> AstShare var (unAstRaw a)

  rconstant = AstRaw . fromPrimal . unAstRaw
  rprimalPart = AstRaw . astSpanPrimal . unAstRaw
  rdualPart = AstRaw . astSpanDual . unAstRaw
  rD u u' = AstRaw $ astSpanD (unAstRaw u) (unAstRaw u')
  rScale s t = AstRaw $ astDualPart
               $ AstConstant (unAstRaw s) * AstD (rzero (rshape s)) (unAstRaw t)

astLetFunRaw :: (KnownNat n, KnownNat m, GoodScalar r, AstSpan s)
             => AstRanked s r n -> (AstRanked s r n -> AstRanked s r2 m)
             -> AstRanked s r2 m
astLetFunRaw a f | astIsSmall True a = f a  -- too important an optimization
astLetFunRaw a f =
  let sh = shapeAst a
      (var, ast) = funToAstR sh f
  in AstLet var a ast

astLetFunRawS :: (Sh.Shape sh, Sh.Shape sh2, GoodScalar r, AstSpan s)
              => AstShaped s r sh -> (AstShaped s r sh -> AstShaped s r2 sh2)
              -> AstShaped s r2 sh2
astLetFunRawS a f | astIsSmallS True a = f a
astLetFunRawS a f =
  let (var, ast) = funToAstS f
  in AstLetS var a ast

astLetHVectorInFunRaw
  :: forall n s r. AstSpan s
  => AstHVector s -> (HVector (AstRanked s) -> AstRanked s r n)
  -> AstRanked s r n
astLetHVectorInFunRaw a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    AstLetHVectorIn vars a (f asts)

astLetHVectorInFunRawS
  :: forall sh s r. AstSpan s
  => AstHVector s -> (HVector (AstRanked s) -> AstShaped s r sh)
  -> AstShaped s r sh
astLetHVectorInFunRawS a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    AstLetHVectorInS vars a (f asts)

astLetHFunInFunRaw
  :: AstHFun -> (AstHFun -> AstRanked s r n)
  -> AstRanked s r n
astLetHFunInFunRaw a f =
  let shss = domainShapesAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunIn var a (f ast)

astLetHFunInFunRawS
  :: AstHFun -> (AstHFun -> AstShaped s r sh)
  -> AstShaped s r sh
astLetHFunInFunRawS a f =
  let shss = domainShapesAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunInS var a (f ast)

astLetHVectorInHVectorFunRaw
  :: AstSpan s
  => AstHVector s -> (HVector (AstRanked s) -> AstHVector s)
  -> AstHVector s
astLetHVectorInHVectorFunRaw a f =
  fun1DToAst (shapeAstHVector a) $ \ !vars !asts ->
    AstLetHVectorInHVector vars a (f asts)

astLetHFunInHVectorFunRaw
  :: AstHFun -> (AstHFun -> AstHVector s)
  -> AstHVector s
astLetHFunInHVectorFunRaw a f =
  let shss = domainShapesAstHFun a
      shs = shapeAstHFun a
  in fun1HToAst shss shs $ \ !var !ast -> AstLetHFunInHVector var a (f ast)

astLetInHVectorFunRaw :: (KnownNat n, GoodScalar r, AstSpan s)
                      => AstRanked s r n -> (AstRanked s r n -> AstHVector s)
                      -> AstHVector s
astLetInHVectorFunRaw a f | astIsSmall True a = f a
astLetInHVectorFunRaw a f = unsafePerformIO $ do  -- the id causes trouble
  let sh = shapeAst a
  (!var, _, !ast) <- funToAstIOR sh id
  return $! AstLetInHVector var a (f ast)

astLetInHVectorFunRawS :: (Sh.Shape sh, GoodScalar r, AstSpan s)
                       => AstShaped s r sh -> (AstShaped s r sh -> AstHVector s)
                       -> AstHVector s
astLetInHVectorFunRawS a f | astIsSmallS True a = f a
astLetInHVectorFunRawS a f = unsafePerformIO $ do  -- the id causes trouble
  (!var, _, !ast) <- funToAstIOS id
  return $! AstLetInHVectorS var a (f ast)

instance AstSpan s => ShapedTensor (AstRawS s) where
  slet a f = AstRawS $ astLetFunRawS (unAstRawS a) (unAstRawS . f . AstRawS)
  sminIndex = AstRawS . fromPrimalS . AstMinIndexS . astSpanPrimalS . unAstRawS
  smaxIndex = AstRawS . fromPrimalS . AstMaxIndexS . astSpanPrimalS . unAstRawS
  sfloor = AstRawS . fromPrimalS . AstFloorS . astSpanPrimalS . unAstRawS
  siota = AstRawS . fromPrimalS $ AstIotaS
  sindex v ix = AstRawS $ AstIndexS (unAstRawS v) (unAstRaw <$> ix)
  ssum = AstRawS . AstSumS . unAstRawS
  sscatter t f = AstRawS $ AstScatterS (unAstRawS t)
                 $ funToAstIndexS (fmap unAstRaw . f . fmap AstRaw)
                     -- this introduces new variable names
  sfromList = AstRawS . AstFromListS . map unAstRawS
  sfromVector = AstRawS . AstFromVectorS . V.map unAstRawS
  sreplicate = AstRawS . AstReplicateS . unAstRawS
  sappend u v = AstRawS $ AstAppendS (unAstRawS u) (unAstRawS v)
  sslice (_ :: Proxy i) Proxy = AstRawS . AstSliceS @i . unAstRawS
  sreverse = AstRawS . AstReverseS . unAstRawS
  stranspose (_ :: Proxy perm) = AstRawS . AstTransposeS @perm . unAstRawS
  sreshape = AstRawS . AstReshapeS . unAstRawS
  sbuild1 f = AstRawS $ AstBuild1S
              $ funToAstI  -- this introduces new variable names
              $ unAstRawS . f . ShapedList.shapedNat . AstRaw
  sgather t f = AstRawS $ AstGatherS (unAstRawS t)
                $ funToAstIndexS (fmap unAstRaw . f . fmap AstRaw)
                    -- this introduces new variable names
  scast = AstRawS . AstCastS . unAstRawS
  sfromIntegral = AstRawS . fromPrimalS . AstFromIntegralS
                  . astSpanPrimalS . unAstRawS
  sconst = AstRawS . fromPrimalS . AstConstS
  sletHVectorIn a f =
    AstRawS
    $ astLetHVectorInFunRawS (unAstRawWrap a) (unAstRawS . f . rawHVector)
  sletHFunIn a f = AstRawS $ astLetHFunInFunRawS a (unAstRawS . f)
  sfromR = AstRawS . AstSFromR . unAstRaw

  sletWrap l u | Just Refl <- sameAstSpan @s @PrimalSpan =
    if nullADShare l then u else AstRawS $ AstLetADShareS l (unAstRawS u)
  sletWrap _ _ = error "sletWrap: wrong span"
    -- We can't use astLet here, because it may inline a let that is
    -- present at the top level of the dual number and so we'd lose
    -- sharing that is not visible in this restricted context.
    -- To make sure astLet is not used on these, we mark them with
    -- a special constructor that also makes comparing lets cheap.
  sletUnwrap u = case unAstRawS u of
    AstLetADShareS l t -> (l, AstRawS t)
    AstConstantS (AstLetADShareS l t) -> (l, AstRawS $ AstConstantS t)
    _ -> (emptyADShare, u)
  sshare a@(AstRawS (AstShareS{})) = a
  sshare a | astIsSmallS True (unAstRawS a) = a
  sshare a = AstRawS $ fun1SToAst $ \ !var -> AstShareS var (unAstRawS a)

  sconstant = AstRawS . fromPrimalS . unAstRawS
  sprimalPart = AstRawS . astSpanPrimalS . unAstRawS
  sdualPart = AstRawS . astSpanDualS . unAstRawS
  sD u u' = AstRawS $ astSpanDS (unAstRawS u) (unAstRawS u')
  sScale s t = AstRawS $ astDualPartS
               $ AstConstantS (unAstRawS s) * AstDS 0 (unAstRawS t)

instance AstSpan s => HVectorTensor (AstRaw s) (AstRawS s) where
  dshape = shapeAstHVector . unAstRawWrap
  dmkHVector = AstRawWrap . AstMkHVector . unRawHVector
  dlambda shss f = AstLambda
                   $ fun1LToAst shss $ \ !vvars !ll -> (vvars, unHFun f ll)
  dHApply t ll = AstRawWrap $ AstHApply t (map unRawHVector ll)
  dunHVector (AstRawWrap (AstMkHVector l)) = rawHVector l
  dunHVector (AstRawWrap hVectorOf) =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: ShapeInt n) ->
              DynamicRanked @r @n $ AstProject hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstProjectS hVectorOf i
    in rawHVector $ V.imap f $ shapeAstHVector hVectorOf
  dletHVectorInHVector a f =
    AstRawWrap
    $ astLetHVectorInHVectorFunRaw (unAstRawWrap a)
                                   (unAstRawWrap . f . rawHVector)
  dletHFunInHVector t f =
    AstRawWrap
    $ astLetHFunInHVectorFunRaw t (unAstRawWrap . f)
  rletInHVector u f =
    AstRawWrap
    $ astLetInHVectorFunRaw (unAstRaw u) (unAstRawWrap . f . AstRaw)
  sletInHVector u f =
    AstRawWrap
    $ astLetInHVectorFunRawS (unAstRawS u) (unAstRawWrap . f . AstRawS)
  dunlet =
    case sameAstSpan @s @PrimalSpan of
      Just Refl -> \t ->
        AstRawWrap $ unletAstHVector6 $ unAstRawWrap t
      _ -> error "dunlet: used not at PrimalSpan"
  dshare a@(AstRawWrap (AstShareHVector{})) = a
  dshare (AstRawWrap a) =
    let shs = shapeAstHVector a
    in AstRawWrap $ fun1XToAst shs $ \ !vars -> AstShareHVector vars a
  dbuild1 k f = AstRawWrap
                $ AstBuildHVector1 k $ funToAstI (unAstRawWrap . f . AstRaw)
  -- These three methods are called at this type in delta evaluation via
  -- dmapAccumR and dmapAccumL, they have to work. We could refrain from
  -- simplifying the resulting terms, but it's not clear that's more consistent.
  rrev f parameters0 hVector =  -- we don't have an AST constructor to hold it
    AstRawWrap
    $ rrev f parameters0 (unRawHVector hVector)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer _ k accShs bShs eShs f df rf acc0 es =
    AstRawWrap
    $ AstMapAccumRDer k accShs bShs eShs f df rf (unAstRawWrap acc0)
                                                 (unAstRawWrap es)
  dmapAccumLDer _ k accShs bShs eShs f df rf acc0 es =
    AstRawWrap
    $ AstMapAccumLDer k accShs bShs eShs f df rf (unAstRawWrap acc0)
                                                 (unAstRawWrap es)

instance AstSpan s => RankedTensor (AstNoVectorize s) where
  rlet a f =
    AstNoVectorize
    $ rlet (unAstNoVectorize a) (unAstNoVectorize . f . AstNoVectorize)
  rshape = rshape . unAstNoVectorize
  rminIndex = AstNoVectorize . rminIndex . unAstNoVectorize
  rmaxIndex = AstNoVectorize . rmaxIndex . unAstNoVectorize
  rfloor = AstNoVectorize . rfloor . unAstNoVectorize
  riota = AstNoVectorize riota
  rindex v ix =
    AstNoVectorize $ rindex (unAstNoVectorize v) (unAstNoVectorize <$> ix)
  rsum = AstNoVectorize . rsum . unAstNoVectorize
  rscatter sh t f =
    AstNoVectorize $ rscatter sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  rfromList = AstNoVectorize . rfromList . map unAstNoVectorize
  rfromVector = AstNoVectorize . rfromVector . V.map unAstNoVectorize
  rreplicate k = AstNoVectorize . rreplicate k . unAstNoVectorize
  rappend u v =
    AstNoVectorize $ rappend (unAstNoVectorize u) (unAstNoVectorize v)
  rslice i n = AstNoVectorize . rslice i n . unAstNoVectorize
  rreverse = AstNoVectorize . rreverse . unAstNoVectorize
  rtranspose perm = AstNoVectorize . rtranspose perm . unAstNoVectorize
  rreshape sh = AstNoVectorize . rreshape sh . unAstNoVectorize
  rbuild1 k f = AstNoVectorize $ AstBuild1 k
                $ funToAstI  -- this introduces new variable names
                $ unAstNoVectorize . f . AstNoVectorize
  rgather sh t f =
    AstNoVectorize $ rgather sh (unAstNoVectorize t)
                   $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  rcast = AstNoVectorize . rcast . unAstNoVectorize
  rfromIntegral = AstNoVectorize . rfromIntegral . unAstNoVectorize
  rconst = AstNoVectorize . rconst
  rletHVectorIn a f =
    AstNoVectorize
    $ rletHVectorIn (unAstNoVectorizeWrap a)
                    (unAstNoVectorize . f . noVectorizeHVector)
  rletHFunIn a f = AstNoVectorize $ rletHFunIn a (unAstNoVectorize . f)
  rfromS = AstNoVectorize . rfromS . unAstNoVectorizeS
  rconstant = AstNoVectorize . rconstant . unAstNoVectorize
  rprimalPart = AstNoVectorize . rprimalPart . unAstNoVectorize
  rdualPart = AstNoVectorize . rdualPart . unAstNoVectorize
  rD u u' = AstNoVectorize $ rD (unAstNoVectorize u) (unAstNoVectorize u')
  rScale s t = AstNoVectorize $ rScale @(AstRanked s)
                                       (unAstNoVectorize s) (unAstNoVectorize t)

instance AstSpan s => ShapedTensor (AstNoVectorizeS s) where
  slet a f =
    AstNoVectorizeS
    $ slet (unAstNoVectorizeS a) (unAstNoVectorizeS . f . AstNoVectorizeS)
  sminIndex = AstNoVectorizeS . sminIndex . unAstNoVectorizeS
  smaxIndex = AstNoVectorizeS . smaxIndex . unAstNoVectorizeS
  sfloor = AstNoVectorizeS . sfloor . unAstNoVectorizeS
  siota = AstNoVectorizeS siota
  sindex v ix =
    AstNoVectorizeS $ sindex (unAstNoVectorizeS v) (unAstNoVectorize <$> ix)
  ssum = AstNoVectorizeS . ssum . unAstNoVectorizeS
  sscatter t f = AstNoVectorizeS $ sscatter (unAstNoVectorizeS t)
                 $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  sfromList = AstNoVectorizeS . sfromList . map unAstNoVectorizeS
  sfromVector = AstNoVectorizeS . sfromVector . V.map unAstNoVectorizeS
  sreplicate = AstNoVectorizeS . sreplicate . unAstNoVectorizeS
  sappend u v =
    AstNoVectorizeS $ sappend (unAstNoVectorizeS u) (unAstNoVectorizeS v)
  sslice proxy1 proxy2 =
    AstNoVectorizeS . sslice proxy1 proxy2 . unAstNoVectorizeS
  sreverse = AstNoVectorizeS . sreverse . unAstNoVectorizeS
  stranspose perm =
    AstNoVectorizeS . stranspose perm . unAstNoVectorizeS
  sreshape = AstNoVectorizeS . sreshape . unAstNoVectorizeS
  sbuild1 f = AstNoVectorizeS $ AstBuild1S
                $ funToAstI  -- this introduces new variable names
                $ unAstNoVectorizeS . f . ShapedList.shapedNat . AstNoVectorize
  sgather t f = AstNoVectorizeS $ sgather (unAstNoVectorizeS t)
                $ fmap unAstNoVectorize . f . fmap AstNoVectorize
  scast = AstNoVectorizeS . scast . unAstNoVectorizeS
  sfromIntegral = AstNoVectorizeS . sfromIntegral . unAstNoVectorizeS
  sconst = AstNoVectorizeS . sconst
  sletHVectorIn a f =
    AstNoVectorizeS
    $ sletHVectorIn (unAstNoVectorizeWrap a)
                    (unAstNoVectorizeS . f . noVectorizeHVector)
  sletHFunIn a f = AstNoVectorizeS $ sletHFunIn a (unAstNoVectorizeS . f)
  sfromR = AstNoVectorizeS . sfromR . unAstNoVectorize
  sconstant = AstNoVectorizeS . sconstant . unAstNoVectorizeS
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  sprimalPart = AstNoVectorizeS . sprimalPart . unAstNoVectorizeS
  sdualPart = AstNoVectorizeS . sdualPart . unAstNoVectorizeS
  sD u u' =
    AstNoVectorizeS $ sD  (unAstNoVectorizeS u) (unAstNoVectorizeS u')
  sScale s t =
    AstNoVectorizeS $ sScale @(AstShaped s)
                             (unAstNoVectorizeS s) (unAstNoVectorizeS t)

instance AstSpan s => HVectorTensor (AstNoVectorize s) (AstNoVectorizeS s) where
  dshape = dshape . unAstNoVectorizeWrap
  dmkHVector =
    AstNoVectorizeWrap . dmkHVector . unNoVectorizeHVector
  dlambda = dlambda @(AstRanked s)
  dHApply t ll =
    AstNoVectorizeWrap $ dHApply t (map unNoVectorizeHVector ll)
  dunHVector =
    noVectorizeHVector . dunHVector . unAstNoVectorizeWrap
  dletHVectorInHVector a f =
    AstNoVectorizeWrap
    $ dletHVectorInHVector (unAstNoVectorizeWrap a)
                           (unAstNoVectorizeWrap . f . noVectorizeHVector)
  dletHFunInHVector t f =
    AstNoVectorizeWrap
    $ dletHFunInHVector t (unAstNoVectorizeWrap . f)
  rletInHVector u f =
    AstNoVectorizeWrap
    $ rletInHVector (unAstNoVectorize u)
                    (unAstNoVectorizeWrap . f . AstNoVectorize)
  sletInHVector u f =
    AstNoVectorizeWrap
    $ sletInHVector (unAstNoVectorizeS u)
                    (unAstNoVectorizeWrap . f . AstNoVectorizeS)
  dbuild1 k f =
    AstNoVectorizeWrap
    $ AstBuildHVector1 k $ funToAstI (unAstNoVectorizeWrap . f . AstNoVectorize)
  rrev f parameters0 hVector =
    AstNoVectorizeWrap
    $ rrev f parameters0 (unNoVectorizeHVector hVector)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer _ k accShs bShs eShs f df rf acc0 es =
    AstNoVectorizeWrap
    $ dmapAccumRDer (Proxy @(AstRanked s))
                    k accShs bShs eShs f df rf (unAstNoVectorizeWrap acc0)
                                               (unAstNoVectorizeWrap es)
  dmapAccumLDer _ k accShs bShs eShs f df rf acc0 es =
    AstNoVectorizeWrap
    $ dmapAccumLDer (Proxy @(AstRanked s))
                    k accShs bShs eShs f df rf (unAstNoVectorizeWrap acc0)
                                               (unAstNoVectorizeWrap es)

unNoVectorizeHVector :: HVector (AstNoVectorize s) -> HVector (AstRanked s)
unNoVectorizeHVector =
  let f (DynamicRanked (AstNoVectorize t)) = DynamicRanked t
      f (DynamicShaped (AstNoVectorizeS t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noVectorizeHVector :: HVector (AstRanked s) -> HVector (AstNoVectorize s)
noVectorizeHVector =
  let f (DynamicRanked t) = DynamicRanked $ AstNoVectorize t
      f (DynamicShaped t) = DynamicShaped $ AstNoVectorizeS t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

instance AstSpan s => RankedTensor (AstNoSimplify s) where
  rlet a f =
    AstNoSimplify
    $ astLetFunRaw (unAstNoSimplify a) (unAstNoSimplify . f . AstNoSimplify)
  rshape = shapeAst . unAstNoSimplify
  rminIndex = AstNoSimplify . fromPrimal . AstMinIndex
              . astSpanPrimal . unAstNoSimplify
  rmaxIndex = AstNoSimplify . fromPrimal . AstMaxIndex
              . astSpanPrimal . unAstNoSimplify
  rfloor = AstNoSimplify . fromPrimal . AstFloor
           . astSpanPrimal . unAstNoSimplify
  riota = AstNoSimplify . fromPrimal $ AstIota
  rindex v ix =
    AstNoSimplify $ AstIndex (unAstNoSimplify v) (unAstNoSimplify <$> ix)
  rsum = AstNoSimplify . AstSum . unAstNoSimplify
  rscatter sh t f = AstNoSimplify $ AstScatter sh (unAstNoSimplify t)
                    $ funToAstIndex
                        (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                          -- this introduces new variable names
  rfromList = AstNoSimplify . AstFromList . map unAstNoSimplify
  rfromVector = AstNoSimplify . AstFromVector . V.map unAstNoSimplify
  rreplicate k = AstNoSimplify . AstReplicate k . unAstNoSimplify
  rappend u v =
    AstNoSimplify $ AstAppend (unAstNoSimplify u) (unAstNoSimplify v)
  rslice i n = AstNoSimplify . AstSlice i n . unAstNoSimplify
  rreverse = AstNoSimplify . AstReverse . unAstNoSimplify
  rtranspose perm = AstNoSimplify . AstTranspose perm . unAstNoSimplify
  rreshape sh = AstNoSimplify . AstReshape sh . unAstNoSimplify
  rbuild1 k f =
    AstNoSimplify $ astBuild1Vectorize k (unAstNoSimplify . f . AstNoSimplify)
  rgather sh t f = AstNoSimplify $ AstGather sh (unAstNoSimplify t)
                   $ funToAstIndex
                       (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                         -- this introduces new variable names
  rcast = AstNoSimplify . AstCast . unAstNoSimplify
  rfromIntegral = AstNoSimplify . fromPrimal . AstFromIntegral
                  . astSpanPrimal . unAstNoSimplify
  rconst = AstNoSimplify . fromPrimal . AstConst
  rletHVectorIn a f =
    AstNoSimplify
    $ astLetHVectorInFunRaw (unAstNoSimplifyWrap a)
                            (unAstNoSimplify . f . noSimplifyHVector)
  rletHFunIn a f = AstNoSimplify $ astLetHFunInFunRaw a (unAstNoSimplify . f)
  rfromS = AstNoSimplify . AstRFromS . unAstNoSimplifyS
  rconstant = AstNoSimplify . fromPrimal . unAstNoSimplify
  rprimalPart = AstNoSimplify . astSpanPrimal . unAstNoSimplify
  rdualPart = AstNoSimplify . astSpanDual . unAstNoSimplify
  rD u u' = AstNoSimplify $ astSpanD (unAstNoSimplify u) (unAstNoSimplify u')
  rScale s t = AstNoSimplify $ astDualPart
               $ AstConstant (unAstNoSimplify s)
                 * AstD (rzero (rshape s)) (unAstNoSimplify t)

instance AstSpan s => ShapedTensor (AstNoSimplifyS s) where
  slet a f =
    AstNoSimplifyS
    $ astLetFunRawS (unAstNoSimplifyS a) (unAstNoSimplifyS . f . AstNoSimplifyS)
  sminIndex = AstNoSimplifyS . fromPrimalS . AstMinIndexS
              . astSpanPrimalS . unAstNoSimplifyS
  smaxIndex = AstNoSimplifyS . fromPrimalS . AstMaxIndexS
              . astSpanPrimalS . unAstNoSimplifyS
  sfloor = AstNoSimplifyS . fromPrimalS . AstFloorS
           . astSpanPrimalS . unAstNoSimplifyS
  siota = AstNoSimplifyS . fromPrimalS $ AstIotaS
  sindex v ix =
    AstNoSimplifyS $ AstIndexS (unAstNoSimplifyS v) (unAstNoSimplify <$> ix)
  ssum = AstNoSimplifyS . AstSumS . unAstNoSimplifyS
  sscatter t f = AstNoSimplifyS $ AstScatterS (unAstNoSimplifyS t)
                 $ funToAstIndexS
                     (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                       -- this introduces new variable names
  sfromList = AstNoSimplifyS . AstFromListS . map unAstNoSimplifyS
  sfromVector = AstNoSimplifyS . AstFromVectorS . V.map unAstNoSimplifyS
  sreplicate = AstNoSimplifyS . AstReplicateS . unAstNoSimplifyS
  sappend u v =
    AstNoSimplifyS $ AstAppendS (unAstNoSimplifyS u) (unAstNoSimplifyS v)
  sslice (_ :: Proxy i) Proxy = AstNoSimplifyS . AstSliceS @i . unAstNoSimplifyS
  sreverse = AstNoSimplifyS . AstReverseS . unAstNoSimplifyS
  stranspose (_ :: Proxy perm) =
    AstNoSimplifyS . AstTransposeS @perm . unAstNoSimplifyS
  sreshape = AstNoSimplifyS . AstReshapeS . unAstNoSimplifyS
  sbuild1 f =
    AstNoSimplifyS
    $ astBuild1VectorizeS (unAstNoSimplifyS . f . fmap AstNoSimplify)
  sgather t f = AstNoSimplifyS $ AstGatherS (unAstNoSimplifyS t)
                $ funToAstIndexS
                    (fmap unAstNoSimplify . f . fmap AstNoSimplify)
                      -- this introduces new variable names
  scast = AstNoSimplifyS . AstCastS . unAstNoSimplifyS
  sfromIntegral = AstNoSimplifyS . fromPrimalS . AstFromIntegralS
                  . astSpanPrimalS . unAstNoSimplifyS
  sconst = AstNoSimplifyS . fromPrimalS . AstConstS
  sletHVectorIn a f =
    AstNoSimplifyS
    $ astLetHVectorInFunRawS (unAstNoSimplifyWrap a)
                             (unAstNoSimplifyS . f . noSimplifyHVector)
  sletHFunIn a f = AstNoSimplifyS $ astLetHFunInFunRawS a (unAstNoSimplifyS . f)
  sfromR = AstNoSimplifyS . AstSFromR . unAstNoSimplify
  sconstant = AstNoSimplifyS . fromPrimalS . unAstNoSimplifyS
    -- exceptionally we do simplify AstConstant to avoid long boring chains
  sprimalPart = AstNoSimplifyS . astSpanPrimalS . unAstNoSimplifyS
  sdualPart = AstNoSimplifyS . astSpanDualS . unAstNoSimplifyS
  sD u u' =
    AstNoSimplifyS $ astSpanDS (unAstNoSimplifyS u) (unAstNoSimplifyS u')
  sScale s t = AstNoSimplifyS $ astDualPartS
               $ AstConstantS (unAstNoSimplifyS s)
                 * AstDS 0 (unAstNoSimplifyS t)

instance AstSpan s => HVectorTensor (AstNoSimplify s) (AstNoSimplifyS s) where
  dshape = shapeAstHVector . unAstNoSimplifyWrap
  dmkHVector =
    AstNoSimplifyWrap . AstMkHVector . unNoSimplifyHVector
  dlambda shss f = AstLambda
                   $ fun1LToAst shss $ \ !vvars !ll -> (vvars, unHFun f ll)
  dHApply t ll =
    AstNoSimplifyWrap $ AstHApply t (map unNoSimplifyHVector ll)
  dunHVector (AstNoSimplifyWrap (AstMkHVector l)) = noSimplifyHVector l
  dunHVector (AstNoSimplifyWrap hVectorOf) =
    let f :: Int -> DynamicTensor VoidTensor -> AstDynamic s
        f i = \case
          DynamicRankedDummy @r @sh _ _ ->
            withListSh (Proxy @sh) $ \(_ :: ShapeInt n) ->
              DynamicRanked @r @n $  AstProject hVectorOf i
          DynamicShapedDummy @r @sh _ _ ->
            DynamicShaped @r @sh $ AstProjectS hVectorOf i
    in noSimplifyHVector
       $ V.imap f $ shapeAstHVector hVectorOf
  dletHVectorInHVector a f =
    AstNoSimplifyWrap
    $ astLetHVectorInHVectorFunRaw (unAstNoSimplifyWrap a)
                                   (unAstNoSimplifyWrap . f . noSimplifyHVector)
  dletHFunInHVector t f =
    AstNoSimplifyWrap
    $ astLetHFunInHVectorFunRaw t (unAstNoSimplifyWrap . f)
  rletInHVector u f =
    AstNoSimplifyWrap
    $ astLetInHVectorFunRaw (unAstNoSimplify u)
                            (unAstNoSimplifyWrap . f . AstNoSimplify)
  sletInHVector u f =
    AstNoSimplifyWrap
    $ astLetInHVectorFunRawS (unAstNoSimplifyS u)
                             (unAstNoSimplifyWrap . f . AstNoSimplifyS)
  dbuild1 k f = AstNoSimplifyWrap
                $ astBuildHVector1Vectorize
                    k (unAstNoSimplifyWrap . f . AstNoSimplify)
  rrev f parameters0 hVector =  -- we don't have an AST constructor to hold it
    AstNoSimplifyWrap
    $ rrev f parameters0 (unNoSimplifyHVector hVector)
  drevDt = drevDt @(AstRanked s)
  dfwd = dfwd @(AstRanked s)
  dmapAccumRDer _ k accShs bShs eShs f df rf acc0 es =
    AstNoSimplifyWrap
    $ AstMapAccumRDer k accShs bShs eShs f df rf (unAstNoSimplifyWrap acc0)
                                                 (unAstNoSimplifyWrap es)
  dmapAccumLDer _ k accShs bShs eShs f df rf acc0 es =
    AstNoSimplifyWrap
    $ AstMapAccumLDer k accShs bShs eShs f df rf (unAstNoSimplifyWrap acc0)
                                                 (unAstNoSimplifyWrap es)

unNoSimplifyHVector :: HVector (AstNoSimplify s) -> HVector (AstRanked s)
unNoSimplifyHVector =
  let f (DynamicRanked (AstNoSimplify t)) = DynamicRanked t
      f (DynamicShaped (AstNoSimplifyS t)) = DynamicShaped t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f

noSimplifyHVector :: HVector (AstRanked s) -> HVector (AstNoSimplify s)
noSimplifyHVector =
  let f (DynamicRanked t) = DynamicRanked $ AstNoSimplify t
      f (DynamicShaped t) = DynamicShaped $ AstNoSimplifyS t
      f (DynamicRankedDummy p1 p2) = DynamicRankedDummy p1 p2
      f (DynamicShapedDummy p1 p2) = DynamicShapedDummy p1 p2
  in V.map f
