{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Conversion constructors.
module HordeAd.Core.Conversion
  ( TKConversion(..), convCmp, lemTKAllNumConvert, lemTKAllNumConvertForward
  , convertSTK, convertFTK, buildTKConversion
  ) where

import Prelude hiding ((.))

import Control.Category
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import GHC.TypeLits (type (+))

import Data.Array.Nested (MapJust, Replicate, type (++))
import Data.Array.Nested.Convert
  (shrFromShX, shsFromSSX, shsFromShX, shxFromShR, shxFromShS)
import Data.Array.Nested.Lemmas
import Data.Array.Nested.Mixed.Shape
import Data.Array.Nested.Shaped.Shape
import Data.Array.Nested.Types (unsafeCoerceRefl)

import HordeAd.Core.TensorKind
import HordeAd.Core.Types

-- | This is copied, with modifications, from ox-arrays.
--
-- This is a recipe for converting arrays, not always followed,
-- and a proof a conversion is possible, with some proof obligations
-- delayed to runtime (in ConvXS' and ConvXX', where not only the ranks
-- of the shapes need to agree, but also the dimensions of the input
-- array and of the output shape, which is not all captured in the type).
-- As in ox-arrays, conversions only change the meta-data, not the underlying
-- vector representation of the array.
type role TKConversion nominal nominal
data TKConversion (a :: TK) (b :: TK) where
  ConvId  :: TKConversion a a
  ConvCmp :: TKConversion b c -> TKConversion a b -> TKConversion a c

  ConvRX  :: TKConversion (TKR2 n a) (TKX2 (Replicate n Nothing) a)
  ConvSX  :: TKConversion (TKS2 sh a) (TKX2 (MapJust sh) a)

  ConvXR  :: SingletonTK a -> TKConversion (TKX2 sh a) (TKR2 (Rank sh) a)
  ConvXS  :: TKConversion (TKX2 (MapJust sh) a) (TKS2 sh a)
  ConvXS' :: Rank sh ~ Rank sh'
          => FullShapeTK (TKS2 sh' a)
          -> TKConversion (TKX2 sh a) (TKS2 sh' a)

  ConvXX' :: Rank sh ~ Rank sh'
          => FullShapeTK (TKX2 sh' a)
          -> TKConversion (TKX2 sh a) (TKX2 sh' a)

  ConvRR  :: TKConversion a b -> TKConversion (TKR2 n a) (TKR2 n b)
  ConvSS  :: TKConversion a b -> TKConversion (TKS2 sh a) (TKS2 sh b)
  ConvXX  :: TKConversion a b -> TKConversion (TKX2 sh a) (TKX2 sh b)
  ConvT2  :: TKConversion a a'
          -> TKConversion b b'
          -> TKConversion (TKProduct a b) (TKProduct a' b')

  Conv0X  :: SingletonTK a -> TKConversion a (TKX2 '[] a)
  ConvX0  :: TKConversion (TKX2 '[] a) a

  ConvNest   :: SingletonTK (TKX2 sh a)
             -> TKConversion (TKX2 (sh ++ sh') a) (TKX2 sh (TKX2 sh' a))
  ConvUnnest :: TKConversion (TKX2 sh (TKX2 sh' a)) (TKX2 (sh ++ sh') a)

  ConvZip   :: SingletonTK a -> SingletonTK b
            -> TKConversion (TKProduct (TKX2 sh a) (TKX2 sh b))
                            (TKX2 sh (TKProduct a b))
  ConvUnzip :: SingletonTK a -> SingletonTK b
            -> TKConversion (TKX2 sh (TKProduct a b))
                            (TKProduct (TKX2 sh a) (TKX2 sh b))

deriving instance Show (TKConversion a b)

instance Category TKConversion where
  id = ConvId
  (.) = convCmp

-- TODO: expand
convCmp :: TKConversion b c -> TKConversion a b -> TKConversion a c
convCmp a b = case (a, b) of
  (_, ConvId) -> a
  (_, ConvCmp ConvId c) -> convCmp a c
  (ConvId, _) -> b
  (ConvCmp a1 a2, _) -> a1 . (a2 . b)
  (ConvSX, ConvXS) -> ConvId
  (ConvSX, ConvCmp ConvXS c) -> c
  (ConvXR{}, ConvRX @n) | Refl <- lemRankReplicate (Proxy @n) -> ConvId
  (ConvXR{}, ConvCmp (ConvRX @n) c) | Refl <- lemRankReplicate (Proxy @n) -> c
  (ConvXR stk, ConvXX'{}) -> ConvXR stk
  (ConvXR stk, ConvCmp ConvXX'{} c) -> convCmp (ConvXR stk) c
  (ConvXS @sh, ConvSX @sh') ->
    gcastWith (unsafeCoerceRefl :: sh :~: sh') $
    ConvId
  (ConvXS @sh, ConvCmp (ConvSX @sh') c) ->
    gcastWith (unsafeCoerceRefl :: sh :~: sh') $
    c
  (ConvXS, ConvXX' (FTKX sh x)) | Refl <- lemRankMapJust (shsFromShX sh) ->
    ConvXS' (FTKS (shsFromShX sh) x)
  (ConvXS, ConvCmp (ConvXX' (FTKX sh x)) c)
    | Refl <- lemRankMapJust (shsFromShX sh) ->
      convCmp (ConvXS' (FTKS (shsFromShX sh) x)) c
  (ConvXS' @_ @sh' _, ConvSX @sh) ->
    gcastWith (unsafeCoerceRefl :: sh :~: sh') $
    ConvId
  (ConvXS' @_ @sh' _, ConvCmp (ConvSX @sh) c) ->
    gcastWith (unsafeCoerceRefl :: sh :~: sh') $
    c
  (ConvXS' ftk, ConvXX'{}) -> ConvXS' ftk
  (ConvXS' ftk, ConvCmp ConvXX'{} c) -> convCmp (ConvXS' ftk) c
  (ConvXS' (FTKS ZSS _), Conv0X stk) -> convCmp ConvXS (Conv0X stk)
  (ConvXS' (FTKS ZSS _), ConvCmp (Conv0X stk) c) ->
    convCmp (convCmp ConvXS (Conv0X stk)) c
  (ConvXX' ftk, ConvXX'{}) -> ConvXX' ftk
  (ConvXX' ftk, ConvCmp ConvXX'{} c) -> convCmp (ConvXX' ftk) c
  (ConvXX' (FTKX ZSX _), Conv0X stk) -> Conv0X stk
  (ConvXX' (FTKX ZSX _), ConvCmp (Conv0X stk) c) -> convCmp (Conv0X stk) c
  (ConvRR a', ConvRR b') -> ConvRR (convCmp a' b')
  (ConvRR a', ConvCmp (ConvRR b') c) -> convCmp (ConvRR (convCmp a' b')) c
  (ConvSS a', ConvSS b') -> ConvSS (convCmp a' b')
  (ConvSS a', ConvCmp (ConvSS b') c) -> convCmp (ConvSS (convCmp a' b')) c
  (ConvXX a', ConvXX b') -> convXX (convCmp a' b')
  (ConvXX a', ConvCmp (ConvXX b') c) -> convCmp (convXX (convCmp a' b')) c
  (Conv0X{}, ConvX0) -> ConvId
  (Conv0X{}, ConvCmp ConvX0 c) -> c
  (ConvX0, ConvXX' @sh (FTKX ZSX _)) ->
    gcastWith (unsafeCoerceRefl :: sh :~: '[]) $
    ConvX0
  (ConvX0, ConvCmp (ConvXX' @sh (FTKX ZSX _)) c) ->
    gcastWith (unsafeCoerceRefl :: sh :~: '[]) $
    convCmp ConvX0 c
  (ConvX0, Conv0X{}) -> ConvId
  (ConvX0, ConvCmp Conv0X{} c) -> c
  (ConvT2 a1 a2, ConvT2 b1 b2) -> convT2 (convCmp a1 b1) (convCmp a2 b2)
  (ConvT2 a1 a2, ConvCmp (ConvT2 b1 b2) c) ->
    convCmp (convT2 (convCmp a1 b1) (convCmp a2 b2)) c
  (ConvNest @sh @_ @sh' _, ConvUnnest @sh2 @sh2') ->
    gcastWith (unsafeCoerceRefl :: sh :~: sh2) $
    gcastWith (unsafeCoerceRefl :: sh' :~: sh2') $
    ConvId
  (ConvNest @sh @_ @sh' _, ConvCmp (ConvUnnest @sh2 @sh2') c) ->
    gcastWith (unsafeCoerceRefl :: sh :~: sh2) $
    gcastWith (unsafeCoerceRefl :: sh' :~: sh2') $
    c
-- not enough type info in the AST:
-- (ConvNest (STKX sh x), ConvXX d) ->
--   convCmp (ConvXX (ConvXX d)) (ConvNest (STKX sh (convertSTKBack d x)))
  (ConvUnnest, ConvNest{}) -> ConvId
  (ConvUnnest, ConvCmp ConvNest{} c) -> c
  (ConvXX d, ConvUnnest) ->
    convCmp ConvUnnest (convXX (convXX d))
  (ConvXX d, ConvCmp ConvUnnest c) ->
    convCmp ConvUnnest (convCmp (convXX (convXX d)) c)
  (ConvZip{}, ConvUnzip{}) -> ConvId
  (ConvZip{}, ConvCmp (ConvUnzip{}) c) -> c
  (ConvXX' (FTKX sh (FTKProduct c1 c2)), ConvZip stk1 stk2) ->
    convCmp (ConvZip stk1 stk2)
            (convT2 (ConvXX' (FTKX sh c1)) (ConvXX' (FTKX sh c2)))
  (ConvXX' (FTKX sh (FTKProduct c1 c2)), ConvCmp (ConvZip stk1 stk2) c) ->
    convCmp (ConvZip stk1 stk2)
            (convCmp (convT2 (ConvXX' (FTKX sh c1)) (ConvXX' (FTKX sh c2))) c)
  (ConvUnzip{}, ConvZip{}) -> ConvId
  (ConvUnzip{}, ConvCmp (ConvZip{}) c) -> c
  (ConvUnzip stk1 stk2, ConvXX' (FTKX sh (FTKProduct c1 c2))) ->
    convCmp (convT2 (ConvXX' (FTKX sh c1)) (ConvXX' (FTKX sh c2)))
            (ConvUnzip stk1 stk2)
  (ConvUnzip stk1 stk2, ConvCmp (ConvXX' (FTKX sh (FTKProduct c1 c2))) c) ->
    convCmp (convT2 (ConvXX' (FTKX sh c1)) (ConvXX' (FTKX sh c2)))
            (convCmp (ConvUnzip stk1 stk2) c)
  _ -> ConvCmp a b

convT2  :: TKConversion a a'
        -> TKConversion b b'
        -> TKConversion (TKProduct a b) (TKProduct a' b')
convT2 ConvId ConvId = ConvId
convT2 a b = ConvT2 a b

convXX  :: TKConversion a b -> TKConversion (TKX2 sh a) (TKX2 sh b)
convXX ConvId = ConvId
convXX a = ConvXX a

lemTKAllNumConvert :: TKAllNum b
                   => TKConversion a b -> Dict0 (TKAllNum a)
lemTKAllNumConvert = \case
  ConvId -> Dict0
  ConvCmp c1 c2 | Dict0 <- lemTKAllNumConvert c1 ->
    lemTKAllNumConvert c2
  ConvRX -> Dict0
  ConvSX -> Dict0
  ConvXR{}  -> Dict0
  ConvXS -> Dict0
  ConvXS'{} -> Dict0
  ConvXX'{} -> Dict0
  ConvRR c | Dict0 <- lemTKAllNumConvert c -> Dict0
  ConvSS c | Dict0 <- lemTKAllNumConvert c -> Dict0
  ConvXX c | Dict0 <- lemTKAllNumConvert c -> Dict0
  ConvT2 c1 c2 | Dict0 <- lemTKAllNumConvert c1
               , Dict0 <- lemTKAllNumConvert c2 -> Dict0
  Conv0X{} -> Dict0
  ConvX0 -> Dict0
  ConvNest{} -> Dict0
  ConvUnnest -> Dict0
  ConvZip{} -> Dict0
  ConvUnzip{} -> Dict0

lemTKAllNumConvertForward :: TKAllNum a
                          => TKConversion a b -> Dict0 (TKAllNum b)
lemTKAllNumConvertForward = \case
  ConvId -> Dict0
  ConvCmp c1 c2 | Dict0 <- lemTKAllNumConvertForward c2 ->
    lemTKAllNumConvertForward c1
  ConvRX -> Dict0
  ConvSX -> Dict0
  ConvXR{}  -> Dict0
  ConvXS -> Dict0
  ConvXS'{} -> Dict0
  ConvXX'{} -> Dict0
  ConvRR c | Dict0 <- lemTKAllNumConvertForward c -> Dict0
  ConvSS c | Dict0 <- lemTKAllNumConvertForward c -> Dict0
  ConvXX c | Dict0 <- lemTKAllNumConvertForward c -> Dict0
  ConvT2 c1 c2 | Dict0 <- lemTKAllNumConvertForward c1
               , Dict0 <- lemTKAllNumConvertForward c2 -> Dict0
  Conv0X{} -> Dict0
  ConvX0 -> Dict0
  ConvNest{} -> Dict0
  ConvUnnest -> Dict0
  ConvZip{} -> Dict0
  ConvUnzip{} -> Dict0

convertSTK :: TKConversion a b -> SingletonTK a -> SingletonTK b
convertSTK = \cases
  ConvId astk -> astk
  (ConvCmp c1 c2) astk -> convertSTK c1 (convertSTK c2 astk)
  ConvRX (STKR n a) -> STKX (ssxReplicate n) a
  ConvSX (STKS sh a) -> STKX (ssxFromShX $ shxFromShS sh) a
  (ConvXR _stk) (STKX ssx a) -> STKR (ssxRank ssx) a
  ConvXS (STKX ssx a) -> STKS (shsFromSSX ssx) a
  (ConvXS' (FTKS sh _x)) (STKX _ssx2 a) -> STKS sh a
  (ConvXX' (FTKX shx _x)) (STKX _ssx2 a) -> STKX (ssxFromShX shx) a
  (ConvRR c) (STKR n a) -> STKR n (convertSTK c a)
  (ConvSS c) (STKS sh a) -> STKS sh (convertSTK c a)
  (ConvXX c) (STKX ssx a) -> STKX ssx (convertSTK c a)
  (ConvT2 c1 c2) (STKProduct stk1 stk2) ->
    STKProduct (convertSTK c1 stk1) (convertSTK c2 stk2)
  (Conv0X _stk) stk -> STKX ZKX stk
  ConvX0 (STKX ZKX stk) -> stk
  (ConvNest (STKX ssx x)) (STKX shsh' _x) ->
    STKX ssx (STKX (ssxDropSSX ssx shsh') x)
  ConvUnnest (STKX sh (STKX sh' x)) -> STKX (sh `ssxAppend` sh') x
  (ConvZip _ _) (STKProduct (STKX sh a1) (STKX _sh a2)) ->
    STKX sh (STKProduct a1 a2)
  (ConvUnzip _ _) (STKX sh (STKProduct a1 a2)) ->
    STKProduct (STKX sh a1) (STKX sh a2)

convertFTK :: TKConversion a b -> FullShapeTK a -> FullShapeTK b
convertFTK = \cases
  ConvId aftk -> aftk
  (ConvCmp c1 c2) aftk -> convertFTK c1 (convertFTK c2 aftk)
  ConvRX (FTKR shr a) -> FTKX (shxFromShR shr) a
  ConvSX (FTKS sh a) -> FTKX (shxFromShS sh) a
  (ConvXR _stk) (FTKX shx a) -> FTKR (shrFromShX shx) a
  ConvXS (FTKX shx a) -> FTKS (shsFromShX shx) a
  (ConvXS' ftk) _ -> ftk
  (ConvXX' ftk) _ -> ftk
  (ConvRR c) (FTKR shr a) -> FTKR shr (convertFTK c a)
  (ConvSS c) (FTKS sh a) -> FTKS sh (convertFTK c a)
  (ConvXX c) (FTKX shx a) -> FTKX shx (convertFTK c a)
  (ConvT2 c1 c2) (FTKProduct ftk1 ftk2) ->
    FTKProduct (convertFTK c1 ftk1) (convertFTK c2 ftk2)
  (Conv0X _stk) ftk -> FTKX ZSX ftk
  ConvX0 (FTKX ZSX ftk) -> ftk
  (ConvNest @_ @_ @sh' (STKX ssx _x)) (FTKX shsh' x) ->
    FTKX (shxTakeSSX (Proxy @sh') ssx shsh') (FTKX (shxDropSSX ssx shsh') x)
  ConvUnnest (FTKX sh (FTKX sh' x)) -> FTKX (sh `shxAppend` sh') x
  (ConvZip _ _) (FTKProduct (FTKX sh a1) (FTKX _sh a2)) ->
    FTKX sh (FTKProduct a1 a2)
  (ConvUnzip _ _) (FTKX sh (FTKProduct a1 a2)) ->
    FTKProduct (FTKX sh a1) (FTKX sh a2)

buildTKConversion :: SNat k -> FullShapeTK a
                  -> TKConversion a b
                  -> TKConversion (BuildTensorKind k a) (BuildTensorKind k b)
buildTKConversion k aftk c0 = case c0 of
  ConvId -> ConvId
  ConvCmp c1 c2 -> convCmp (buildTKConversion k (convertFTK c2 aftk) c1)
                           (buildTKConversion k aftk c2)
  ConvRX | FTKR @n shr xstk <- aftk
         , Refl <- lemRankReplicate (Proxy @n)
         , Refl <- lemRankReplicate (Proxy @(1 + n)) ->
    convCmp (ConvXX' (FTKX (SKnown k :$% shxFromShR shr) xstk)) ConvRX
  ConvSX -> ConvSX
  ConvXR stk -> ConvXR stk
  ConvXS -> ConvXS
  ConvXS' ftk -> ConvXS' (buildFTK k ftk)
  ConvXX' ftk -> ConvXX' (buildFTK k ftk)
  ConvRR c -> ConvRR c
  ConvSS c -> ConvSS c
  ConvXX c -> ConvXX c
  ConvT2 c1 c2 | FTKProduct ftk1 ftk2 <- aftk ->
    ConvT2 (buildTKConversion k ftk1 c1) (buildTKConversion k ftk2 c2)
  Conv0X _astk -> case aftk of
    FTKScalar -> ConvSX
    FTKR @n shr x | Refl <- lemRankReplicate (Proxy @n)
                  , Refl <- lemRankReplicate (Proxy @(1 + n)) ->
      convCmp (ConvXX (ConvXR (ftkToSTK x)))
              (convCmp (ConvNest (STKX (SKnown k :!% ZKX) (ftkToSTK x)))
                       (convCmp
                          (ConvXX' (FTKX (SKnown k :$% shxFromShR shr) x))
                          ConvRX))
    FTKS _sh x ->
      convCmp (ConvXX ConvXS)
              (convCmp (ConvNest (STKX (SKnown k :!% ZKX) (ftkToSTK x)))
                       ConvSX)
    FTKX _ssx x -> ConvNest (STKX (SKnown k :!% ZKX) (ftkToSTK x))
    FTKProduct aftk1 aftk2 ->
      buildTKConversion
        k aftk (convCmp (ConvZip (ftkToSTK aftk1) (ftkToSTK aftk2))
                        (ConvT2 (Conv0X (ftkToSTK aftk1))
                                (Conv0X (ftkToSTK aftk2))))
  ConvX0 -> case aftk of
    FTKX ZSX FTKScalar -> ConvXS
    FTKX ZSX (FTKR @n _n x) | Refl <- lemRankReplicate (Proxy @n) ->
      convCmp (ConvXR (ftkToSTK x))
              (convCmp ConvUnnest (ConvXX ConvRX))
    FTKX ZSX FTKS{} ->
      convCmp ConvXS
              (convCmp ConvUnnest (ConvXX ConvSX))
    FTKX ZSX FTKX{} -> ConvUnnest
    FTKX ZSX (FTKProduct aftk1 aftk2) ->
      buildTKConversion
        k aftk (convCmp (ConvT2 ConvX0 ConvX0)
                        (ConvUnzip (ftkToSTK aftk1) (ftkToSTK aftk2)))
  ConvNest (STKX sh x) -> ConvNest (STKX (SKnown k :!% sh) x)
  ConvUnnest -> ConvUnnest
  ConvZip astk1 astk2 -> ConvZip astk1 astk2
  ConvUnzip astk1 astk2 -> ConvUnzip astk1 astk2
