-- | Predefined common functions for pretty-printing AST terms
-- in a few useful configurations.
module HordeAd.Core.PPEngine
  ( printAstVarName
  , printAstSimple, printAstPretty, printAstPrettyButNested
  , printArtifactSimple, printArtifactPretty
  , printArtifactPrimalSimple, printArtifactPrimalPretty
  ) where

import Prelude

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM

import HordeAd.Core.Ast
import HordeAd.Core.PPTools

-- * Pretty-printing terms in a few useful configurations

{-# INLINE printAstVarRename #-}
printAstVarRename :: KnownSpan s
                  => IntMap String -> AstVarName '(s, y) -> String
printAstVarRename renames var =
  printAstVar (defaulPrintConfig {varRenames = renames}) var ""

{-# INLINE printAstSimpleRename #-}
printAstSimpleRename :: KnownSpan s
                     => IntMap String -> AstTensor ms s y -> String
printAstSimpleRename renames t =
  printAst
    (defaulPrintConfig {loseRoudtrip = False, varRenames = renames}) 0 t ""

{-# INLINE printAstPrettyRename #-}
printAstPrettyRename :: KnownSpan s
                     => IntMap String -> AstTensor ms s y -> String
printAstPrettyRename renames t =
  printAst (defaulPrintConfig {varRenames = renames}) 0 t ""

{-# INLINE printAstVarName #-}
printAstVarName :: KnownSpan s
                => AstVarName '(s, y) -> String
printAstVarName var =
  printAstVar defaulPrintConfig var ""

-- | Print an AST term in a form close to being able to roundtrip,
-- including explicit sharing preservation.
{-# INLINE printAstSimple #-}
printAstSimple :: KnownSpan s
               => AstTensor ms s y -> String
printAstSimple t =
  printAst (defaulPrintConfig {loseRoudtrip = False}) 0 t ""

-- | Print an AST term in a readable form that does not roundtrip,
-- and where Haskell @let@ (sharing on Haskell heap) is used instead
-- of explicit sharing of subterms.
{-# INLINE printAstPretty #-}
printAstPretty :: KnownSpan s
               => AstTensor ms s y -> String
printAstPretty t =
  printAst defaulPrintConfig 0 t ""

{-# INLINE printAstPrettyButNested #-}
printAstPrettyButNested :: KnownSpan s
                        => AstTensor ms s y -> String
printAstPrettyButNested t =
  printAst (defaulPrintConfig {ignoreNestedLambdas = False}) 0 t ""

{-# INLINE printArtifactSimple #-}
printArtifactSimple :: AstArtifactRev x z -> String
printArtifactSimple AstArtifactRev{..} =
  let nDt = fromEnum (varNameToAstVarId artVarDtRev) - 100000000
      renames = IM.singleton nDt "dret"
      varsPP = [ printAstVarRename renames artVarDtRev
               , printAstVarRename renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstSimpleRename renames artDerivativeRev

{-# INLINE printArtifactPretty #-}
printArtifactPretty :: AstArtifactRev x z -> String
printArtifactPretty AstArtifactRev{..} =
  let nDt = fromEnum (varNameToAstVarId artVarDtRev) - 100000000
      renames = IM.singleton nDt "dret"
      varsPP = [ printAstVarRename renames artVarDtRev
               , printAstVarRename renames artVarDomainRev ]
  in "\\" ++ unwords varsPP
          ++ " -> " ++ printAstPrettyRename renames artDerivativeRev

{-# INLINE printArtifactPrimalSimple #-}
printArtifactPrimalSimple :: AstArtifactRev x z -> String
printArtifactPrimalSimple AstArtifactRev{..} =
  "\\" ++ printAstVarName artVarDomainRev
       ++ " -> " ++ printAstSimple artPrimalRev

{-# INLINE printArtifactPrimalPretty #-}
printArtifactPrimalPretty :: AstArtifactRev x z -> String
printArtifactPrimalPretty AstArtifactRev{..} =
  "\\" ++ printAstVarName artVarDomainRev
       ++ " -> " ++ printAstPretty artPrimalRev
