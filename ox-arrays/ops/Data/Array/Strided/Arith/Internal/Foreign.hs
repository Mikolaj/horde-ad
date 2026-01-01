{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Array.Strided.Arith.Internal.Foreign where

import Data.Int
import Foreign.C.Types
import Foreign.Ptr
import Language.Haskell.TH

import Data.Array.Strided.Arith.Internal.Lists


$(do
  let importsScal ttyp tyn =
        [("binary_" ++ tyn ++ "_vv_strided", [t| CInt -> Int64 -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("binary_" ++ tyn ++ "_sv_strided", [t| CInt -> Int64 -> Ptr Int64 -> Ptr $ttyp ->                  $ttyp -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("binary_" ++ tyn ++ "_vs_strided", [t| CInt -> Int64 -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp ->                  $ttyp -> IO () |])
        ,("unary_" ++ tyn ++ "_strided",     [t| CInt -> Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("reduce1_" ++ tyn,                 [t| CInt -> Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("reducefull_" ++ tyn,              [t| CInt -> Int64 -> Ptr Int64 -> Ptr Int64 -> Ptr $ttyp -> IO $ttyp |])
        ,("extremum_min_" ++ tyn,            [t| Ptr Int64 -> Int64 -> Ptr Int64 -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("extremum_max_" ++ tyn,            [t| Ptr Int64 -> Int64 -> Ptr Int64 -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("dotprodinner_" ++ tyn,            [t| Int64 -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ]

  let importsInt ttyp tyn =
        [("ibinary_" ++ tyn ++ "_vv_strided", [t| CInt -> Int64 -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("ibinary_" ++ tyn ++ "_sv_strided", [t| CInt -> Int64 -> Ptr Int64 -> Ptr $ttyp ->                  $ttyp -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("ibinary_" ++ tyn ++ "_vs_strided", [t| CInt -> Int64 -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp ->                  $ttyp -> IO () |])
        ]

  let importsFloat ttyp tyn =
        [("fbinary_" ++ tyn ++ "_vv_strided", [t| CInt -> Int64 -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("fbinary_" ++ tyn ++ "_sv_strided", [t| CInt -> Int64 -> Ptr Int64 -> Ptr $ttyp ->                  $ttyp -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ,("fbinary_" ++ tyn ++ "_vs_strided", [t| CInt -> Int64 -> Ptr Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr $ttyp ->                  $ttyp -> IO () |])
        ,("funary_" ++ tyn ++ "_strided",     [t| CInt -> Int64 -> Ptr $ttyp -> Ptr Int64 -> Ptr Int64 -> Ptr $ttyp -> IO () |])
        ]

  let generate types imports =
        sequence
          [ForeignD . ImportF CCall Unsafe ("oxarop_" ++ name) (mkName ("c_" ++ name)) <$> typ
          | arithtype <- types
          , (name, typ) <- imports (conT (atType arithtype)) (atCName arithtype)]
  decs1 <- generate typesList importsScal
  decs2 <- generate intTypesList importsInt
  decs3 <- generate floatTypesList importsFloat
  return (decs1 ++ decs2 ++ decs3))
