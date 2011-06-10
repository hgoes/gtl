{-# LANGUAGE TypeFamilies #-}
module Language.GTL.Backend.None where

import Language.GTL.Backend

data None = None

instance GTLBackend None where
  data GTLBackendModel None = NoneData
  backendName _ = "none"
  initBackend _ args = return NoneData
  typeCheckInterface _ _ x = Right x
  cInterface _ _ = CInterface
    { cIFaceIncludes = []
    , cIFaceStateType = []
    , cIFaceInputType = []
    , cIFaceStateInit = const ""
    , cIFaceIterate = \_ _ -> ""
    , cIFaceGetOutputVar = \_ _ -> ""
    , cIFaceGetInputVar = \_ _ -> ""
    , cIFaceTranslateType = \_ -> ""
    , cIFaceTranslateValue = \_ -> ""
    }
  backendVerify _ _ _ = return Nothing
