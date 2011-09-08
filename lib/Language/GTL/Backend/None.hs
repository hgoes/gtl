{-# LANGUAGE TypeFamilies #-}
{-| This is a dummy backend that doesn't offer any formalism to specify models or verify contracts.
    It is only used to provide a backend for testing purporses (Or if you are too lazy to write components). -}
module Language.GTL.Backend.None where

import Language.GTL.Backend

-- | The none backend data type
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
  backendVerify _ _ _ _ _ _ _ = return Nothing
