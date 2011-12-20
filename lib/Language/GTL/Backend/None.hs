{-# LANGUAGE TypeFamilies #-}
{-| This is a dummy backend that doesn't offer any formalism to specify models or verify contracts.
    It is only used to provide a backend for testing purporses (Or if you are too lazy to write components). -}
module Language.GTL.Backend.None where

import Language.GTL.Backend
import Data.Map as Map

-- | The none backend data type
data None = None

instance GTLBackend None where
  data GTLBackendModel None = NoneData
  backendName _ = "none"
  initBackend _ _ args = return NoneData
  backendGetAliases _ _ = Map.empty
  typeCheckInterface _ _ x = return x
  cInterface _ _ = CInterface
    { cIFaceIncludes = []
    , cIFaceStateType = []
    , cIFaceInputType = []
    , cIFaceStateInit = const ""
    , cIFaceIterate = \_ _ -> ""
    , cIFaceGetOutputVar = \_ _ _ -> Just ""
    , cIFaceGetInputVar = \_ _ _ -> Just ""
    , cIFaceTranslateType = \_ -> ("","",False)
    , cIFaceTranslateValue = \_ -> CValue ""
    }
  backendVerify _ _ _ _ _ _ _ _ _ = return Nothing
