{-# LANGUAGE TypeFamilies #-}
module Language.GTL.Backend where

import Language.GTL.Syntax
import Data.Map as Map
import Data.Traversable
import Prelude hiding (mapM)
import Data.Typeable
import Data.Dynamic

class GTLBackend b where
  data GTLBackendData b
  backendName :: b -> String
  initBackend :: b -> [String] -> IO (GTLBackendData b)
  typeCheckInterface :: b -> GTLBackendData b -> Map String TypeRep -> Map String TypeRep -> Either String (Map String TypeRep,Map String TypeRep)
  cInterface :: b -> GTLBackendData b -> CInterface
  backendVerify :: b -> GTLBackendData b -> Expr String Bool -> IO (Maybe Bool)

data CInterface = CInterface
                  { cIFaceIncludes :: [String]
                  , cIFaceStateType :: [String]
                  , cIFaceInputType :: [String]
                  , cIFaceStateInit :: [String] -> String
                  , cIFaceIterate :: [String] -> [String] -> String
                  , cIFaceGetOutputVar :: [String] -> String -> String
                  , cIFaceGetInputVar :: [String] -> String -> String
                  , cIFaceTranslateType :: TypeRep -> String
                  }

mergeTypes :: Map String TypeRep -> Map String TypeRep -> Either String (Map String TypeRep)
mergeTypes m1 m2 
  = mapM id $
    Map.unionWithKey (\name (Right tp1) (Right tp2) -> if tp1 == tp2
                                                       then Right tp1
                                                       else Left $ "Type error for variable "++name++
                                                            ": gtl-specification says it's "++show tp1++
                                                            ", but the backend says it's "++show tp2
                     ) (fmap (Right) m1) (fmap (Right) m2)