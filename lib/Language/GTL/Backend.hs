{-# LANGUAGE TypeFamilies #-}
{-| Provides an abstraction over many different synchronized formalisms.
 -}
module Language.GTL.Backend where

import Language.GTL.Expression
import Data.Map as Map
import Data.Traversable
import Prelude hiding (mapM)
import Data.Typeable
import Data.Dynamic

type ModelInterface = (Map String TypeRep,Map String TypeRep)

-- | A GTLBackend is a synchronized formalism that can be used to specify models and perform verification.
class GTLBackend b where
  -- | The backend model is data that is loaded once and contains enough information to perform verification tasks on a synchronous model
  data GTLBackendModel b
  -- | The name of the backend. Used to determine which backend to load.
  backendName :: b -> String
  -- | Initialize a backend with a list of parameters
  initBackend :: b -> [String] -> IO (GTLBackendModel b)
  -- | Perform type checking on the synchronized model
  typeCheckInterface :: b -- ^ The backend
                        -> GTLBackendModel b -- ^ The backend data
                        -> ModelInterface -- ^ A type mapping for the in- and outputs
                        -> Either String ModelInterface
  -- | Get the C-interface of a GTL model
  cInterface :: b -- ^ The backend
                -> GTLBackendModel b -- ^ The backend data
                -> CInterface
  -- | Perform a backend-specific model checking algorithm.
  --   Returns `Nothing' if the result is undecidable and `Just' `True', if the verification goal holds.
  backendVerify :: b -> GTLBackendModel b -> Expr String Bool -> IO (Maybe Bool)

-- | A C-interface is information that is needed to integrate a C-state machine.
data CInterface = CInterface
                  { -- | A list of C-headers to be included
                    cIFaceIncludes :: [String],
                    -- | A list of C-types that together form the signature of the state of the state machine
                    cIFaceStateType :: [String],
                    -- | The type signature of the input variables. Input variables aren't considered state.
                    cIFaceInputType :: [String],
                    -- | Generate a call to initialize the state machine
                    cIFaceStateInit :: [String] -> String,
                    -- | Perform one iteration of the state machine
                    cIFaceIterate :: [String] -> [String] -> String,
                    -- | Extract an output variable from the machine state
                    cIFaceGetOutputVar :: [String] -> String -> String,
                    -- | Extract an input variable from the state machine
                    cIFaceGetInputVar :: [String] -> String -> String,
                    -- | Translate a haskell type to C
                    cIFaceTranslateType :: TypeRep -> String,
                    -- | Translate a haskell value to C
                    cIFaceTranslateValue :: Dynamic -> String
                  }

-- | Merge two type-mappings into one, report conflicting types
mergeTypes :: Map String TypeRep -> Map String TypeRep -> Either String (Map String TypeRep)
mergeTypes m1 m2 
  = mapM id $
    Map.unionWithKey (\name (Right tp1) (Right tp2) -> if tp1 == tp2
                                                       then Right tp1
                                                       else Left $ "Type error for variable "++name++
                                                            ": gtl-specification says it's "++show tp1++
                                                            ", but the backend says it's "++show tp2
                     ) (fmap (Right) m1) (fmap (Right) m2)