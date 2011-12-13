{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
{-| Provides an abstraction over many different synchronized formalisms.
 -}
module Language.GTL.Backend where

import Language.GTL.Expression
import Language.GTL.Types
import Data.Map as Map
import Data.MapMonad (unionWithKeyM)
import Prelude hiding (mapM)
import Control.Monad.Error (MonadError(..))

import Misc.ProgramOptions as Opts

-- | Represents the input and output variables of a model and associates types with them.
type ModelInterface = (Map String GTLType,Map String GTLType)

-- | A GTLBackend is a synchronized formalism that can be used to specify models and perform verification.
class GTLBackend b where
  -- | The backend model is data that is loaded once and contains enough information to perform verification tasks on a synchronous model
  data GTLBackendModel b
  -- | The name of the backend. Used to determine which backend to load.
  backendName :: b -> String
  -- | Initialize a backend with a list of parameters
  initBackend :: b -> Opts.Options -> [String] -> IO (GTLBackendModel b)
  backendGetAliases :: b -> GTLBackendModel b -> Map String GTLType
  -- | Perform type checking on the synchronized model
  typeCheckInterface :: MonadError String m =>
                        b -- ^ The backend
                        -> GTLBackendModel b -- ^ The backend data
                        -> ModelInterface -- ^ A type mapping for the in- and outputs
                        -> m ModelInterface
  -- | Get the C-interface of a GTL model
  cInterface :: b -- ^ The backend
                -> GTLBackendModel b -- ^ The backend data
                -> CInterface
  -- | Perform a backend-specific model checking algorithm.
  --   Returns `Nothing' if the result is undecidable and `Just' `True', if the verification goal holds.
  backendVerify :: b -> GTLBackendModel b
                   -> Integer -- ^ Cycle time
                   -> TypedExpr String -- ^ Contract
                   -> Map String GTLType -- ^ Local variables of the model
                   -> Map String (GTLType, GTLConstant) -- ^ Variables which get a constant value
                   -> Opts.Options -- ^ Options
                   -> String -- ^ Name of the GTL file without extension
                   -> IO (Maybe Bool)

-- | A C-interface is information that is needed to integrate a C-state machine.
data CInterface = CInterface
                  { -- | A list of C-headers to be included
                    cIFaceIncludes :: [String],
                    -- | A list of C-types that together form the signature of the state of the state machine
                    cIFaceStateType :: [(String,String,Bool)],
                    -- | The type signature of the input variables. Input variables aren't considered state.
                    cIFaceInputType :: [(String,String,Bool)],
                    -- | Generate a call to initialize the state machine
                    cIFaceStateInit :: [String] -> String,
                    -- | Perform one iteration of the state machine
                    cIFaceIterate :: [String] -> [String] -> String,
                    -- | Extract an output variable from the machine state
                    cIFaceGetOutputVar :: [String] -> String -> [Integer] -> Maybe String,
                    -- | Extract an input variable from the state machine
                    cIFaceGetInputVar :: [String] -> String -> [Integer] -> Maybe String,
                    -- | Translate a haskell type to C
                    cIFaceTranslateType :: GTLType -> (String,String,Bool),
                    -- | Translate a haskell value to C
                    cIFaceTranslateValue :: GTLConstant -> CExpr
                  }

data CExpr = CValue String
           | CArray [CExpr]

-- | Merge two type-mappings into one, report conflicting types
mergeTypes :: MonadError String m => Map String GTLType -> Map String GTLType -> m (Map String GTLType)
mergeTypes m1 m2
  = unionWithKeyM (\name tp1 tp2 -> if tp1 == tp2
                                   then return tp1
                                   else throwError $ "Type error for variable "++name++
                                        ": gtl-specification says it's "++show tp1++
                                        ", but the backend says it's "++show tp2
                     ) m1 m2
