-- | Data types representing a parsed GTL file.
module Language.GTL.Syntax where

import Language.GTL.Token (UnOp(..),BinOp(..))
import Control.Monad.Error
import Data.Map as Map
import Data.Word
import Data.Typeable

-- | A GTL file is a list of declarations.
data Declaration = Model ModelDecl -- ^ Declares a model.
                 | Connect ConnectDecl -- ^ Declares a connection between two models.
                 | Verify VerifyDecl -- ^ Declares a property that needs to be verified.
                 deriving Show

-- | Declares a synchronous model.
data ModelDecl = ModelDecl
                 { modelName :: String -- ^ The name of the model in the GTL formalism.
                 , modelType :: String -- ^ The synchronous formalism the model is written in (for example /scade/)
                 , modelArgs :: [String] -- ^ Arguments specific to the synchronous formalism, for example in which file the model is specified etc.
                 , modelContract :: [GExpr] -- ^ A list of contracts that this model fulfills.
                 , modelInits :: [(String,InitExpr)] -- ^ A list of initializations for the variables of the model.
                 , modelInputs :: Map String String -- ^ Declared inputs of the model with their corresponding type
                 , modelOutputs :: Map String String -- ^ Declared outputs of a model
                 } deriving Show

-- | Declares a connection between two variables
data ConnectDecl = ConnectDecl
                   { connectFromModel :: String -- ^ Model of the source variable
                   , connectFromVariable :: String -- ^ Name of the source variable
                   , connectToModel :: String -- ^ Model of the target variable
                   , connectToVariable :: String -- ^ Name of the target variable
                   } deriving Show

-- | A list of formulas to verify.
data VerifyDecl = VerifyDecl
                  { verifyFormulas :: [GExpr] -- ^ The formulas to be verified.
                  } deriving Show

-- | An untyped expression type.
--   Used internally in the parser.
data GExpr = GBin BinOp GExpr GExpr
           | GUn UnOp GExpr
           | GConst Int
           | GConstBool Bool
           | GVar (Maybe String) String
           | GSet [Integer]
           | GExists String (Maybe String) String GExpr
           deriving (Show,Eq,Ord)

-- | Information about the initialization of a variable.
data InitExpr = InitAll -- ^ The variable is initialized with all possible values.
              | InitOne Integer -- ^ The variable is initialized with a specific value.
              deriving (Show,Eq)