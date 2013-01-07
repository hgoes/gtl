-- | Data types representing a parsed GTL file.
module Language.GTL.Parser.Syntax where

import Language.GTL.Parser.Monad
import Language.GTL.Parser.Token (UnOp(..),BinOp(..))
import Language.GTL.Types
import Data.Map as Map

-- | A GTL file is a list of declarations.
data Declaration = Model ModelDecl -- ^ Declares a model.
                 | Connect ConnectDecl -- ^ Declares a connection between two models.
                 | Verify VerifyDecl -- ^ Declares a property that needs to be verified.
                 | Instance InstanceDecl
                 | TypeAlias String UnResolvedType
                 deriving Show

data ModelArgs = StrArg String | ConstantDecl String PExpr deriving Show

-- | Declares a synchronous model.
data ModelDecl = ModelDecl
                 { modelName :: String -- ^ The name of the model in the GTL formalism.
                 , modelType :: String -- ^ The synchronous formalism the model is written in (for example /scade/)
                 , modelArgs :: [ModelArgs] -- ^ Arguments specific to the synchronous formalism, for example in which file the model is specified etc.
                 , modelContract :: [Contract] -- ^ A list of contracts that this model fulfills.
                 , modelInits :: [(String,InitExpr)] -- ^ A list of initializations for the variables of the model.
                 , modelInputs :: Map String UnResolvedType -- ^ Declared inputs of the model with their corresponding type
                 , modelOutputs :: Map String UnResolvedType -- ^ Declared outputs of a model
                 , modelLocals :: Map String UnResolvedType
                 , modelCycleTime :: Integer -- ^ Cycle time given in us
                 } deriving Show

-- | Declares a connection between two variables
data ConnectDecl = ConnectDecl
                   { connectFromModel :: String -- ^ Model of the source variable
                   , connectFromVariable :: String -- ^ Name of the source variable
                   , connectFromIndices :: [Integer]
                   , connectToModel :: String -- ^ Model of the target variable
                   , connectToVariable :: String -- ^ Name of the target variable
                   , connectToIndices :: [Integer]
                   } deriving Show

-- | A list of formulas to verify.
data VerifyDecl = VerifyDecl
                  { verifyFormulas :: [PExpr] -- ^ The formulas to be verified.
                  } deriving Show

-- | Declares an instance of a specific model.
data InstanceDecl = InstanceDecl
                    { instanceModel :: String -- ^ The model of which this is an instance
                    , instanceName :: String -- ^ The name of the instance
                    , instanceContract :: [Contract] -- ^ Additional contracts to which this instance conforms
                    , instanceInits :: [(String,InitExpr)] -- ^ Additional initialization values
                    } deriving Show

data TimeSpec = NoTime
              | TimeSteps Integer
              | TimeUSecs Integer
              deriving (Eq,Ord)

instance Show TimeSpec where
  show NoTime = ""
  show (TimeSteps i) = "["++show i++" cy]"
  show (TimeUSecs i) = "["++show i++" us]"

data ContextInfo = ContextIn
                 | ContextOut
                 deriving (Show,Eq,Ord)

type PExpr = (Posn,GExpr)

-- | An untyped expression type.
--   Used internally in the parser.
data GExpr = GBin BinOp TimeSpec PExpr PExpr
           | GUn UnOp TimeSpec PExpr
           | GConst Int
           | GConstBool Bool
           | GVar (Maybe String) String
           | GSet [Integer]
           | GExists String (Maybe String) String PExpr
           | GAutomaton [State]
           | GTuple [PExpr]
           | GArray [PExpr]
           | GIndex PExpr PExpr
           | GEnum String
           | GBuiltIn String [PExpr]
           | GContext ContextInfo PExpr
           deriving (Show,Eq,Ord)

-- | A state of a state machine.
data State = State
             { stateName :: String -- ^ User-given name of the state
             , stateInitial :: Bool -- ^ Whether the state machine can start in this state
             , stateFinal :: Bool -- ^ Is this a final state?
             , stateContent :: [Either PExpr (String,Maybe PExpr)] -- ^ A list of conditions which must hold in this state and transitions which lead to other states
             } deriving (Show,Eq,Ord)

-- | Information about the initialization of a variable.
data InitExpr = InitAll -- ^ The variable is initialized with all possible values.
              | InitOne PExpr -- ^ The variable is initialized with a specific value.
              deriving (Show,Eq)

data Contract = Contract 
                { contractIsGuaranteed :: Bool
                , contractFormula :: PExpr
                } deriving (Show,Eq,Ord)
  