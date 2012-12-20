{- | The parser monad for GTL is designed to allow lazy parsing as well as precise error reporting 
 -}
module Language.GTL.Parser.Monad (GTLParser
                                 ,ParserState(..)
                                 ,Posn()
                                 ,movePosn
                                 ,startPosn
                                 ,getPos
                                 ,runGTLParser
                                 ) where

import Control.Monad.State.Strict
import Control.Monad.Error

-- | The current position of the parser, given as line and column number
data Posn = Posn !Int !Int !Int deriving (Eq,Ord)

-- | Advance the parser position one character
--   Uses the character to decide if a new line has been started or a column advance has been made (by using a tabulator).
movePosn :: Posn -> Char -> Posn
movePosn (Posn a l c) '\t' = Posn (a+1) l     (((c+7) `div` 8)*8+1)
movePosn (Posn a l c) '\n' = Posn (a+1) (l+1) 1
movePosn (Posn a l c) _    = Posn (a+1) l     (c+1)

-- | The initial parsing position: Line 1, column 1.
startPosn :: Posn
startPosn = Posn 0 1 1

-- | The internal state of the parser
data ParserState = ParserState
                   { parserPos :: Posn -- ^ The current position in the input stream
                   , parserInp :: String -- ^ The current input stream
                   , parserChr :: !Char -- ^ The last character being considered
                   , parserScd :: !Int -- ^ The state of the parser
                   }

-- | A GTLParser is a monad which can report errors as strings and holds the parser state
type GTLParser a = ErrorT String (State ParserState) a

-- | Get the current position from the parser monad
getPos :: GTLParser Posn
getPos = do
  st <- get
  return $ parserPos st

-- | Evaluate a parser on a given string, returns either an error message with
--   a position where the error occured or the result of the parser.
runGTLParser :: GTLParser a -> String -> Either (String,Posn) a
runGTLParser p inp = case runState (runErrorT p) (ParserState { parserPos = startPosn
                                                              , parserInp = inp
                                                              , parserChr = '\n'
                                                              , parserScd = 0
                                                              }) of
                       (Left err,st) -> Left (err,parserPos st)
                       (Right res,_) -> Right res

instance Show Posn where
  show (Posn _ l c) = "line "++show l++", column "++show c