module Language.GTL.Parser.Monad where

import Control.Monad.State.Strict
import Control.Monad.Error

data Posn = Posn !Int !Int !Int deriving (Eq,Ord)

movePosn :: Posn -> Char -> Posn
movePosn (Posn a l c) '\t' = Posn (a+1) l     (((c+7) `div` 8)*8+1)
movePosn (Posn a l c) '\n' = Posn (a+1) (l+1) 1
movePosn (Posn a l c) _    = Posn (a+1) l     (c+1)

startPosn :: Posn
startPosn = Posn 0 1 1

data ParserState = ParserState
                   { parserPos :: Posn
                   , parserInp :: String
                   , parserChr :: !Char
                   , parserScd :: !Int
                   }

type GTLParser a = ErrorT String (State ParserState) a

getPos :: GTLParser Posn
getPos = do
  st <- get
  return $ parserPos st

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