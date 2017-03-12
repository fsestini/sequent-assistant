module Parser.Base
  ( alphaNum
  , try
  , string
  , sepBy
  , sepBy1
  , many1
  , liftUnary
  , toParser
  , getTheory
  , TPCombs.parse
  , spaces
  , (<||>)
  , TPCombs.ParseError
  , TPCombs.Parser
  , TParser
  ) where

import Formula

import Text.Parsec.String
import qualified Text.Parsec.Char as TPC
import Text.Parsec.Prim hiding (try)
import qualified Text.Parsec.Combinator as TPComb

import Control.Monad.Reader
import qualified Text.ParserCombinators.Parsec as TPCombs

type TParser a = ReaderT (Theory String) Parser a

liftBinary :: (Parser a -> Parser b -> Parser c)
           -> TParser a
           -> TParser b
           -> TParser c
liftBinary f tp1 tp2 = do
  theory <- getTheory
  lift (f (toParser tp1 theory) (toParser tp2 theory))

liftUnary :: (Parser a -> Parser b) -> TParser a -> TParser b
liftUnary f tp = do
  theory <- getTheory
  lift (f (toParser tp theory))

toParser :: TParser a -> Theory String -> Parser a
toParser tp t = runReaderT tp t

spaces :: TParser ()
spaces = lift TPC.spaces

getTheory :: TParser (Theory String)
getTheory = ask

string :: String -> TParser String
string = lift . TPC.string

infixl 3 <||>
(<||>) :: TParser c -> TParser c -> TParser c
(<||>) = liftBinary (<|>)
try :: TParser b -> TParser b
try = liftUnary TPCombs.try
sepBy1 :: TParser a -> TParser sep -> TParser [a]
sepBy1 = liftBinary TPComb.sepBy1
sepBy :: TParser a -> TParser sep -> TParser [a]
sepBy = liftBinary TPComb.sepBy
many1 :: TParser a -> TParser [a]
many1 = liftUnary TPComb.many1

alphaNum :: TParser Char
alphaNum = lift TPC.alphaNum
