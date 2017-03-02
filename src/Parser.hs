{-# LANGUAGE DataKinds #-}

module Parser where

import Formula
import Substitution

import Text.Parsec.String
import Text.Parsec.Char
import Text.Parsec.Prim hiding (try)
import Text.Parsec.Combinator

import Control.Monad.Reader
import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

type TParser a = ReaderT (Theory String) Parser a

liftBinary :: (Parser a -> Parser b -> Parser c) -> TParser a -> TParser b -> TParser c
liftBinary f tp1 tp2 = do
  theory <- getTheory
  lift (f (toParser tp1 theory) (toParser tp2 theory))

liftUnary :: (Parser a -> Parser b) -> TParser a -> TParser b
liftUnary f tp = do
  theory <- getTheory
  lift (f (toParser tp theory))

languageDef =
  emptyDef
  { Token.identStart = letter
  , Token.identLetter = alphaNum
  , Token.reservedNames =
      [ "true"
      , "false"
      , "forall"
      , "exists"
      , "not"
      , "and"
      , "or"
      , "->"
      ]
  , Token.reservedOpNames =
      ["->", "and", "or", "not", "forall", "exists"]
  }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved = Token.reserved lexer

reservedOp = Token.reservedOp lexer

parens :: Parser a -> Parser a
parens = Token.parens     lexer

whiteSpace = Token.whiteSpace lexer

comma :: Parser String
comma = Token.comma lexer

forallTransformer :: Parser (Formula String -> Formula String)
forallTransformer = do
  reservedOp "forall"
  x <- identifier
  return $ abstractForall x

existsTransformer :: Parser (Formula String -> Formula String)
existsTransformer = do
  reservedOp "exists"
  x <- identifier
  return $ abstractExists x

operators =
  [ [ Prefix (notOp >> return (Not))
    , Prefix forallTransformer
    , Prefix existsTransformer]
  , [ Infix (andOp >> return (Conj)) AssocLeft
    , Infix (orOp >> return (Disj)) AssocLeft
    ]
  , [Infix (implOp >> return (Impl)) AssocLeft]
  ]
  where
    notOp = Token.reservedOp lexer "not"
    andOp = Token.reservedOp lexer "and"
    orOp = Token.reservedOp lexer "or"
    implOp = Token.reservedOp lexer "->"

toParser :: TParser a -> Theory String -> Parser a
toParser tp t = runReaderT tp t

getTheory :: TParser (Theory String)
getTheory = ask

string' :: String -> TParser String
string' = lift . string

formulaParser :: TParser (Formula String)
formulaParser = lift whiteSpace >> expr

expr :: TParser (Formula String)
expr = do
  theory <- getTheory
  lift $ buildExpressionParser operators (toParser atom theory)

infixl 3 <||>
(<||>) = liftBinary (<|>)
parens' = liftUnary parens
try' = liftUnary try
sepBy1' = liftBinary sepBy1
many1' = liftUnary many1
alphaNum' :: TParser Char
alphaNum' = lift alphaNum

ppred :: String -> [Term String] -> Formula String
ppred str args = if str == "eq"
                    then Equality (head args) (head (tail args))
                    else Predicate str args

atom :: TParser (Formula String)
atom =  parens' formulaParser
    <||> (lift (reserved "true") >> return Top)
    <||> (lift (reserved "false") >> return Bottom)
    <||> ppred <$> lift identifier
               <*> (try' (parens' (sepBy1' (termParser) (lift comma)))
                          <||> return [])



termParser :: TParser (Term String) 
termParser = do
  ident <- lift identifier
  theory <- ask
  if elem ident (functionSymbols theory)
     then do
       args <- try' (parens' (sepBy1' termParser (lift comma))) <||> return []
       return $ Func ident args
     else return . Free $ ident

parseTerm :: Theory String -> String -> Term String
parseTerm theory str =
  case parse (toParser termParser theory) "" str of
    Left e -> error $ show e
    Right t -> t

parseFormula :: Theory String -> String -> Formula String
parseFormula theory str =
  case parse (toParser formulaParser theory) "" str of
    Left e -> error $ show e
    Right f -> f

sequentParser :: TParser (Sequent String)
sequentParser = do
  left <- sepBy1' formulaParser (lift comma)
  lift whiteSpace
  lift $ string "|-"
  lift whiteSpace
  right <- sepBy1' formulaParser (lift comma)
  return (S left right)

parseSequent :: Theory String -> String -> Either ParseError (Sequent String)
parseSequent theory = parse (toParser sequentParser theory) ""
