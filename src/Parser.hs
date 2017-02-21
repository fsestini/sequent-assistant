{-# LANGUAGE DataKinds #-}

module Parser where

import Formula
import Substitution
import Text.Parsec.String
import Text.Parsec.Char

import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

functionSymbols :: [String]
functionSymbols = ["s", "z"]

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
parens     = Token.parens     lexer 
whiteSpace = Token.whiteSpace lexer 
comma = Token.comma lexer

mainParser :: Parser (Formula String)
mainParser = whiteSpace >> formula

formula :: Parser (Formula String)
formula = parens formula

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
  [ [ Prefix (reservedOp "not" >> return (Not))
    , Prefix forallTransformer
    , Prefix existsTransformer]
  , [ Infix (reservedOp "and" >> return (Conj)) AssocLeft
    , Infix (reservedOp "or" >> return (Disj)) AssocLeft
    ]
  , [Infix (reservedOp "->" >> return (Impl)) AssocLeft]
  ]

expr :: Parser (Formula String)
expr = buildExpressionParser operators atom

atom :: Parser (Formula String)
atom  =  parens expr
     <|> (reserved "true" >> return Top)
     <|> (reserved "false" >> return Bottom)
     <|> Term <$> parseTerm

parseTerm :: Parser (Term String) 
parseTerm = do
  ident <- identifier
  if elem ident functionSymbols
     then do
       args <- try (parens (sepBy1 parseTerm comma)) <|> return []
       return $ Func ident args
     else return . Free $ ident

parseString :: String -> Formula String
parseString str =
  case parse expr "" str of
    Left e -> error $ show e
    Right f -> f

sequentParser :: Parser (Sequent String)
sequentParser = do
  left <- sepBy1 expr comma
  whiteSpace
  string "|-"
  whiteSpace
  right <- sepBy1 expr comma
  return (S left right)

parseSequent :: String -> Either ParseError (Sequent String)
parseSequent = parse sequentParser ""
