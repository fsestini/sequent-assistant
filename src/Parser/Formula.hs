module Parser.Formula
  ( formulaParser
  , parseFormula
  , termParser
  , parseTerm
  , sequentParser
  , parseSequent
  , int
  , comma
  ) where

import Formula
import Substitution
import Parser.Base

import Control.Monad.Reader
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.Parsec.Char as TPC
import qualified Text.ParserCombinators.Parsec as TPCombs
import qualified Text.ParserCombinators.Parsec.Token as Token

languageDef =
  emptyDef
  { Token.identStart = TPC.letter
  , Token.identLetter = TPC.alphaNum
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
int :: TParser Int
int = lift $ fmap (fromInteger :: Integer -> Int) (Token.integer lexer)
parens = liftUnary (Token.parens lexer)
whiteSpace = lift $ Token.whiteSpace lexer
comma = lift (Token.comma lexer)

forallTransformer :: TPCombs.Parser (Formula String -> Formula String)
forallTransformer = do
  reservedOp "forall"
  x <- identifier
  return $ abstractForall x

existsTransformer :: TPCombs.Parser (Formula String -> Formula String)
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
  , [Infix (implOp >> return (Impl)) AssocRight]
  ]
  where
    notOp = Token.reservedOp lexer "not"
    andOp = Token.reservedOp lexer "and"
    orOp = Token.reservedOp lexer "or"
    implOp = Token.reservedOp lexer "->"

formulaParser :: TParser (Formula String)
formulaParser = whiteSpace >> expr

expr :: TParser (Formula String)
expr = do
  theory <- getTheory
  lift $ buildExpressionParser operators (toParser atom theory)

ppred :: String -> [Term String] -> Formula String
ppred str args = if str == "eq"
                    then Equality (head args) (head (tail args))
                    else Predicate str args

atom :: TParser (Formula String)
atom =  parens formulaParser
    <||> (lift (reserved "true") >> return Top)
    <||> (lift (reserved "false") >> return Bottom)
    <||> ppred <$> lift identifier
               <*> (try (parens (sepBy1 (termParser) comma))
                          <||> return [])

termParser :: TParser (Term String) 
termParser = do
  ident <- lift identifier
  theory <- ask
  if elem ident (functionSymbols theory)
     then do
       args <- try (parens (sepBy1 termParser comma)) <||> return []
       return $ Func ident args
     else return . Free $ ident

parseTerm :: Theory String -> String -> Term String
parseTerm theory str =
  case TPCombs.parse (toParser termParser theory) "" str of
    Left e -> error $ show e
    Right t -> t

parseFormula :: Theory String -> String -> Formula String
parseFormula theory str =
  case TPCombs.parse (toParser formulaParser theory) "" str of
    Left e -> error $ show e
    Right f -> f

sequentParser :: TParser (Sequent String)
sequentParser = do
  left <- sepBy1 formulaParser comma
  whiteSpace
  string "|-"
  whiteSpace
  right <- sepBy1 formulaParser comma
  return (S left right)

parseSequent :: Theory String -> String -> Either TPCombs.ParseError (Sequent String)
parseSequent theory = TPCombs.parse (toParser sequentParser theory) ""
