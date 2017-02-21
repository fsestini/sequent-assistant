module Commands where

import Text.Parsec.String
import Text.Parsec.Char
import Text.Parsec.Prim
import Text.Parsec.Combinator

import Formula
import Parser

data Command a = IdAxiom
               | AndLeft
               | AndRight
               | OrLeft
               | OrRight
               | NotLeft
               | NotRight
               | ImplLeft
               | ImplRight
               | ForallLeft (Term a)
               | ForallRight
               | ExistsLeft
               | ExistsRight (Term a)
               | ExchangeLeft Int
               | ExchangeRight Int
               | Skip
               | Print deriving (Eq, Show)
               
parseIdAxiom :: Parser (Command a)
parseIdAxiom = string "identity" >> return IdAxiom

commandParser :: Parser (Command String)
commandParser =
  try (string "identity" >> return IdAxiom) <|>
  try (string "and left" >> return AndLeft) <|>
  try (string "and right" >> return AndRight) <|>
  try (string "or left" >> return OrLeft) <|>
  try (string "or right" >> return OrRight) <|>
  try (string "not left" >> return NotLeft) <|>
  try (string "not right" >> return NotRight) <|>
  try (string "impl left" >> return ImplLeft) <|>
  try (string "impl right" >> return ImplRight) <|>
  try (string "forall left" >> spaces >> parseTerm >>= return . ForallLeft) <|>
  try (string "forall right" >> return ForallRight) <|>
  try (string "exists left" >> return ExistsLeft) <|>
  try (string "exists right" >> parseTerm >>= return . ExistsRight) <|>
  try
    (string "exchange left" >> spaces >> (fmap read (many1 digit)) >>=
     return . ExchangeLeft) <|>
  try
    (string "exchange right" >> spaces >> (fmap read (many1 digit)) >>=
     return . ExchangeRight) <|>
  try (string "skip" >> return Skip) <|>
  try (string "print" >> return Print)

parseCommand = parse commandParser ""
