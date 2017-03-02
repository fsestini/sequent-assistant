module Commands where

import Text.Parsec.String
import Text.Parsec.Char
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Control.Monad.Trans

import Formula
import Parser

data ProverCommand a = Prove (Sequent a)
                     | LoadTheory FilePath
                     | SetLogic Logic
                     | Info

data ProofCommand a = IdAxiom
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
                    | EqualityLeft Int
                    | EqualityRight Int
                    | Skip
                    | Print deriving (Eq, Show)
               
commandParser :: TParser (ProverCommand String)
commandParser =
  ((string' "prove ") >> Prove <$> sequentParser) <||>
  ((string' "load theory ") >> LoadTheory <$> many1' alphaNum') <||>
  ((string' "set logic ") >>
   SetLogic <$>
   ((string' "classical" >> return Classical) <||>
    (string' "intuitionistic" >> return Intuitionistic))) <||>
  ((string' "info") >> return Info)

parseCommand theory = parse (toParser commandParser theory) ""

parseIdAxiom :: Parser (ProofCommand a)
parseIdAxiom = string "identity" >> return IdAxiom

proofCommandParser :: TParser (ProofCommand String)
proofCommandParser =
  try' (string' "identity" >> return IdAxiom) <||>
  try' (string' "and left" >> return AndLeft) <||>
  try' (string' "and right" >> return AndRight) <||>
  try' (string' "or left" >> return OrLeft) <||>
  try' (string' "or right" >> return OrRight) <||>
  try' (string' "not left" >> return NotLeft) <||>
  try' (string' "not right" >> return NotRight) <||>
  try' (string' "impl left" >> return ImplLeft) <||>
  try' (string' "impl right" >> return ImplRight) <||>
  try' (string' "forall left" >> lift spaces >> termParser >>= return . ForallLeft) <||>
  try' (string' "forall right" >> return ForallRight) <||>
  try' (string' "exists left" >> return ExistsLeft) <||>
  try' (string' "exists right" >> termParser >>= return . ExistsRight) <||>
  try'
    (string' "exchange left" >> lift spaces >> (fmap read (many1' (lift digit))) >>=
     return . ExchangeLeft) <||>
  try'
    (string' "exchange right" >> lift spaces >> (fmap read (many1' (lift digit))) >>=
     return . ExchangeRight) <||>
  try'
    (string' "equality left" >> lift spaces >> (fmap read (many1' (lift digit))) >>=
     return . EqualityLeft) <||>
  try'
    (string' "equality right" >> lift spaces >> (fmap read (many1' (lift digit))) >>=
     return . EqualityRight) <||>
  try' (string' "skip" >> return Skip) <||>
  try' (string' "print" >> return Print)

parseProofCommand theory = parse (toParser proofCommandParser theory) ""
