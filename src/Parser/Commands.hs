module Parser.Commands
  ( commandParser
  , parseCommand
  , proofCommandParser
  , parseProofCommand
  ) where

import Commands
import Formula
import Parser.Formula
import Parser.Base
               
commandParser :: TParser (ProverCommand String)
commandParser =
  ((string "prove ") >> Prove <$> sequentParser) <||>
  ((string "load theory ") >> LoadTheory <$> many1 alphaNum) <||>
  ((string "set logic ") >>
   SetLogic <$>
   ((string "classical" >> return Classical) <||>
    (string "intuitionistic" >> return Intuitionistic))) <||>
  ((string "info") >> return Info)

parseCommand theory = parse (toParser commandParser theory) ""

parseIdAxiom :: TParser (ProofCommand a)
parseIdAxiom = string "identity" >> return IdAxiom

parseIdC = string "identity" >> return IdAxiom
parseReflC = string "reflexivity" >> return ReflAxiom
parseAndLC = string "and left" >> return AndLeft
parseAndRC = string "and right" >> return AndRight
parseOrLC = string "or left" >> return OrLeft
parseOrRC = string "or right" >> return OrRight
parseNotLC = string "not left" >> return NotLeft
parseNotRC = string "not right" >> return NotRight
parseImplLC = string "impl left" >> return ImplLeft
parseImplRC = string "impl right" >> return ImplRight
parseForallLC =
  string "forall left" >> spaces >> termParser >>= return . ForallLeft
parseForallRC = string "forall right" >> return ForallRight
parseExistsLC = string "exists left" >> return ExistsLeft
parseExistsRC =
  string "exists right" >> spaces >> termParser >>= return . ExistsRight
parseExchLC = string "exchange left" >> spaces >> int >>= return . ExchangeLeft
parseExchRC = string "exchange right" >> spaces >> int >>= return . ExchangeRight
parseEqLC = string "equality left" >> spaces >> int >>= return . EqualityLeft
parseEqRC = string "equality right" >> spaces >> int >>= return . EqualityRight
parseSkipC = string "skip" >> return Skip
parsePrintC = string "print" >> return Print
parseCutC =
  string "cut" >>
  return Cut <*> formulaParser <*> (sepBy int comma) <*> (sepBy int comma)

proofCommandParser :: TParser (ProofCommand String)
proofCommandParser = foldr1 (<||>) $ map try [
    parseIdC
  , parseReflC
  , parseAndLC
  , parseAndRC
  , parseOrLC 
  , parseOrRC 
  , parseNotLC
  , parseNotRC
  , parseImplLC
  , parseImplRC
  , parseForallLC
  , parseForallRC
  , parseExistsLC
  , parseExistsRC
  , parseExchLC
  , parseExchRC
  , parseEqLC
  , parseEqRC
  , parseSkipC
  , parsePrintC
  , parseCutC
  ]

parseProofCommand theory = parse (toParser proofCommandParser theory) ""
