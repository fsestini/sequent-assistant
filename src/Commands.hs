module Commands where

import Formula

data ProverCommand a = Prove (Sequent a)
                     | LoadTheory FilePath
                     | SetLogic Logic
                     | Info

data ProofCommand a = IdAxiom
                    | ReflAxiom
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
                    | Cut (Formula a) [Int] [Int]
                    | Print deriving (Eq, Show)
