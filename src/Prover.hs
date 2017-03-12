{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall -Wno-partial-type-signatures #-}

module Prover where

import FromString
import Proof hiding (getCommand, getTheory)
import Substitution
import Commands
import Formula
import Parser.Commands
import Parser.Formula
import System.IO
import Control.Monad.Reader
import Data.Maybe
import qualified Data.Set as S
import TeX

getTheory :: Prover a (Theory a)
getTheory = ask

getLogic :: Prover a Logic
getLogic = fmap logic ask

withLogic :: Logic -> Prover a b -> Prover a b
withLogic Intuitionistic p = local (const intuitionisticLogic) p
withLogic Classical p = local (const classicalLogic) p

getCommand :: Prover String (ProverCommand String)
getCommand = do
  liftIO $ putStr "> "
  liftIO $ hFlush stdout
  line <- liftIO getLine
  theory <- getTheory
  case parseCommand theory line of
    Left err -> (liftIO $ putStrLn $ "error: " ++ show err) >> getCommand
    Right comm -> return comm

askToPrint :: _ => ProofTree a -> m ()
askToPrint proofTree = do
  liftIO $ putStr "Print proof? (y/n) " >> hFlush stdout
  line <- liftIO getLine
  when (line == "y") (liftIO $ putStrLn $ texTree proofTree)


askToSave :: _ => Formula a -> Prover a () -> Prover a ()
askToSave formula k = do
  liftIO $ putStr "Save theorem with name (empty to skip): " >> hFlush stdout
  line <- liftIO getLine
  if line == ""
    then k
    else local (updateTheory (fromString line) formula) k

printTheorems :: _ => Prover a ()
printTheorems = do
  x <- fmap axioms getTheory
  forM_ x (\(name, th) -> liftIO . putStrLn $ (show name) ++ ": " ++ show th)

proverLoop :: Prover String ()
proverLoop = do
  comm <- getCommand
  case comm of
    Prove sequent -> do
      proofTree <- desugar sequent >>= prove
      askToPrint proofTree
      askToSave (toFormula sequent) proverLoop
    LoadTheory _ ->
      (liftIO $ putStrLn "error: not yet supported.") >> proverLoop
    SetLogic l -> withLogic l proverLoop
    Info -> printTheorems >> proverLoop

--------------------------------------------------------------------------------
-- Desugaring of theorem names

desugar :: Sequent String -> Prover String (Sequent String)
desugar (S fs1 fs2) = do
  theory <- getTheory
  fs1' <- mapM (auxSchemata theory . aux (axioms theory)) $ fs1
  fs2' <- mapM (auxSchemata theory . aux (axioms theory)) $ fs2
  return $ S fs1' fs2'
  where
    aux axioms f@(Predicate ident []) =
      case listToMaybe matches of
        Nothing -> f
        Just (_, ax) -> ax
      where
        matches = filter ((ident ==) . fst) axioms
    aux _ f = f
    auxSchemata theory@(T _ _ _ axiomSchemata) f@(Predicate ident []) =
      case listToMaybe matches of
        Nothing -> return f
        Just (_, axSch) ->
          liftIO $ do
            putStr "Insert formula to instantiate axiom schema: "
            hFlush stdout
            line <- getLine
            return (axSch (parseFormula theory line))
      where
        matches = filter ((ident ==) . fst) axiomSchemata
    auxSchemata _ f = return f

--------------------------------------------------------------------------------
-- Main function

proverMain :: IO ()
proverMain = runReaderT loop peanoArithmetic
  where
    loop = do
      liftIO $ putStrLn "Loading theory of Peano arithmetic..."
      liftIO $ hFlush stdout
      proverLoop

--------------------------------------------------------------------------------

peanoArithmetic :: Theory String
peanoArithmetic =
  T
    ["s", "z", "plus", "times"]
    Classical
    [ ("ax1", parseFormula partial "forall x (eq(plus(x, z),x))")
    , ( "ax2"
      , parseFormula
          partial
          "forall x (forall y (eq(plus(x, s(y)), s(plus(x,y)))))")
    , ("ax3", parseFormula partial "forall x (not (eq(z, s(x))))")
    , ( "ax4"
      , parseFormula partial "forall x (forall y (eq(s(x), s(y)) -> eq(x,y)))")
    ]
    [("ax7", induction)]
  where
    partial = T ["s", "z", "plus", "times"] Classical [] []
    induction :: Formula String -> Formula String
    induction f =
      predZero `Impl`
      ((abstractForall fv (f `Impl` predSucc)) `Impl` (abstractForall fv f))
      where
        fv = head . S.toList $ formulaFreeVars f
        termZero = Func "z" []
        predZero = substFormula (simpleVarSub fv termZero) f
        predSucc = substFormula (simpleTermSub (Free fv) (Func "s" [Free fv])) f
        -- predSucc = substFormula xToSuccX f
        xToSuccX t@(Free x)
          | x == fv = Func "s" [Free fv]
          | otherwise = t
