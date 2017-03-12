{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wall -Wno-partial-type-signatures #-}

module Proof where

import System.IO
import Rules
import Control.Monad.Except
import Control.Monad.State
import Formula
import Control.Monad.Trans.Maybe
import Tree
import Commands
import Parser.Commands
import Control.Monad.Reader

type ProofTree a = Tree (Sequent a)

type ProofEnv a = Theory a
type ProofT a m b = MaybeT (StateT (Location (Sequent a)) (ReaderT (ProofEnv a) m)) b

type Prover a b = ReaderT (ProofEnv a) IO b

liftMaybe :: Monad m => Maybe a -> MaybeT m a
liftMaybe = MaybeT . return

getTheory :: Monad m => ProofT a m (Theory a)
getTheory = lift ask

nextSequent :: (Eq a, Monad m) => ProofT a m (Sequent a)
nextSequent = do
  loc <- get
  newLoc <- liftMaybe $ searchTree loc test
  put newLoc
  let sequent = label newLoc
  return sequent
  where
    test t = (null . subForest) t && (not (isAxiom (rootLabel t)))

-- Add sequents as premises of the current one.
addGoals :: Monad m => [Sequent a] -> ProofT a m ()
addGoals seqs = do
  loc <- get
  put $ modifyTree trans loc
  where
    trans t = Node (rootLabel t) (map (flip Node []) seqs)

getCommand :: (MonadIO m) => ProofT String m (ProofCommand String)
getCommand = do
  line <- liftIO getLine
  theory <- getTheory
  case parseProofCommand theory line of
    Left err -> do
      liftIO $ do
        putStrLn ("error: " ++ (show err))
        putStr "proof> "
        hFlush stdout
      getCommand
    Right comm -> return comm

getRule :: (Eq a, Ord a, PickFresh a) => ProofCommand a -> Rule a
getRule IdAxiom = identity
getRule AndLeft = andLeft
getRule AndRight = andRight
getRule OrLeft = orLeft
getRule OrRight = orRight
getRule NotLeft = notLeft
getRule NotRight = notRight
getRule ImplLeft = implLeft
getRule ImplRight = implRight
getRule (ForallLeft term) = forallLeft term
getRule ForallRight = forallRight
getRule ExistsLeft = existsLeft
getRule (ExistsRight term) = existsRight term
getRule (ExchangeLeft i) = exchangeLeft i
getRule (ExchangeRight i) = exchangeRight i
getRule (EqualityLeft i) = equalityLeft i
getRule (EqualityRight i) = equalityRight i

liftRule :: MonadIO m => Rule a -> Sequent a -> ProofT a m ()
liftRule r sequent = do
  case runExcept (r sequent) of
    Left err -> liftIO . putStrLn $ "error: " ++ err
    Right newSequents -> addGoals newSequents

proofLoop :: _ => ProofT String m ()
proofLoop = do
  sequent@(S ante cons) <- nextSequent
  liftIO $ do
    putStrLn ""
    forM_ ante (putStrLn . show)
    putStrLn "--------------------------------------------------"
    forM_ cons (putStrLn . show)
    putStrLn ""
    putStr "> "
    hFlush stdout
  comm <- getCommand
  case comm of
    Print -> undefined
    Skip -> proofLoop
    _ -> liftRule (getRule comm) sequent >> proofLoop

prove :: Sequent String -> Prover String (ProofTree String)
prove sequent = do
  loc <- fmap snd $ runStateT (runMaybeT proofLoop) (start (Node sequent []))
  return . end $ loc
