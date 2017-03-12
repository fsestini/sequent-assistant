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
import Parser
import Control.Monad.Reader

type ProofTree a = Tree (Sequent a)

type ProofT a m b = MaybeT (StateT (Location (Sequent a)) (ReaderT (Theory a, Logic) m)) b
type ProofIO a b = ProofT a IO b
type Proof a b = ProofT a Identity b

type Prover a b = ReaderT (Theory a, Logic) IO b

liftProof :: Proof a b -> ProofIO a b
liftProof = hoist (hoist (hoist (return . runIdentity)))

liftMaybe :: Monad m => Maybe a -> MaybeT m a
liftMaybe = MaybeT . return

nextSequent :: Eq a => Proof a (Sequent a)
nextSequent = do
  loc <- get
  newLoc <- liftMaybe $ searchTree loc test
  put newLoc
  let seq = label newLoc
  return seq
  where
    test t = (null . subForest) t && (not (isAxiom (rootLabel t)))

-- Add sequents as premises of the current one.
addGoals :: [Sequent a] -> Proof a ()
addGoals seqs = do
  loc <- get
  put $ modifyTree trans loc
  where
    trans t = Node (rootLabel t) (map (flip Node []) seqs)

getCommand :: ProofIO String (ProofCommand String)
getCommand = do
  line <- liftIO getLine
  theory <- lift (fmap fst ask)
  case parseProofCommand theory line of
    Left err ->
      (liftIO $
      putStrLn ("error: " ++ (show err)) >> putStr "Enter command: " >>
      hFlush stdout) >> getCommand
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

liftRule :: Rule a -> Sequent a -> ProofIO a ()
liftRule r seq = do
  case runExcept (r seq) of
    Left err -> liftIO . putStrLn $ "error: " ++ err
    Right newSequents -> liftProof $ addGoals newSequents

proofLoop :: _ => ProofIO String ()
proofLoop = do
  sequent@(S ante cons) <- liftProof nextSequent
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
