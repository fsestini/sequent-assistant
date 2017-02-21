{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Proof where

import System.IO
import Rules
import Control.Monad.Except
import Control.Monad.State
import Formula
import Control.Monad.Trans.Maybe
import Data.Maybe
import Tree
import Control.Monad.Morph
import Control.Monad.Identity
import Commands
import Parser

type ProofTree a = Tree (Sequent a)
type Proof a b = MaybeT (State (Location (Sequent a))) b

type ProofIO a b = MaybeT (StateT (Location (Sequent a)) IO) b

liftProof :: Proof a b -> ProofIO a b
liftProof = hoist (hoist (return . runIdentity))

liftMaybe :: Monad m => Maybe a -> MaybeT m a
liftMaybe = MaybeT . return

nextSequent :: Eq a => Proof a (Sequent a)
nextSequent = do
  loc <- get
  newLoc <- liftMaybe $ searchTree loc test
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

getCommand :: ProofIO a (Command String)
getCommand = do
  line <- liftIO getLine
  case parseCommand line of
    Left err ->
      (liftIO $
      putStrLn ("error: " ++ (show err)) >> putStr "Enter command: " >>
      hFlush stdout) >> getCommand
    Right comm -> return comm

getRule :: (Eq a, Ord a, PickFresh a) => Command a -> Rule a
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

liftRule :: Rule a -> Sequent a -> ProofIO a ()
liftRule r seq = do
  case runExcept (r seq) of
    Left err -> liftIO . putStrLn $ "error: " ++ err
    Right newSequents -> liftProof $ addGoals newSequents

proofLoop :: _ => ProofIO String ()
proofLoop = do
  sequent <- liftProof nextSequent
  liftIO . putStrLn $ "proving: " ++ show sequent
  comm <- getCommand
  case comm of
    Print -> undefined
    Skip -> proofLoop
    _ -> liftRule (getRule comm) sequent >> proofLoop

prove :: _ => Sequent String -> IO (ProofTree String)
prove seq = do
  x <- fmap snd $ runStateT (runMaybeT proofLoop) (start (Node seq []))
  return $ end x
  
main :: IO ()
main = do
  putStr "Enter sequent: "
  hFlush stdout
  line <- getLine
  case parseSequent line of
    Left err -> putStrLn $ "Error: " ++ (show err)
    Right seq -> do pt <- prove seq
                    putStrLn "No more goals. Proof tree:"
                    putStrLn . show $ pt
                    main
