{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}

module Formula where

import Fin
import qualified Data.Map.Strict as M
import Text.PrettyPrint
import Control.Monad.Reader
import Data.List

data RawTerm :: Nat -> * ->  * where
  Bound :: Fin n -> RawTerm n a
  Free :: a -> RawTerm n a
  Func :: String -> [RawTerm n a] -> RawTerm n a

deriving instance Eq a => Eq (RawTerm n a)

type Term a = RawTerm Zero a

data RawFormula :: Nat -> * -> * where
  Predicate :: a -> [RawTerm n a] -> RawFormula n a
  Conj :: RawFormula n a -> RawFormula n a -> RawFormula n a
  Disj :: RawFormula n a -> RawFormula n a -> RawFormula n a
  Impl :: RawFormula n a -> RawFormula n a -> RawFormula n a
  Forall :: RawFormula (Succ n) a -> RawFormula n a
  Exists :: RawFormula (Succ n) a -> RawFormula n a
  Not :: RawFormula n a -> RawFormula n a
  Top :: RawFormula n a
  Bottom :: RawFormula n a
  Equality :: RawTerm n a -> RawTerm n a -> RawFormula n a

deriving instance Eq a => Eq (RawFormula n a)

type Formula a = RawFormula Zero a

data Sequent a = S [Formula a] [Formula a] deriving (Eq)

instance Show a => Show (Term a) where
  show t = runReader (showTerm t) M.empty

instance (Show a, PickFresh a) => Show (Formula a) where
  show f = runReader (showFormula f) M.empty

instance (Show a, PickFresh a) => Show (Sequent a) where
  show (S fs1 fs2) = let f = join . intersperse ", " . map show
                     in f (reverse fs1) ++ " |- " ++ f fs2

class PickFresh a where
  pickFresh :: [a] -> a

instance PickFresh String where
  pickFresh strs = aux 0 strs
    where
      aux :: Int -> [String] -> String
      aux i strs =
        let x = "x" ++ replicate i '\''
        in if elem x strs
             then aux (i + 1) strs
             else x

showTerm :: Show a => RawTerm n a -> Reader (M.Map Int a) String
showTerm (Free x) = return . show $ x
showTerm (Func f xs) = do
  strs <- mapM showTerm xs
  return $ f ++ "(" ++ concat (intersperse ", " strs) ++ ")"
showTerm (Bound n) = do
  env <- ask
  case M.lookup (toInt n) env of
    Nothing -> error "error in showTerm"
    Just x -> return . show $ x

showParens :: Reader a String -> Reader a String
showParens r = do
  rr <- r
  return $ "(" ++ rr ++ ")"

showFormula :: (Show a, PickFresh a) => RawFormula n a -> Reader (M.Map Int a) String
showFormula (Term t) = showTerm t
showFormula (Conj f1 f2) = do
  sf1 <- showParens $ showFormula f1
  sf2 <- showParens $ showFormula f2
  return $ sf1 ++ " /\\ " ++ sf2
showFormula (Disj f1 f2) = do
  sf1 <- showParens $ showFormula f1
  sf2 <- showParens $ showFormula f2
  return $ sf1 ++ " \\/ " ++ sf2
showFormula (Impl f1 f2) = do
  sf1 <- showParens $ showFormula f1
  sf2 <- showParens $ showFormula f2
  return $ sf1 ++ " -> " ++ sf2
showFormula (Equality t1 t2) = do
  st1 <- showTerm t1
  st2 <- showTerm t2
  return $ st1 ++ " = " ++ st2
showFormula (Not f) = (++) "not " <$> showFormula f
showFormula Top = return "Top"
showFormula Bottom = return "_|_"
showFormula (Forall f) = do
  env <- ask
  let newV = pickFresh . M.elems $ env
  res <- showParens $ local (M.insert 0 newV . M.mapKeys (+1)) (showFormula f)
  return $ "forall " ++ show newV ++ " " ++ res
showFormula (Exists f) = do
  env <- ask
  let newV = pickFresh . M.elems $ env
  res <- showParens $ local (M.insert 0 newV . M.mapKeys (+1)) (showFormula f)
  return $ "exists " ++ show newV ++ " " ++ res 
