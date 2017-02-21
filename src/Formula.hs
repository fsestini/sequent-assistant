{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

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

instance (Show a, Pretty a) => Show (Term a) where
  show t = render $ runReader (pTerm t) M.empty

instance (Show a, PickFresh a, Pretty a) => Show (Formula a) where
  show f = render $ runReader (pFormula f) M.empty

instance (Show a, PickFresh a, Pretty a) => Show (Sequent a) where
  show (S fs1 fs2) = let f = join . intersperse ", " . map show
                     in f (reverse fs1) ++ " |- " ++ f fs2

class PickFresh a where
  pickFresh :: [a] -> a

instance PickFresh String where
  pickFresh strs = aux 0 strs
    where
      aux :: Int -> [String] -> String
      aux i strs' =
        let x = "x" ++ replicate i '\''
        in if elem x strs'
             then aux (i + 1) strs'
             else x

class Pretty a where
  pretty :: a -> Doc

instance Pretty String where
  pretty = text

pTerm :: Pretty a => RawTerm n a -> Reader (M.Map Int a) Doc
pTerm (Free x) = return . pretty $ x
pTerm (Func f xs) = do
  strs <- mapM pTerm xs
  return $
    text f <>
    if null strs
      then empty
      else parens (hcat (punctuate comma strs))
pTerm (Bound n) = do
  env <- ask
  case M.lookup (toInt n) env of
    Nothing -> error "error in showTerm"
    Just x -> return . pretty $ x

isAtomic :: RawFormula n a -> Bool
isAtomic (Predicate _ _) = True
isAtomic Top = True
isAtomic Bottom = True
isAtomic _ = False

pFormulaMaybeParens :: _ => RawFormula n a -> Reader (M.Map Int a) Doc
pFormulaMaybeParens f = if not (isAtomic f)
                           then parens <$> (pFormula f)
                           else pFormula f

pFormula :: (Pretty a, PickFresh a) => RawFormula n a -> Reader (M.Map Int a) Doc
pFormula (Predicate ident terms) =
  fmap
    (pretty ident <>)
    (if null terms
       then return empty
       else parens . hcat . punctuate comma <$> mapM pTerm terms)
pFormula (Conj f1 f2) = do
  sf1 <- pFormulaMaybeParens f1
  sf2 <- pFormulaMaybeParens f2
  return $ hsep [sf1, text "∧", sf2]
pFormula (Disj f1 f2) = do
  sf1 <- pFormulaMaybeParens f1
  sf2 <- pFormulaMaybeParens f2
  return $ hsep [sf1, text "∨", sf2]
pFormula (Impl f1 f2) = do
  sf1 <- pFormulaMaybeParens f1
  sf2 <- pFormulaMaybeParens f2
  return $ hsep [sf1, text "→", sf2]
pFormula (Equality t1 t2) = do
  st1 <- pTerm t1
  st2 <- pTerm t2
  return $ hsep [st1, text "=", st2]
pFormula (Not f) = (text "¬" <+>) <$> pFormula f
pFormula (Forall f) = do
  env <- ask
  let newV = pickFresh . M.elems $ env
  res <- local (M.insert 0 newV . M.mapKeys (+ 1)) (pFormulaMaybeParens f)
  return $ hsep [text "∀", pretty newV, res]
pFormula (Exists f) = do
  env <- ask
  let newV = pickFresh . M.elems $ env
  res <- local (M.insert 0 newV . M.mapKeys (+ 1)) (pFormulaMaybeParens f)
  return $ hsep [text "∃", pretty newV, res]
pFormula Bottom = return . text $ "⊥"
pFormula Top = return . text $ "⊤"
