{-# LANGUAGE RankNTypes #-}
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
import Control.Arrow hiding ((<+>))
import qualified Data.Map.Strict as M
import Text.PrettyPrint
import Control.Monad.Reader
import Data.List
import qualified Data.Set as S

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
data Logic = Classical | Intuitionistic
data Theory a = T
  { functionSymbols :: [a]
  , logic :: Logic
  , axioms :: [(a, Formula a)]
  , axiomSchemata :: [(a, Formula a -> Formula a)]
  }

instance (Show a, Pretty a, Ord a) => Show (Term a) where
  show t = render $ runReader (pTerm t) (M.empty, S.toList $ termFreeVars t)

instance (Show a, PickFresh a, Pretty a, Ord a) => Show (Formula a) where
  show f = render $ runReader (pFormula f) (M.empty, S.toList $ formulaFreeVars f)

instance (Show a, PickFresh a, Pretty a, Ord a) =>
         Show (Sequent a) where
  show (S fs1 fs2) = asd1 ++ " |- " ++ asd2
    where
      fvs = S.toList $ foldr S.union S.empty (map formulaFreeVars (fs1 ++ fs2))
      asd1 =
        join .
        intersperse ", " .
        map (render . flip runReader (M.empty, fvs) . pFormula) $
        (reverse fs1)
      asd2 =
        join .
        intersperse ", " .
        map (render . flip runReader (M.empty, fvs) . pFormula) $
        fs2

class PickFresh a where
  pickFresh :: [a] -> a

instance PickFresh String where
  pickFresh strs = aux 0 strs
    where
      aux :: Int -> [String] -> String
      aux i strs' =
        let x = "x" ++ (show i)
        in if elem x strs'
             then aux (i + 1) strs'
             else x

class Pretty a where
  pretty :: a -> Doc

instance Pretty String where
  pretty = text

pTerm :: Pretty a => RawTerm n a -> Reader (M.Map Int a, [a]) Doc
pTerm (Free x) = return . pretty $ x
pTerm (Func f xs) = do
  strs <- mapM pTerm xs
  return $
    text f <>
    if null strs
      then empty
      else parens (hcat (punctuate comma strs))
pTerm (Bound n) = do
  env <- fmap fst ask
  case M.lookup (toInt n) env of
    Nothing -> error "error in showTerm"
    Just x -> return . pretty $ x

isAtomic :: RawFormula n a -> Bool
isAtomic (Predicate _ _) = True
isAtomic Top = True
isAtomic Bottom = True
isAtomic _ = False

pFormulaMaybeParens :: _ => RawFormula n a -> Reader (M.Map Int a, [a]) Doc
pFormulaMaybeParens f = if not (isAtomic f)
                           then parens <$> (pFormula f)
                           else pFormula f

pFormula :: (Pretty a, PickFresh a) => RawFormula n a -> Reader (M.Map Int a, [a]) Doc
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
  env <- fmap fst ask
  fvs <- fmap snd ask
  let newV = pickFresh (M.elems env ++ fvs)
  res <- local ((M.insert 0 newV . M.mapKeys (+ 1)) *** id) (pFormulaMaybeParens f)
  return $ hsep [text "∀", pretty newV, res]
pFormula (Exists f) = do
  env <- fmap fst ask
  fvs <- fmap snd ask
  let newV = pickFresh (M.elems env ++ fvs)
  res <- local ((M.insert 0 newV . M.mapKeys (+ 1)) *** id) (pFormulaMaybeParens f)
  return $ hsep [text "∃", pretty newV, res]
pFormula Bottom = return . text $ "⊥"
pFormula Top = return . text $ "⊤"

--------------------------------------------------------------------------------
-- Free vars

termFreeVars :: Ord a => RawTerm n a -> S.Set a
termFreeVars (Free x) = S.singleton x
termFreeVars (Func _ ts) = foldr S.union S.empty (map termFreeVars ts)
termFreeVars (Bound _) = S.empty

formulaFreeVars :: Ord a => RawFormula n a -> S.Set a
formulaFreeVars (Predicate _ terms) =
  foldr S.union S.empty (map termFreeVars terms)
formulaFreeVars (Conj f1 f2) = formulaFreeVars f1 `S.union` formulaFreeVars f2
formulaFreeVars (Disj f1 f2) = formulaFreeVars f1 `S.union` formulaFreeVars f2
formulaFreeVars (Impl f1 f2) = formulaFreeVars f1 `S.union` formulaFreeVars f2
formulaFreeVars (Not fr) = formulaFreeVars fr
formulaFreeVars (Forall fr) = formulaFreeVars fr
formulaFreeVars (Exists fr) = formulaFreeVars fr
formulaFreeVars (Equality t1 t2) = termFreeVars t1 `S.union` termFreeVars t2
formulaFreeVars Top = S.empty
formulaFreeVars Bottom = S.empty

sequentFreeVars :: Ord a => Sequent a -> S.Set a
sequentFreeVars (S fs1 fs2) = foldr S.union S.empty (map formulaFreeVars (fs1 ++ fs2))

--------------------------------------------------------------------------------

toFormula :: Sequent a -> Formula a
toFormula (S lfs rfs) = foldr1 Conj lfs `Impl` foldr1 Disj rfs

updateTheory :: a -> Formula a -> Theory a -> Theory a
updateTheory thrmId formula (T fs l axs axsSch) =
  T fs l ((thrmId, formula) : axs) axsSch

intuitionisticLogic :: Theory a
intuitionisticLogic = T [] Intuitionistic [] []

classicalLogic :: Theory a
classicalLogic = T [] Classical [] []
