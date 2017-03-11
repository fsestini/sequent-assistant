{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

module Rules where

import Formula
import Substitution
import Control.Monad.Except
import qualified Data.Set as S

type ExceptS a = Except String a
type Rule a = Sequent a -> ExceptS [Sequent a]

data Addition a = Addition { addLeft :: [Formula a], addRight :: [Formula a]}

liftRuleLeft :: MonadError String m => (Formula a -> m [Addition a])
             -> Sequent a -> m [Sequent a]
liftRuleLeft f (S (l:ls) rs) = do
  frss <- f l
  let sequents = map (\frs -> S (addLeft frs ++ ls) (addRight frs ++ rs)) frss
  return sequents  
liftRuleLeft _ _ = throwError "cannot apply left rule to empty antecedent"

liftRuleRight :: MonadError String m => (Formula a -> m [Addition a])
              -> Sequent a -> m [Sequent a]
liftRuleRight f (S ls (r : rs)) = do
  frss <- f r
  let sequents = map (\frs -> S (addLeft frs ++ ls) (addRight frs ++ rs)) frss
  return sequents
liftRuleRight _ _ = throwError "cannot apply right rule to empty succedent"

isAxiom :: Eq a => Sequent a -> Bool
isAxiom sequent = isIdAxiom sequent || isReflAxiom sequent

isIdAxiom :: Eq a => Sequent a -> Bool
isIdAxiom (S fs1 fs2) = or $ map (uncurry (==)) mix
  where
    mix = [(f1, f2) | f1 <- fs1, f2 <- fs2]

isReflAxiom :: Eq a => Sequent a -> Bool
isReflAxiom (S _ fs) = any pred fs
  where
    pred (Equality t1 t2) = t1 == t2
    pred _ = False

identity :: Eq a => Sequent a -> ExceptS [Sequent a]
identity sequent =
  if isIdAxiom sequent
    then return []
    else throwError "no formulas unify"

reflexivity :: Eq a => Sequent a -> ExceptS [Sequent a]
reflexivity sequent =
  if isReflAxiom sequent
    then return []
    else throwError "reflexivity does not apply here"

andLeft :: Sequent a -> ExceptS [Sequent a]
andLeft = liftRuleLeft andLeft'
  where
    andLeft' (Conj f1 f2) = return [Addition [f1, f2] []]
    andLeft' _ = throwError "no left conjunction in position"

andRight :: Sequent a -> ExceptS [Sequent a]
andRight = liftRuleRight andRight'
  where
    andRight' (Conj f1 f2) = return [Addition [] [f1], Addition [] [f2]]
    andRight' _ = throwError "no right conjunction in position"

orLeft :: Sequent a -> ExceptS [Sequent a]
orLeft = liftRuleLeft orLeft'
  where
    orLeft' (Disj f1 f2) = return [Addition [f1] [], Addition [f2] []]
    orLeft' _ = throwError "no left disjunction in position"

orRight :: Sequent a -> ExceptS [Sequent a]
orRight = liftRuleRight orRight'
  where
    orRight' (Disj f1 f2) = return [Addition [] [f1, f2]]
    orRight' _ = throwError "no right disjunction in position"

notLeft :: Sequent a -> ExceptS [Sequent a]
notLeft = liftRuleLeft notLeft'
  where
    notleft' (Not f) = return [Addition [] [f]]
    notLeft' _ = throwError "no left negation in position"

notRight :: Sequent a -> ExceptS [Sequent a]
notRight = liftRuleRight notRight'
  where
    notRight' (Not f) = return [Addition [f] []]
    notRight' _ = throwError "no right negation in position"

implLeft :: Sequent a -> ExceptS [Sequent a]
implLeft = liftRuleLeft implLeft'
  where
    implLeft' (Impl f1 f2) = return [Addition [] [f1], Addition [f2] []]
    implLeft' _ = throwError "no left implication in position"

implRight :: Sequent a -> ExceptS [Sequent a]
implRight = liftRuleRight implRight'
  where
    implRight' (Impl f1 f2) = return [Addition [f1] [f2]]
    implRight' _ = throwError "no right implication in position"

forallLeft :: forall a . (Ord a, PickFresh a) => Term a -> Sequent a -> ExceptS [Sequent a]
forallLeft term sequent = liftRuleLeft forallLeft' $ sequent
  where
    newV = pickFresh . S.toList . sequentFreeVars $ sequent
    forallLeft' original@(Forall _) =
      let fr' = instantiate newV original
          fr'' = substFormula (simpleVarSub newV (raiseTerm term)) fr'
      in return [Addition [fr'', original] []]
    forallLeft' _ = throwError "no left forall in position"

forallRight :: forall a . (Ord a, PickFresh a) => Sequent a -> ExceptS [Sequent a]
forallRight sequent = liftRuleRight forallRight' $ sequent
  where
    w = pickFresh . S.toList . sequentFreeVars $ sequent
    forallRight' f@(Forall _) = return [Addition [] [instantiate w f]]
    forallRight' _ = throwError "no right forall in position"

existsLeft :: (Ord a, PickFresh a) => Sequent a -> ExceptS [Sequent a]
existsLeft sequent = liftRuleLeft existsLeft' $ sequent
  where
    w = pickFresh . S.toList . sequentFreeVars $ sequent
    existsLeft' f@(Exists _) = return [Addition [instantiate w f] []]
    existsLeft' _ = throwError "no left existential in position"

existsRight :: forall a . (Ord a, PickFresh a) => Term a -> Sequent a -> ExceptS [Sequent a]
existsRight term sequent = liftRuleRight existsRight' $ sequent
  where
    newV = pickFresh . S.toList . sequentFreeVars $ sequent
    existsRight' f@(Exists _) =
      let f' = instantiate newV f
          f'' = substFormula (simpleVarSub newV (raiseTerm term)) f'
      in return [Addition [] [f'', f]]
    existsRight' _ = throwError "no right existential in position"

equalityLeft :: Eq a => Int -> Sequent a -> ExceptS [Sequent a]
equalityLeft i (S (Equality t1 t2:lfs) rfs) =
  if i < length lfs
     then return [(S (Equality t1 t2 : transform i asd lfs) rfs)]
     else throwError "index out of range"
  where
    asd = substFormula (simpleTermSub t1 t2)
equalityLeft _ _ = throwError "no left equality in position"

equalityRight :: Eq a => Int -> Sequent a -> ExceptS [Sequent a]
equalityRight i (S (Equality t1 t2:lfs) rfs) =
  if i < length rfs
    then return [(S (Equality t1 t2 : lfs) (transform i asd rfs))]
    else throwError "index out of range"
  where
    asd = substFormula (simpleTermSub t1 t2)
equalityRight _ _ = throwError "no left equality in position"

transform :: Eq a => Int -> (a -> a) -> [a] -> [a]
transform i f fs =
  let mapped = map mapper (zip [0 ..] fs)
  in map snd mapped
  where
    mapper (j, f') = if i == j then (j, f f') else (j, f')

maybeIndex :: Int -> [a] -> Maybe a
maybeIndex _ [] = Nothing
maybeIndex 0 (x : _) = Just x
maybeIndex n (_ : xs) = maybeIndex (n - 1) xs

exchangeLeft :: Eq a => Int -> Sequent a -> ExceptS [Sequent a]
exchangeLeft i (S lfs rfs) =
  case exchange i lfs of
    Nothing -> throwError "index out of range"
    Just lfs' -> return [(S lfs' rfs)]

exchangeRight :: Eq a => Int -> Sequent a -> ExceptS [Sequent a]
exchangeRight i (S lfs rfs) =
  case exchange i rfs of
    Nothing -> throwError "index out of range"
    Just rfs' -> return [(S lfs rfs')]

exchange :: Eq a => Int -> [a] -> Maybe [a]
exchange _ [] = Nothing
exchange 0 xs = return xs
exchange i list@(x:xs) = do
  listElem <- maybeIndex i list
  return $ listElem : transform (i - 1) (const x) xs
