{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Substitution where

--import Debug.Trace
import Fin
import Formula

--------------------------------------------------------------------------------
-- Abstraction

bindTerm :: Eq a => SNat n -> a -> RawTerm n a -> RawTerm (Succ n) a
bindTerm n x (Func f ts) = Func f $ map (bindTerm n x) ts
bindTerm _ _ (Bound fin) = Bound . raiseFin $ fin
bindTerm n y (Free x) | x == y = Bound (maxOf n)
                               | otherwise = Free x

bindFormula' :: Eq a => SNat n -> a -> RawFormula n a -> RawFormula (Succ n) a
bindFormula' n x (Predicate ident terms) =
  Predicate ident (map (bindTerm n x) terms)
bindFormula' n x (Conj f1 f2) = bindFormula' n x f1 `Conj` bindFormula' n x f2
bindFormula' n x (Disj f1 f2) = bindFormula' n x f1 `Disj` bindFormula' n x f2
bindFormula' n x (Impl f1 f2) = bindFormula' n x f1 `Impl` bindFormula' n x f2
bindFormula' n x (Not f) = Not $ bindFormula' n x f
bindFormula' n x (Forall f) = Forall $ bindFormula' (SSucc n) x f
bindFormula' n x (Exists f) = Exists $ bindFormula' (SSucc n) x f
bindFormula' n x (Equality t1 t2) = Equality (bindTerm n x t1) (bindTerm n x t2)
bindFormula' _ _ Top = Top
bindFormula' _ _ Bottom = Bottom

bindFormula :: Eq a => a -> Formula a -> RawFormula (Succ Zero) a
bindFormula x f = bindFormula' SZero x f

abstractForall :: Eq a => a -> Formula a -> Formula a
abstractForall x f = Forall $ bindFormula x f

abstractExists :: Eq a => a -> Formula a -> Formula a
abstractExists x f = Exists $ bindFormula x f

--------------------------------------------------------------------------------
-- Instantiation

instantiateTerm :: SNat n -> a -> RawTerm (Succ n) a -> RawTerm n a
instantiateTerm _ _ (Free y) = Free y
instantiateTerm n x (Func f ts) = Func f $ map (instantiateTerm n x) ts
instantiateTerm n x (Bound fin) = case thick n (maxOf n) fin of
                                    Nothing -> Free x
                                    Just fin' -> Bound fin'

instantiateFormula :: SNat n -> a -> RawFormula (Succ n) a -> RawFormula n a
instantiateFormula n x (Predicate ident terms) =
  Predicate ident (map (instantiateTerm n x) terms)
instantiateFormula n x (Conj f1 f2) =
  Conj (instantiateFormula n x f1) (instantiateFormula n x f2)
instantiateFormula n x (Disj f1 f2) =
  Disj (instantiateFormula n x f1) (instantiateFormula n x f2)
instantiateFormula n x (Impl f1 f2) =
  Impl (instantiateFormula n x f1) (instantiateFormula n x f2)
instantiateFormula n x (Not f) = Not $ instantiateFormula n x f
instantiateFormula n x (Forall f) = Forall $ instantiateFormula (SSucc n) x f
instantiateFormula n x (Exists f) = Forall $ instantiateFormula (SSucc n) x f
instantiateFormula n x (Equality t1 t2) =
  Equality (instantiateTerm n x t1) (instantiateTerm n x t2)
instantiateFormula _ _ Top = Top
instantiateFormula _ _ Bottom = Bottom

instantiate :: a -> Formula a -> Formula a
instantiate x (Forall f) = instantiateFormula SZero x f
instantiate x (Exists f) = instantiateFormula SZero x f
instantiate _ _ = error "cannot instantiateFormula non-quantifier"

--------------------------------------------------------------------------------
-- Substitution

-- substInTerm' :: (forall m . RawTerm m a -> RawTerm m a) -> RawTerm n a -> RawTerm n a
-- substInTerm' f (Func name ts) = Func name $ map (substInTerm' f) ts
-- substInTerm' f t = f t

substFormula' :: (forall m . RawTerm m a -> RawTerm m a) -> RawFormula n a -> RawFormula n a
substFormula' f (Predicate ident terms) =
  Predicate ident (map f terms)
substFormula' f (Conj f1 f2) = substFormula' f f1 `Conj` substFormula' f f2
substFormula' f (Disj f1 f2) = substFormula' f f1 `Disj` substFormula' f f2
substFormula' f (Impl f1 f2) = substFormula' f f1 `Impl` substFormula' f f2
substFormula' f (Not fr) = Not $ substFormula' f fr
substFormula' f (Forall fr) = Forall $ substFormula' f fr
substFormula' f (Exists fr) = Exists $ substFormula' f fr
substFormula' f (Equality t1 t2) =
  Equality (f t1) (f t2)
substFormula' _ Top = Top
substFormula' _ Bottom = Bottom

substFormula :: (forall n . RawTerm n a -> RawTerm n a) -> Formula a -> Formula a
substFormula f = substFormula' f

simpleVarSub :: Eq a => a -> Term a -> RawTerm n a -> RawTerm n a
simpleVarSub x t = simpleTermSub (Free x) t

simpleTermSub :: Eq a => Term a -> Term a -> RawTerm n a -> RawTerm n a
simpleTermSub t1 t2 s
  | (raiseTerm t1) == s = (raiseTerm t2)
  | otherwise =
    case s of
      Func name ts -> Func name (map (simpleTermSub t1 t2) ts)
      _ -> s

raiseTerm :: Term a -> RawTerm n a
raiseTerm (Free x) = Free x
raiseTerm (Func name ts) = Func name (map raiseTerm ts)

