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

import qualified Data.Set as S
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
bindFormula' n x (Term t) = Term (bindTerm n x t)
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
instantiateFormula n x (Term t) = Term $ instantiateTerm n x t
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

substInTerm' :: (forall m . RawTerm m a -> RawTerm m a) -> RawTerm n a -> RawTerm n a
substInTerm' f (Func name ts) = Func name $ map (substInTerm' f) ts
substInTerm' f t = f t

substFormula' :: (forall m . RawTerm m a -> RawTerm m a) -> RawFormula n a -> RawFormula n a
substFormula' f (Term t) = Term . substInTerm' f $ t
substFormula' f (Conj f1 f2) = substFormula' f f1 `Conj` substFormula' f f2
substFormula' f (Disj f1 f2) = substFormula' f f1 `Disj` substFormula' f f2
substFormula' f (Impl f1 f2) = substFormula' f f1 `Impl` substFormula' f f2
substFormula' f (Not fr) = Not $ substFormula' f fr
substFormula' f (Forall fr) = Forall $ substFormula' f fr
substFormula' f (Exists fr) = Exists $ substFormula' f fr
substFormula' f (Equality t1 t2) =
  Equality (substInTerm' f t1) (substInTerm' f t2)
substFormula' _ Top = Top
substFormula' _ Bottom = Bottom

substFormula :: (Term a -> Term a) -> Formula a -> Formula a
substFormula f = substFormula' (raiseSubst f)

simpleVarSub :: Eq a => a -> Term a -> Term a -> Term a
simpleVarSub x t (Free y) | x == y = t
                          | otherwise = Free y
simpleVarSub _ _ t = t

simpleTermSub :: Eq a => Term a -> Term a -> Term a -> Term a
simpleTermSub t t' s = if t == s then t' else s

raiseTerm :: Term a -> RawTerm n a
raiseTerm (Free x) = Free x
raiseTerm (Func name ts) = Func name (map raiseTerm ts)

raiseSubst :: (Term a -> Term a) -> RawTerm n a -> RawTerm n a
raiseSubst _ t@(Bound _) = t
raiseSubst f (Free x) = raiseTerm $ f (Free x)
raiseSubst f (Func name ts) = Func name (map (raiseSubst f) ts)

--------------------------------------------------------------------------------
-- Free vars

termFreeVars :: Ord a => RawTerm n a -> S.Set a
termFreeVars (Free x) = S.singleton x
termFreeVars (Func _ ts) = foldr S.union S.empty (map termFreeVars ts)
termFreeVars (Bound _) = S.empty

freeVars :: Ord a => RawFormula n a -> S.Set a
freeVars (Term t) = termFreeVars t
freeVars (Conj f1 f2) = freeVars f1 `S.union` freeVars f2
freeVars (Disj f1 f2) = freeVars f1 `S.union` freeVars f2
freeVars (Impl f1 f2) = freeVars f1 `S.union` freeVars f2
freeVars (Not fr) = freeVars fr
freeVars (Forall fr) = freeVars fr
freeVars (Exists fr) = freeVars fr
freeVars (Equality t1 t2) = termFreeVars t1 `S.union` termFreeVars t2
freeVars Top = S.empty
freeVars Bottom = S.empty

sequentFreeVars :: Ord a => Sequent a -> S.Set a
sequentFreeVars (S fs1 fs2) = foldr S.union S.empty (map freeVars (fs1 ++ fs2))
