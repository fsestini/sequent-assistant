{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}

module Fin where

data Nat = Zero | Succ Nat

data Fin :: Nat -> * where
  FZero :: Fin n
  FSucc :: Fin n -> Fin (Succ n)

deriving instance Eq (Fin n)

data SNat :: Nat -> * where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)

maxOf :: SNat n -> Fin (Succ n)
maxOf SZero = FZero
maxOf (SSucc n) = FSucc (maxOf n)

thick :: SNat n -> Fin (Succ n) -> Fin (Succ n) -> Maybe (Fin n)
thick SZero FZero FZero = Nothing
thick SZero FZero (FSucc f2) = Just f2
thick (SSucc _) FZero FZero = Nothing
thick (SSucc _) FZero (FSucc f2) = Just f2
thick (SSucc _) (FSucc _) FZero = Just FZero
thick (SSucc n) (FSucc f1) (FSucc f2) = fmap FSucc (thick n f1 f2)

raiseFin :: Fin n -> Fin (Succ n)
raiseFin FZero = FZero
raiseFin (FSucc n) = FSucc (raiseFin n)

toInt :: Fin n -> Int
toInt FZero = 0
toInt (FSucc fin) = toInt fin + 1
