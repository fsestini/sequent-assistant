{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module FromString where

class FromString a where
  fromString :: String -> a

instance FromString String where
  fromString = id
