module Tree
  ( Location
  , Tree(..)
  , searchTree
  , dfsNext
  , start
  , end
  , label
  , tree
  , modifyTree
  ) where

import Control.Applicative
import Control.Monad
import Data.Tree
import Data.Tree.Zipper

type Location a = TreePos Full a

start :: Tree a -> Location a
start = fromTree

end :: Location a -> Tree a
end = toTree . root

forceRight :: Location a -> Location a
forceRight loc =
  case next loc of
    Nothing ->
      case parent loc of
        Nothing -> loc
        Just up -> forceRight up
    Just right -> right

dfsNext :: Location a -> Location a
dfsNext loc =
  case firstChild loc of
    Just loc' -> loc'
    Nothing -> forceRight loc

searchTree :: Eq a => Location a -> (Tree a -> Bool) -> Maybe (Location a)
searchTree loc p =
  if p (tree loc)
    then Just loc
    else searchTree' loc p (dfsNext loc)
  where
    searchTree' original p loc
      | original == loc = Nothing
      | otherwise =
        if p (tree loc)
          then Just loc
          else searchTree' original p (dfsNext loc)

dfsTraversal :: Location a -> [Location a]
dfsTraversal loc = loc : dfsTraversal (dfsNext loc)

dfsData :: Tree a -> [a]
dfsData = map label . dfsTraversal . fromTree
