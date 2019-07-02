module Utils.Renaming
  ( new_name
  , default_or_new_name
  ) where

import Data.Set (Set, notMember, member)

-- | Generate a new name distinct from the set of names in @ns@
new_name :: Set String -> String
new_name ns = head (Prelude.filter (\x -> notMember x ns) ["$" ++ (show i) | i <- [0..]])

-- | If @n@ is not contained in @ns@, return it. Otherwise, generate a new name
-- distinct from those contained in @ns@ and return it.
default_or_new_name :: String -> Set String -> String
default_or_new_name n ns = if member n ns then new_name ns else n