
-- | Lists of length at least 2.
--
--   Import as:
--   @
--      import Agda.Utils.List2 (List2(List2))
--      import qualified Agda.Utils.List2 as List2
--   @

module Agda.Utils.List2
  ( module Agda.Utils.List2
  , module Reexport
  ) where

import Control.DeepSeq
import Control.Monad                   ( (<=<) )

import qualified Data.List as List

import GHC.Exts                        ( IsList(..) )
import qualified GHC.Exts  as Reexport ( toList )

import Agda.Utils.List1                ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1

import Agda.Utils.Impossible

-- | Lists of length ≥2.
data List2 a = List2 a a [a]
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Safe. O(1).
head :: List2 a -> a
head (List2 a _ _) = a

-- | Safe. O(1).
tail :: List2 a -> List1 a
tail (List2 a b cs) = b :| cs

-- | Safe. O(n).
init :: List2 a -> List1 a
init (List2 a b cs) = a :| List1.init (b :| cs)

-- | Safe. O(1).
fromListMaybe :: [a] -> Maybe (List2 a)
fromListMaybe = fromList1Maybe <=< List1.nonEmpty

-- | Safe. O(1).
fromList1Maybe :: List1 a -> Maybe (List2 a)
fromList1Maybe = \case
  (a :| b : cs) -> Just (List2 a b cs)
  _ -> Nothing

instance IsList (List2 a) where
  type Item (List2 a) = a

  -- Unsafe! O(1).
  fromList :: [a] -> List2 a
  fromList (a : b : cs) = List2 a b cs
  fromList _            = __IMPOSSIBLE__

  toList :: List2 a -> [a]
  toList (List2 a b cs) = a : b : cs

-- | Safe. O(1).
toList1 :: List2 a -> List1 a
toList1 (List2 a b cs) = a :| b : cs

-- | Unsafe!
fromList1 :: List1 a -> List2 a
fromList1 (a :| b : cs) = List2 a b cs
fromList1 _             = __IMPOSSIBLE__

break :: (a -> Bool) -> List2 a -> ([a],[a])
break p = List.break p . toList

instance NFData a => NFData (List2 a) where
  rnf (List2 a b cs) = rnf a `seq` rnf b `seq` rnf cs
