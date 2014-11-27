{-|
Module      : Control.CPFD.Domain
Description : Finite Domain
Copyright   : (c) notae@me.com, 2014
License     : BSD-style
Maintainer  : notae@me.com
Stability   : experimental
Portability : POSIX
-}

{-# LANGUAGE ConstraintKinds #-}

module Control.CPFD.Domain
       (
       -- * Types
         FDValue
       , Domain
       -- * Operators
       , (\\)
       -- * Query
       , null, single, size, member, notMember
       , isSubsetOf, isProperSubsetOf
       -- * Construction
       , empty, singleton
       -- * Combine
       , intersection
       -- * Filter
       , filter
       -- * Map
       , map
       -- * Min / Max
       , findMin, findMax
       -- * Conversion
       -- ** List
       , fromList
       , toList
       )
       where

import Prelude hiding (null, filter, map)
import Data.Set (Set)
import qualified Data.Set as Set

-- | Type constraint for domain value
type FDValue v = (Ord v, Show v)

-- | Domain of variables.
type Domain = Set

-- | Create a domain from list
fromList :: Ord v => [v] -> Set v
fromList = Set.fromList

-- | Create a domain from an element
singleton :: v -> Set v
singleton = Set.singleton

-- | Convert a domain to list
toList :: Set v -> [v]
toList = Set.toList

-- | Create an empty domain
empty :: Domain v
empty = Set.empty

-- | Check if domain is empty
null :: Domain v -> Bool
null s = Set.size s == 0

-- | Check if domain is singleton
single :: Domain v -> Bool
single s = Set.size s == 1

size :: Domain v -> Int
size = Set.size

intersection :: Ord v => Domain v -> Domain v -> Domain v
intersection = Set.intersection

findMin :: Domain v -> v
findMin = Set.findMin

findMax :: Domain v -> v
findMax = Set.findMax

filter :: (v -> Bool) -> Domain v -> Domain v
filter = Set.filter

isSubsetOf :: Ord v => Domain v -> Domain v -> Bool
isSubsetOf = Set.isSubsetOf

isProperSubsetOf :: Ord v => Domain v -> Domain v -> Bool
isProperSubsetOf = Set.isProperSubsetOf

(\\) :: Ord v => Domain v -> Domain v -> Domain v
(\\) = (Set.\\)

map :: Ord v' => (v -> v') -> Domain v -> Domain v'
map = Set.map

member :: Ord v => v -> Domain v -> Bool
member = Set.member

notMember :: Ord v => v -> Domain v -> Bool
notMember = Set.notMember
