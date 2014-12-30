{-|
Module      : Control.CPFD.Internal
Description : Simple 2-List Queue for CPFD
Copyright   : (c) notae@me.com, 2014
License     : BSD-style
Maintainer  : notae@me.com
Stability   : experimental
Portability : POSIX
-}

module Control.CPFD.Internal.Queue
       (
         Queue, empty, null, fromList, toList, enq, deq
       ) where

import           Prelude hiding (null)
import qualified Prelude as Prelude

data Queue a = Queue [a] [a] deriving (Show)

empty :: Queue a
empty = Queue [] []

{-|
>>> null empty
True
>>> null $ enq 1 empty
False
>>> null $ Queue [] [1,2,3]
False
-}
null :: Queue a -> Bool
null (Queue is os) = Prelude.null is && Prelude.null os

{-|
>>> fromList []
Queue [] []
>>> fromList [1,2]
Queue [] [1,2]
-}
fromList :: [a] -> Queue a
fromList as = Queue [] as

{-|
>>> toList empty
[]
>>> toList $ enq 1 empty
[1]
>>> toList $ Queue [6,5,4] [1,2,3]
[1,2,3,4,5,6]
-}
toList :: Queue a -> [a]
toList (Queue is os) = os ++ reverse is

{-|
>>> enq 2 $ enq 1 empty
Queue [2,1] []
-}
enq :: a -> Queue a -> Queue a
enq a (Queue is os) = Queue (a:is) os

{-|
>>> deq $ enq 2 $ enq 1 empty
(1,Queue [] [2])
-}
deq :: Queue a -> (a, Queue a)
deq (Queue is [])     = deq $ Queue [] $ reverse is
deq (Queue is (a:os)) = (a, Queue is os)
