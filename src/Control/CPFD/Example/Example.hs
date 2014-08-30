{-|
Module      : Control.CPFD.Example.Example
Description : Example for Constraint Programming over Finite Domain
Copyright   : (c) notae@me.com, 2014
License     : BSD-style
Maintainer  : notae@me.com
Stability   : experimental
Portability : POSIX
-}

{-# LANGUAGE ConstraintKinds #-}

module Control.CPFD.Example.Example where

import Control.Applicative ((<$>))
import Control.Applicative ((<*>))
import Control.CPFD
import Control.Monad (forM)
import Data.List (sort)
import Data.Traversable (traverse)
import qualified Data.Set as Set


{-|
>>> sort test1
[[1,4],[1,5],[2,4],[2,5],[3,4],[3,5]]
-}
test1 :: [[Int]]
test1 = runFD' $ \p -> do
  x <- newL p [1..3]
  y <- newL p [4..5]
  labelL p [x, y]

{-|
>>> sort test2
[[1,3],[2,2],[3,1]]
-}
test2 :: [[Int]]
test2 = runFD' $ \p -> do
  x <- newL p [1..3]
  y <- newL p [1..3]
  add' 4 x y
  labelL p [x, y]

{-|
>>> sort test3
[[1,3,7],[2,2,8],[3,1,9]]
-}
test3 :: [[Int]]
test3 = runFD' $ \p -> do
  x <- newL p [1..10]
  y <- newL p [1..10]
  z <- newL p [1..10]
  add' 4 x y
  add' 10 y z
  labelL p [x, y, z]

{-|
>>> sort testSub1
[[1,3],[2,4],[3,5]]
-}
testSub1 :: [[Int]]
testSub1 = runFD' $ \p -> do
  x <- newL p [1..5]
  y <- newL p [1..5]
  sub 2 y x
  labelL p [x, y]

{-|
>>> sort testEq1
[[1,3,1],[2,4,2],[3,5,3]]
-}
testEq1 :: [[Int]]
testEq1 = runFD' $ \p -> do
  x <- newL p [1..5]
  y <- newL p [1..5]
  z <- newL p [1..5]
  z `eq` x
  sub 2 y x
  labelL p [x, y, z]

{-|
>>> sort testLE1
[[1,1],[1,2],[1,3],[2,2],[2,3],[3,3]]
-}
testLE1 :: [[Int]]
testLE1 = runFD' $ \p -> do
  x <- newL p [1..3]
  y <- newL p [1..3]
  x `le` y
  labelL p [x, y]

{-|
>>> sort testNeq1
[[1,2],[1,3],[2,1],[2,3],[3,1],[3,2]]
-}
testNeq1 :: [[Int]]
testNeq1 = runFD' $ \p -> do
  x <- newL p [1..3]
  y <- newL p [1..3]
  x `neq` y
  labelL p [x, y]

{-|
>>> length testAlldiff1
6
-}
testAlldiff1 :: [[Int]]
testAlldiff1 = runFD' $ \p -> do
  x <- newL p [1..3]
  y <- newL p [1..3]
  z <- newL p [1..3]
  alldiff [x, y, z]
  labelL p [x, y, z]

{-|
>>> length testVars1
24
-}
testVars1 :: [[Int]]
testVars1 = runFD' $ \p -> do
  xs <- newNL p 4 [1..4]
  alldiff xs
  labelL p xs

{-|
>>> sort testAdd31
[[4,1,3],[4,2,2],[5,2,3],[5,3,2],[6,3,3]]
-}
testAdd31 :: [[Int]]
testAdd31 = runFD' $ \p -> do
  x <- newL p [4..8]
  y <- newL p [0..3]
  z <- newL p [2..3]
  add3 x y z
  labelL p [x, y, z]

{-|
>>> sort testAdd32
[[0,0],[0,1],[0,2],[1,1],[1,2],[1,3],[2,2],[2,3],[3,3]]
-}
testAdd32 :: [[Int]]
testAdd32 = runFD' $ \p -> do
  x <- newL p [0..3]
  y <- newL p [0..3]
  z <- newL p [0..2]
  add3 y x z
  labelL p [x, y]

{-|
>>> sort testEqmod1
[[4,1],[4,4],[5,2],[5,5]]
-}
testEqmod1 :: [[Int]]
testEqmod1 = runFD' $ \p -> do
  x <- newL p [4..5]
  y <- newL p [0..5]
  eqmod 3 x y
  labelL p [x, y]

{-|
>>> sort testNeqmod1
[[4,0],[4,2],[4,3],[4,5],[5,0],[5,1],[5,3],[5,4]]
-}
testNeqmod1 :: [[Int]]
testNeqmod1 = runFD' $ \p -> do
  x <- newL p [4..5]
  y <- newL p [0..5]
  neqmod 3 x y
  labelL p [x, y]

{-|
>>> sort testBool1
[[False,True,False],[True,False,True]]
-}
testBool1 :: [[Bool]]
testBool1 = runFD' $ \p -> do
  x <- newL p [False, True]
  y <- newL p [False, True]
  z <- newL p [False, True]
  x `neq` y
  y `neq` z
  labelL p [x, y, z]

{-|
Embedding variable into Traversable
>>> sort testTraversable
[[1,2],[1,3],[2,1],[2,3],[3,1],[3,2]]
-}
testTraversable :: [[Int]]
testTraversable = runFD' $ \p -> do
  vars <- newTL p [[1..3], [1..3]]
  alldiffF vars
  labelT p vars

{-|
Example of constraints with multiple type variables
-}
mt :: Var s Int -> Var s Bool -> FD s Bool
mt = arcConstraint mtConstraint

{-|
>>> mtConstraint (Set.fromList [1..10]) (Set.fromList [True,False])
(fromList [1,2,3,4,5,6,7,8,9,10],fromList [False,True])

>>> mtConstraint (Set.fromList [1..10]) (Set.fromList [True])
(fromList [2,4,6,8,10],fromList [True])
>>> mtConstraint (Set.fromList [1..10]) (Set.fromList [False])
(fromList [1,3,5,7,9],fromList [False])

>>> mtConstraint (Set.fromList [2,4..10]) (Set.fromList [True,False])
(fromList [2,4,6,8,10],fromList [True])
>>> mtConstraint (Set.fromList [1,3..9]) (Set.fromList [True,False])
(fromList [1,3,5,7,9],fromList [False])

>>> mtConstraint (Set.fromList [2,4..10]) (Set.fromList [False])
(fromList [],fromList [])
>>> mtConstraint (Set.fromList [1,3..9]) (Set.fromList [True])
(fromList [],fromList [])

>>> mtConstraint (Set.fromList []) (Set.fromList [True,False])
(fromList [],fromList [])
>>> mtConstraint (Set.fromList [1..10]) (Set.fromList [])
(fromList [],fromList [])
-}
mtConstraint :: ArcPropagator Int Bool
mtConstraint vx vy = (vx', vy') where
  vx' = Set.filter (\x -> (x `mod` 2 == 0) `Set.member` vy) vx
  vy' = Set.filter (\y -> or [(x `mod` 2 == 0) == y | x <- Set.toList vx]) vy

{-|
Example of Container with multiple type variables
-}

newtype PairList x y t =
  PairList { unPairList :: [(t x, t y)] }
  deriving (Show, Eq, Ord)

instance (FDDomain x, FDDomain y) =>
         Container (PairList x y) where
  cmap f (PairList ps) = PairList $ fmap (\(x, y) -> (f x, f y)) ps
  cmapA f (PairList ps) =
    PairList <$> traverse (\(tx, ty) -> (,) <$> f tx <*> f ty) ps
  toList f (PairList ps) = concatMap (\(x, y) -> [f x, f y]) ps

{-|
Test for constraints with multiple type variables in Container

>>> length testMT
6
>>> sort testMT
[PairList {unPairList = [([1],[False]),([4],[True])]},PairList {unPairList = [([1],[False]),([5],[False])]},PairList {unPairList = [([2],[True]),([4],[True])]},PairList {unPairList = [([2],[True]),([5],[False])]},PairList {unPairList = [([3],[False]),([4],[True])]},PairList {unPairList = [([3],[False]),([5],[False])]}]-}
testMT :: [PairList Int Bool []]
testMT = runFD' $ \p -> do
  v <- newCL p $
       PairList [ ([1..3], [True, False])
                , ([4..5], [True, False]) ]
  forM (unPairList v) $ uncurry mt
  labelC p v
