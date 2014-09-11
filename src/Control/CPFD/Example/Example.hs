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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.CPFD.Example.Example where

import Control.Applicative ((<$>))
import Control.Applicative ((<*>))
import Control.CPFD
import Control.Monad (forM_)
import Data.List (sort)
import Data.Traversable (traverse)
import qualified Data.Set as Set


{-|
>>> sort $ runFD test1
[[1,4],[1,5],[2,4],[2,5],[3,4],[3,5]]
-}
test1 :: FD s [[Int]]
test1 = do
  x <- newL [1..3]
  y <- newL [4..5]
  labelT [x, y]

{-|
>>> sort $ runFD test2
[[1,3],[2,2],[3,1]]
-}
test2 :: FD s [[Int]]
test2 = do
  x <- newL [1..3]
  y <- newL [1..3]
  add' 4 x y
  labelT [x, y]

{-|
>>> sort $ runFD test3
[[1,3,7],[2,2,8],[3,1,9]]
-}
test3 :: FD s [[Int]]
test3 = do
  x <- newL [1..10]
  y <- newL [1..10]
  z <- newL [1..10]
  add' 4 x y
  add' 10 y z
  labelT [x, y, z]

{-|
>>> sort $ runFD testSub1
[[1,3],[2,4],[3,5]]
-}
testSub1 :: FD s [[Int]]
testSub1 = do
  x <- newL [1..5]
  y <- newL [1..5]
  sub 2 y x
  labelT [x, y]

{-|
>>> sort $ runFD testEq1
[[1,3,1],[2,4,2],[3,5,3]]
-}
testEq1 :: FD s [[Int]]
testEq1 = do
  x <- newL [1..5]
  y <- newL [1..5]
  z <- newL [1..5]
  z `eq` x
  sub 2 y x
  labelT [x, y, z]

{-|
>>> sort $ runFD testLE1
[[1,1],[1,2],[1,3],[2,2],[2,3],[3,3]]
-}
testLE1 :: FD s [[Int]]
testLE1 = do
  x <- newL [1..3]
  y <- newL [1..3]
  x `le` y
  labelT [x, y]

{-|
>>> sort $ runFD testNeq1
[[1,2],[1,3],[2,1],[2,3],[3,1],[3,2]]
-}
testNeq1 :: FD s [[Int]]
testNeq1 = do
  x <- newL [1..3]
  y <- newL [1..3]
  x `neq` y
  labelT [x, y]

{-|
>>> length $ runFD testAlldiff1
6
-}
testAlldiff1 :: FD s [[Int]]
testAlldiff1 = do
  x <- newL [1..3]
  y <- newL [1..3]
  z <- newL [1..3]
  alldiff [x, y, z]
  labelT [x, y, z]

{-|
>>> length $ runFD testVars1
24
-}
testVars1 :: FD s [[Int]]
testVars1 = do
  xs <- newNL 4 [1..4]
  alldiff xs
  labelT xs

{-|
>>> sort $ runFD testAdd31
[[4,1,3],[4,2,2],[5,2,3],[5,3,2],[6,3,3]]
-}
testAdd31 :: FD s [[Int]]
testAdd31 = do
  x <- newL [4..8]
  y <- newL [0..3]
  z <- newL [2..3]
  add3 x y z
  labelT [x, y, z]

{-|
>>> sort $ runFD testAdd32
[[0,0,0],[0,1,1],[0,2,2],[1,0,1],[1,1,2],[1,2,3],[2,0,2],[2,1,3],[3,0,3]]
-}
testAdd32 :: FD s [[Int]]
testAdd32 = do
  x <- newL [0..3]
  y <- newL [0..2]
  z <- newL [0..3]
  add3 z x y
  labelT [x, y, z]

{-|
>>> sort $ runFD testEqmod1
[[4,1],[4,4],[5,2],[5,5]]
-}
testEqmod1 :: FD s [[Int]]
testEqmod1 = do
  x <- newL [4..5]
  y <- newL [0..5]
  eqmod 3 x y
  labelT [x, y]

{-|
>>> sort $ runFD testNeqmod1
[[4,0],[4,2],[4,3],[4,5],[5,0],[5,1],[5,3],[5,4]]
-}
testNeqmod1 :: FD s [[Int]]
testNeqmod1 = do
  x <- newL [4..5]
  y <- newL [0..5]
  neqmod 3 x y
  labelT [x, y]

{-|
>>> sort $ runFD testBool1
[[False,True,False],[True,False,True]]
-}
testBool1 :: FD s [[Bool]]
testBool1 = do
  x <- newL [False, True]
  y <- newL [False, True]
  z <- newL [False, True]
  x `neq` y
  y `neq` z
  labelT [x, y, z]

{-|
Embedding variable into Traversable
>>> sort $ runFD testTraversable
[[1,2],[1,3],[2,1],[2,3],[3,1],[3,2]]
-}
testTraversable :: FD s [[Int]]
testTraversable = do
  vars <- newTL [[1..3], [1..3]]
  alldiffF vars
  labelT vars

{-|
Example of constraints with multiple type variables
-}
mt :: Var s Int -> Var s Bool -> FD s ()
mt = arcConstraint "mt" mtConstraint

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
mtConstraint :: ArcPropRule Int Bool
mtConstraint vx vy = (vx', vy') where
  vx' = Set.filter (\x -> (x `mod` 2 == 0) `Set.member` vy) vx
  vy' = Set.filter (\y -> or [(x `mod` 2 == 0) == y | x <- Set.toList vx]) vy

{-|
Example of Container with multiple type variables
-}
type PairList x y = [(x, y)]

newtype CPairList x y t =
  CPairList { unPairList :: PairList (t x) (t y) }
  deriving (Show, Eq, Ord)

instance (FDDomain x, FDDomain y) =>
         ContainerMap (CPairList x y) where
  cmapA f (CPairList ps) =
    CPairList <$> traverse (\(tx, ty) -> (,) <$> f tx <*> f ty) ps
  fromContainer f (CPairList ps) = concatMap (\(x, y) -> [f x, f y]) ps

instance ContainerLift (CPairList x y) (PairList x y) where
  cup f ps = CPairList $ fmap (\(x, y) -> (f x, f y)) ps
  cdown f (CPairList ps) = fmap (\(x, y) -> (f x, f y)) ps

instance (ContainerMap (CPairList x y),
          ContainerLift (CPairList x y) (PairList x y)) =>
         Container (CPairList x y) (PairList x y)

{-|
Test for constraints with multiple type variables in Container

>>> length $ runFD testMT
6
>>> sort $ runFD testMT
[[(1,False),(4,True)],[(1,False),(5,False)],[(2,True),(4,True)],[(2,True),(5,False)],[(3,False),(4,True)],[(3,False),(5,False)]]
-}
testMT :: FD s [PairList Int Bool]
testMT = do
  CPairList v <- newCL $
                 CPairList [ ([1..3], [True, False])
                           , ([4..5], [True, False]) ]
  forM_ v $ uncurry mt
  labelC $ CPairList v
