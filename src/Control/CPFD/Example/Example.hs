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
import Data.Traversable (traverse)
import qualified Data.Set as Set


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
  deriving (Show, Eq)

instance (FDDomain x, FDDomain y) =>
         Container (PairList x y) where
  cmap f (PairList ps) = PairList $ fmap (\(x, y) -> (f x, f y)) ps
  cmapA f (PairList ps) =
    PairList <$> traverse (\(tx, ty) -> (,) <$> f tx <*> f ty) ps
  toList f (PairList ps) = concatMap (\(x, y) -> [f x, f y]) ps

{-|
Test for constraints with multiple type variables in Container

>>> length $ testMT
6
-}
testMT :: [PairList Int Bool []]
testMT = runFD $ do
  p <- newPool
  v <- newCL p $
       PairList [ ([1..3], [True, False])
                , ([4..5], [True, False]) ]
  forM (unPairList v) $ uncurry mt
  labelC p v
