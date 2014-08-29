{-|
Module      : Control.CPFD
Description : Constraint Programming over Finite Domain
Copyright   : (c) notae@me.com, 2014
License     : BSD-style
Maintainer  : notae@me.com
Stability   : experimental
Portability : POSIX

This module provides interfaces for constraint programming
over multiple finite domain in Haskell.
Originally from: <http://overtond.blogspot.jp/2008/07/pre.html>
-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}

module Control.CPFD
       (
       -- * Monads
         FD
       , runFD
       -- * Variables
       , FDDomain
       , Domain
       , Var
       , Pool
       , newPool
       , Container (..), List (..)
       , new, newL, newN, newNL, newT, newTL, newC, newCL
       , set, setS, setL
       -- * Constraint Store
       , Propagator
       , add, add2, adds
       , ArcPropagator
       , arcConstraint
       -- * Labelling
       , labelL, labelC
       -- * Primitive Constraint
       -- ** Core Constraint
       , alldiff
       , alldiffF
       -- ** Arithmetic Constraint
       , eq
--        , le
       , neq
--        , add
--        , sub
--        , add3
       -- ** Modulo Constraint
--        , eqmod
--        , neqmod
--        , alldiffmod
       ) where

import Control.Applicative ((<$>))
import Control.Applicative (Applicative)
import Control.Applicative (WrappedMonad (..))
import Control.Monad (forM)
import Control.Monad (liftM)
import Control.Monad.ST (ST)
import Control.Monad.ST (runST)
import Data.Foldable (Foldable)
import Data.Maybe (listToMaybe)
import Data.STRef (STRef)
import Data.STRef (modifySTRef)
import Data.STRef (newSTRef)
import Data.STRef (readSTRef)
import Data.STRef (writeSTRef)
import Data.Set (Set)
import Data.Traversable (Traversable)
import Data.Traversable (traverse)
import qualified Data.Foldable as Foldable
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import Control.Monad (replicateM)


-- | Monad for constraints on finite domain
type FD = ST

runFD :: (forall s. FD s a) -> a
runFD = runST

-- | Constraint for domain value
type FDDomain v = (Ord v, Show v)

-- | Domain of variables.
type Domain = Set

-- | Finite domain variable
data Var s v =
  Var
  { varDomain :: STRef s (Domain v)
  , varStack  :: STRef s [Domain v]
  , varAction :: STRef s (ST s Bool) }

class Container c where
  cmap :: (forall a. t a -> t' a) -> c t -> c t'
  cmapA :: Applicative f =>
           (forall a. FDDomain a => t a -> f (t' a)) -> c t -> f (c t')
  cmapM :: Monad m =>
           (forall a. FDDomain a => t a -> m (t' a)) -> c t -> m (c t')
  cmapM f = unwrapMonad . cmapA (WrapMonad . f)
  toList :: (forall a. FDDomain a => t a -> t') -> c t -> [t']

newtype List v t = List { unList :: [t v] } deriving (Show, Eq)

instance FDDomain v => Container (List v)  where
  cmap f (List ts) = List $ map f ts
  cmapA f (List ts) = List <$> traverse f ts
  toList f (List ts) = map f ts

data NVar s = forall v. FDDomain v => NVar (Var s v)

-- | Variable pool
type Pool s = STRef s [NVar s]

-- | Create an empty pool.
newPool :: FD s (Pool s)
newPool = newSTRef []

-- | (for debug)
showNVar :: NVar s -> FD s String
showNVar (NVar (Var vd vs _)) = do
  d <- readSTRef vd
  s <- readSTRef vs
  return $ show (d, s)

-- Primitives for variable domain

-- | Create a new variable with domain.
new :: FDDomain v => Pool s -> Domain v -> FD s (Var s v)
new p d = do
  vd <- newSTRef d
  vs <- newSTRef []
  va <- newSTRef $ return True
  let v = Var vd vs va
  modifySTRef p $ \nvs -> NVar v : nvs
  return v

-- | Get domain of the variable.
get :: Var s v -> FD s (Domain v)
get (Var vd _ _) = readSTRef vd

-- | Set domain of the variable and invoke propagators.
set :: FDDomain v => Var s v -> Domain v -> FD s Bool
set (Var vd _ va) d =
  if empty d
  then return False
  else do
    old <- readSTRef vd
    let sd   = Set.size d
    let sold = Set.size old
    if sd < sold
      then do
        writeSTRef vd d
        a <- readSTRef va
        a
      else if sd == sold
           then return True
           else error "invalid: tried to enlarge domain"

-- Utilities for variable domain

-- | Same as 'new' except to take a list as domain.
newL :: FDDomain v => Pool s -> [v] -> FD s (Var s v)
newL p d = new p (Set.fromList d)

newN :: FDDomain v => Pool s -> Int -> Domain v -> FD s [Var s v]
newN p n d = replicateM n (new p d)

newNL :: FDDomain v => Pool s -> Int -> [v] -> FD s [Var s v]
newNL p n d = replicateM n (newL p d)

-- | Same as 'new' except to take a Traversable containing domains.
newT :: (FDDomain v, Traversable t) =>
        Pool s -> t (Domain v) -> FD s (t (Var s v))
newT p = Traversable.mapM (new p)

-- | Same as 'new' except to take a Traversable containing lists as domains.
newTL :: (FDDomain v, Traversable t) =>
         Pool s -> t [v] -> FD s (t (Var s v))
newTL p = Traversable.mapM (newL p)

-- | Same as 'new' except to take a Container containing domains.
newC :: Container c => Pool s -> c Domain -> FD s (c (Var s))
newC p = cmapM (new p)

-- | Same as 'new' except to take a Container containing domains.
newCL :: Container c => Pool s -> c [] -> FD s (c (Var s))
newCL p = cmapM (newL p)

-- | Same as 'get' except to return a list as domain.
getL :: FDDomain v => Var s v -> FD s [v]
getL v = liftM Set.toList $ get v

-- | Same as 'get' except to return a Maybe as domain.
getM :: FDDomain v => Var s v -> FD s (Maybe v)
getM v = liftM (listToMaybe . Set.toList) $ get v

-- | Same as 'get' except to return a list as domain in Container.
getCL :: Container c => c (Var s) -> FD s (c [])
getCL = cmapM getL

-- | Same as 'get' except to return a Maybe as domain in Container.
getCM :: Container c => c (Var s) -> FD s (c Maybe)
getCM = cmapM getM

-- | Set domain of the variable with singleton value and invoke propagators.
setS :: FDDomain v => Var s v -> v -> FD s Bool
setS v val = set v (Set.singleton val)

-- | Same as 'set' except to take a list as domain.
setL :: FDDomain v => Var s v -> [v] -> FD s Bool
setL v d = set v (Set.fromList d)

-- | Check if domain is empty
empty :: Domain v -> Bool
empty s = Set.size s == 0

-- | Check if domain is singleton
single :: Domain v -> Bool
single s = Set.size s == 1

-- Labeling

-- | (for debug)
getStack :: Var s v -> FD s [Domain v]
getStack (Var _ vs _) = readSTRef vs

__push :: NVar s -> FD s ()
__push (NVar (Var vd vs _)) = do
  d <- readSTRef vd
  modifySTRef vs $ \ds -> d:ds

__pop :: NVar s -> FD s ()
__pop (NVar (Var vd vs _)) = do
  (d:ds) <- readSTRef vs
  writeSTRef vd d
  writeSTRef vs ds

_push :: Pool s -> FD s ()
_push p = do
  vs <- readSTRef p
  mapM_ __push vs

_pop :: Pool s -> FD s ()
_pop p = do
  vs <- readSTRef p
  mapM_ __pop vs

labelL :: FDDomain v => Pool s -> [Var s v] -> FD s [[v]]
labelL p l = liftM (map $ map head . unList) $ labelC' p (List l) (map NVar l)

labelC :: Container c => Pool s -> c (Var s) -> FD s [c []]
labelC p c = labelC' p c (toList NVar c)

labelC' :: Container c => Pool s -> c (Var s) -> [NVar s] -> FD s [c []]
labelC' p c nvs =
  case nvs of
    []        -> do
      c' <- getCL c
      return [c']
    _ -> do
      (NVar v, nvss) <- deleteFindMin nvs
      d <- getL v
      liftM concat $ forM d $ \i -> do
        _push p
        r <- setS v i
        s <- if r
             then labelC' p c nvss
             else return []
        _pop p
        return s

-- | (for internal)
deleteFindMin :: [NVar s] -> FD s (NVar s, [NVar s])
deleteFindMin nvs = do
  vdss <- forM nvs $ \(NVar (Var vd _ _)) -> liftM Set.size $ readSTRef vd
  let smin = minimum vdss
  let (former, latter) = span (\(vds, _) -> vds /= smin) $ zip vdss nvs
  let nvsmin = snd $ head latter
  let cnvs = map snd $ former ++ tail latter
  return (nvsmin, cnvs)

-- Primitives for variable domain propagator

-- | Propagate a domain changing to other domains.
-- Return True for sat / unknown, False for unsat.
type Propagator s = FD s Bool

-- | Add a propagator to the variable
add :: Var s v -> Propagator s -> FD s ()
add (Var _ _ va) p = do
  a <- readSTRef va
  let varAction' = do r <- a
                      if r then p else return False
  writeSTRef va varAction'

-- | Add a propagator to the variable and invoke it
add1 :: Var s v -> Propagator s -> FD s Bool
add1 v p = do
  add v p
  p

-- | Add a propagator to the variables and invoke it
add2 :: Var s v1 -> Var s v2 -> Propagator s -> FD s Bool
add2 v1 v2 p = do
  add v1 p
  add v2 p
  p

-- | Add a propagator to the variables and invoke it
adds :: [Var s v] -> Propagator s -> FD s Bool
adds vs p = do
  mapM_ (`add` p) vs
  p

-- Utilities for variable domain propagator

type ArcPropagator a b = Domain a -> Domain b -> (Domain a, Domain b)

arcConstraint :: (FDDomain a, FDDomain b) =>
                 ArcPropagator a b -> Var s a -> Var s b -> FD s Bool
arcConstraint c x y = add2 x y $ do
  dx <- get x
  dy <- get y
  let (dx', dy') = c dx dy
  rx <- set x dx'
  ry <- set y dy'
  return $ rx && ry

-- Primitive constraints

eq :: FDDomain v => Var s v -> Var s v -> FD s Bool
eq x y = adds [x, y] $ do
  dx <- get x
  dy <- get y
  let dz = dx `Set.intersection` dy
  rx <- set x dz
  ry <- set y dz
  return (rx && ry)

neq :: FDDomain v => Var s v -> Var s v -> FD s Bool
neq = arcConstraint neqConstraint

neqConstraint :: Ord v => ArcPropagator v v
neqConstraint vx vy
  | single vx && single vy =
    if vx == vy
    then (Set.empty, Set.empty)
    else (vx, vy)
  | single vx && vx `Set.isProperSubsetOf` vy = (vx, vy Set.\\ vx)
  | single vy && vy `Set.isProperSubsetOf` vx = (vx Set.\\ vy, vy)
  | otherwise = (vx, vy)

-- | Differ from each other in list
alldiff :: FDDomain v => [Var s v] -> FD s Bool
alldiff []     = return True
alldiff (v:vs) = do
  mapM_ (v `neq`) vs
  alldiff vs

-- | Differ from each other in Foldable
alldiffF :: (FDDomain v, Foldable f) => f (Var s v) ->FD s Bool
alldiffF = alldiff . Foldable.toList


-- Internal Tests

{-|
>>> testL
(fromList [1,2,3,4,5,6,7,8,9,10],fromList [1,2,3,4,5])
-}
testL :: (Domain Int, Domain Int)
testL = runFD $ do
  p <- newPool
  v <- newL p [1..10]
  val <- get v
  setL v [1..5]
  val' <- get v
  return (val, val')

{-|
>>> testTLProp
(fromList [5,7,9],fromList [5,7,9])
-}
testTLProp :: (Domain Int, Domain Int)
testTLProp = runFD $ do
  p <- newPool
  [x, y] <- newTL p [[1,3..11], [5..10]]
  x `eq` y
  dx <- get x
  dy <- get y
  return (dx, dy)

{-|
>>> testAlldiff
(fromList [1,3,7,9,11],fromList [6,7,8,9,10],fromList [5])
-}
testAlldiff :: (Domain Int, Domain Int, Domain Int)
testAlldiff = runFD $ do
  p <- newPool
  [x, y, z] <- newTL p [[1,3..11], [5..10], [5]]
  alldiff [x, y, z]
  dx <- get x
  dy <- get y
  dz <- get z
  return (dx, dy, dz)

{-|
>>> testProp
(fromList [5,7,9],fromList [5,7,9])
-}
testProp :: (Domain Int, Domain Int)
testProp = runFD $ do
  p <- newPool
  x <- newL p [1,3..11]
  y <- newL p [5..10]
  x `eq` y
  dx <- get x
  dy <- get y
  return (dx, dy)
