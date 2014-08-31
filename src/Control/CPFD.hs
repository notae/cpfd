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
       -- * Variables and Domains
       , FDDomain
       , Domain
       , Var
       , Container (..), CList (..), CTraversable (..)
       , new, newL, newN, newNL, newT, newTL, newC, newCL
       , set, setS, setL
       -- * Constraint Store
       , Propagator
--        , add, add2, adds
       , ArcPropagator, arcConstraint
       , MultiPropagator, multiConstraint
       -- * Labelling
       , labelL, labelT, labelC
       -- * Primitive Constraint
       -- ** Core Constraint
       , alldiff
       , alldiffF
       -- ** Arithmetic Constraint
       , eq
       , le
       , neq
       , add'
       , sub
       , add3
       -- ** Modulo Constraint
       , eqmod
       , neqmod
       , alldiffmod
       ) where

import Control.Applicative ((<$>))
import Control.Applicative (Applicative)
import Control.Applicative (WrappedMonad (..))
import Control.Monad (forM)
import Control.Monad (liftM)
import Control.Monad (replicateM)
import Control.Monad.ST (ST)
import Control.Monad.ST (runST)
import Control.Monad.State (StateT)
import Data.Foldable (Foldable)
import Data.Maybe (listToMaybe)
import Data.STRef (STRef)
import Data.STRef (modifySTRef)
import Data.STRef (newSTRef)
import Data.STRef (readSTRef)
import Data.STRef (writeSTRef)
import Data.Set (Set)
import Data.Traversable (Traversable)
import qualified Data.Foldable as Foldable
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import Control.Monad.State (evalStateT)
import Control.Monad.Trans (lift)
import qualified Control.Monad.State as State


-- | Monad for constraints on finite domain
type FD s = StateT (FDState s) (ST s)

data FDState s = FDState { varList :: VarList s }

-- | Run FD monad
runFD :: (forall s. FD s a) -> a
runFD fd = runST $ flip evalStateT undefined $ do
  vl <- newVarList
  let state = FDState { varList = vl }
  State.put state
  fd

-- | Constraint for domain value
type FDDomain v = (Ord v, Show v)

-- | Domain of variables.
type Domain = Set

-- | Finite domain variable
data Var s v =
  Var
  { varDomain :: STRef s (Domain v)
  , varStack  :: STRef s [Domain v]
  , varAction :: STRef s (FD s Bool) }

-- | (for internal use in pool)
data NVar s = forall v. FDDomain v => NVar (Var s v)

class Container c where
  cmap :: (forall a. t a -> t' a) -> c t -> c t'
  cmapA :: Applicative f =>
           (forall a. FDDomain a => t a -> f (t' a)) -> c t -> f (c t')
  cmapM :: Monad m =>
           (forall a. FDDomain a => t a -> m (t' a)) -> c t -> m (c t')
  cmapM f = unwrapMonad . cmapA (WrapMonad . f)
  toList :: (forall a. FDDomain a => t a -> t') -> c t -> [t']

-- | (for internal use)
newtype CList v t = CList { unCList :: [t v] } deriving (Eq, Show)

instance FDDomain v => Container (CList v)  where
  cmap f (CList ts) = CList $ map f ts
  cmapA f (CList ts) = CList <$> Traversable.traverse f ts
  toList f (CList ts) = map f ts

-- | (for internal use)
newtype CTraversable t' v t =
  CTraversable { unCTraversable :: t' (t v) } deriving (Eq, Show)

instance (FDDomain v, Traversable t') =>
         Container (CTraversable t' v) where
  cmap f (CTraversable ts) = CTraversable $ fmap f ts
  cmapA f (CTraversable ts) = CTraversable <$> Traversable.traverse f ts
  toList f (CTraversable ts) = Foldable.toList $ fmap f ts

-- | Variable list
type VarList s = STRef s [NVar s]

-- | Create an empty variable list.
newVarList :: FD s (VarList s)
newVarList = lift $ newSTRef []

getVarList :: FD s [NVar s]
getVarList = do
  FDState vl <- State.get
  lift $ readSTRef vl

-- | (for debug)
showNVar :: NVar s -> FD s String
showNVar (NVar (Var vd vs _)) = do
  d <- lift $ readSTRef vd
  s <- lift $ readSTRef vs
  return $ show (d, s)

-- Primitives for variable domain

-- | Create a new variable with domain.
new :: FDDomain v => Domain v -> FD s (Var s v)
new d = do
  FDState vl <- State.get
  vd <- lift $ newSTRef d
  vs <- lift $ newSTRef []
  va <- lift $ newSTRef $ return True
  let v = Var vd vs va
  lift $ modifySTRef vl $ \nvs -> NVar v : nvs
  return v

-- | Get domain of the variable.
get :: Var s v -> FD s (Domain v)
get (Var vd _ _) = lift $ readSTRef vd

-- | Set domain of the variable and invoke propagators.
set :: FDDomain v => Var s v -> Domain v -> FD s Bool
set (Var vd _ va) d =
  if empty d
  then return False
  else do
    old <- lift $ readSTRef vd
    let sd   = Set.size d
    let sold = Set.size old
    if sd < sold
      then do
        lift $ writeSTRef vd d
        a <- lift $ readSTRef va
        a
      else if sd == sold
           then return True
           else error "invalid: tried to enlarge domain"

-- Utilities for variable domain

-- | Same as 'new' except to take a list as domain.
newL :: FDDomain v => [v] -> FD s (Var s v)
newL d = new (Set.fromList d)

-- | Same as 'new' except to take a number of variables to create.
newN :: FDDomain v => Int -> Domain v -> FD s [Var s v]
newN n d = replicateM n (new d)

-- | Same as 'newN' except to take a list as domain.
newNL :: FDDomain v => Int -> [v] -> FD s [Var s v]
newNL n d = replicateM n (newL d)

-- | Same as 'new' except to take a Traversable containing domains.
newT :: (FDDomain v, Traversable t) => t (Domain v) -> FD s (t (Var s v))
newT = Traversable.mapM new

-- | Same as 'new' except to take a Traversable containing lists as domains.
newTL :: (FDDomain v, Traversable t) => t [v] -> FD s (t (Var s v))
newTL = Traversable.mapM newL

-- | Same as 'new' except to take a Container containing domains.
newC :: Container c => c Domain -> FD s (c (Var s))
newC = cmapM new

-- | Same as 'new' except to take a Container containing domains.
newCL :: Container c => c [] -> FD s (c (Var s))
newCL = cmapM newL

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
getStack (Var _ vs _) = lift $ readSTRef vs

__push :: NVar s -> FD s ()
__push (NVar (Var vd vs _)) = do
  d <- lift $ readSTRef vd
  lift $ modifySTRef vs $ \ds -> d:ds

__pop :: NVar s -> FD s ()
__pop (NVar (Var vd vs _)) = do
  (d:ds) <- lift $ readSTRef vs
  lift $ writeSTRef vd d
  lift $ writeSTRef vs ds

push :: FD s ()
push = do
  vs <- getVarList
  mapM_ __push vs

pop :: FD s ()
pop = do
  vs <- getVarList
  mapM_ __pop vs

-- | Label variables specified in list.
labelL :: FDDomain v => [Var s v] -> FD s [[v]]
labelL l = liftM (map $ map head . unCList) $ labelC' (CList l) (map NVar l)

-- | Label variables specified in Traversable.
labelT :: (FDDomain v, Traversable t) => t (Var s v) -> FD s [t v]
labelT t = liftM (map $ fmap head . unCTraversable) $ labelC' (CTraversable t) (Foldable.toList $ fmap NVar t)

-- | Label variables specified in Container.
labelC :: Container c => c (Var s) -> FD s [c []]
labelC c = labelC' c (toList NVar c)

labelC' :: Container c => c (Var s) -> [NVar s] -> FD s [c []]
labelC' c nvs =
  case nvs of
    []        -> do
      c' <- getCL c
      return [c']
    _ -> do
      (NVar v, nvss) <- deleteFindMin nvs
      d <- getL v
      liftM concat $ forM d $ \i -> do
        push
        r <- setS v i
        s <- if r
             then labelC' c nvss
             else return []
        pop
        return s

-- | (for internal)
deleteFindMin :: [NVar s] -> FD s (NVar s, [NVar s])
deleteFindMin nvs = do
  vdss <- forM nvs $ \(NVar (Var vd _ _)) -> liftM Set.size $ lift $ readSTRef vd
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
  a <- lift $ readSTRef va
  let varAction' = do r <- a
                      if r then p else return False
  lift $ writeSTRef va varAction'

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

-- | Domain propagator for arc
type ArcPropagator a b = Domain a -> Domain b -> (Domain a, Domain b)

-- | Create arc constraint from propagator
arcConstraint :: (FDDomain a, FDDomain b) =>
                 ArcPropagator a b -> Var s a -> Var s b -> FD s Bool
arcConstraint c x y = add2 x y $ do
  dx <- get x
  dy <- get y
  let (dx', dy') = c dx dy
  rx <- set x dx'
  ry <- set y dy'
  return $ rx && ry

-- | Domain propagator for multiple-arc
type MultiPropagator v = [Domain v] -> [Domain v]

-- | Create multiple-arc constraint from propagator
multiConstraint :: FDDomain v => MultiPropagator v -> [Var s v] -> FD s Bool
multiConstraint c vs = adds vs $ do
  ds <- mapM get vs
  let ds' = c ds
  rs <- (`mapM` zip vs ds') $ uncurry set
  return $ and rs

-- Primitive constraints

-- | Equality constraint
eq :: FDDomain v => Var s v -> Var s v -> FD s Bool
eq x y = adds [x, y] $ do
  dx <- get x
  dy <- get y
  let dz = dx `Set.intersection` dy
  rx <- set x dz
  ry <- set y dz
  return (rx && ry)

-- | Inequality (<=) constraint
le :: FDDomain v => Var s v -> Var s v -> FD s Bool
le = arcConstraint leConstraint

leConstraint :: FDDomain v => ArcPropagator v v
leConstraint vx vy = (vx', vy') where
  minX = Set.findMin vx
  maxY = Set.findMax vy
  vx' = Set.filter (<= maxY) vx
  vy' = Set.filter (>= minX) vy

-- | Inequality (/=) constraint
neq :: FDDomain v => Var s v -> Var s v -> FD s Bool
neq = arcConstraint neqConstraint

neqConstraint :: FDDomain v => ArcPropagator v v
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

-- | x == y (mod m)
eqmod :: (FDDomain v, Integral v) => v -> Var s v -> Var s v -> FD s Bool
eqmod m = arcConstraint (eqmodConstraint m)

eqmodConstraint :: Integral v => v -> ArcPropagator v v
eqmodConstraint m vx vy = (vx', vy') where
  vmz = Set.map (`mod` m) vx `Set.intersection` Set.map (`mod` m) vy
  vx' = Set.filter (\e -> (e `mod` m) `Set.member` vmz) vx
  vy' = Set.filter (\e -> (e `mod` m) `Set.member` vmz) vy

-- | x /= y (mod m)
neqmod :: (FDDomain v, Integral v) => v -> Var s v -> Var s v -> FD s Bool
neqmod m = arcConstraint (neqmodConstraint m)

neqmodConstraint :: Integral v => v -> ArcPropagator v v
neqmodConstraint m vx vy = (vx'', vy'') where
  vmx = Set.map (`mod` m) vx
  vmy = Set.map (`mod` m) vy
  vy' = Set.filter (\e -> (e `mod` m) `Set.notMember` vmx) vy
  vx' = Set.filter (\e -> (e `mod` m) `Set.notMember` vmy) vx
  (vx'', vy'')
    | single vmx && single vmy =
      if vmx == vmy
      then (Set.empty, Set.empty)
      else (vx, vy)
    | single vmx && vmx `Set.isProperSubsetOf` vmy = (vx, vy')
    | single vmy && vmy `Set.isProperSubsetOf` vmx = (vx', vy)
    | otherwise = (vx, vy)

-- | Differ from each other in list (mod m)
alldiffmod :: (FDDomain v, Integral v) => v -> [Var s v] -> FD s Bool
alldiffmod _ []     = return True
alldiffmod m (v:vs) = do
  mapM_ (neqmod m v) vs
  alldiffmod m vs

-- | add' c x y means c = x + y (c is constant value)
add' :: (FDDomain v, Num v) => v -> Var s v -> Var s v -> FD s Bool
add' c = arcConstraint (addConstraint c)

addConstraint :: (Eq v, Num v) => v -> ArcPropagator v v
addConstraint c vx vy = (vx', vy') where
  vx' = Set.filter (\ix -> any (\iy -> ix+iy==c) $ Set.toList vy) vx
  vy' = Set.filter (\iy -> any (\ix -> ix+iy==c) $ Set.toList vx) vy

-- | add3 z x y means z = x + y
add3 :: (FDDomain v, Num v) => Var s v -> Var s v -> Var s v -> FD s Bool
add3 z x y = multiConstraint add3Constraint [x, y, z]

add3Constraint :: (Ord a, Num a) => MultiPropagator a
add3Constraint [vx, vy, vz] = [vx', vy', vz'] where
  minZ = Set.findMin vx + Set.findMin vy
  maxZ = Set.findMax vx + Set.findMax vy
  vz' = Set.filter (\e -> minZ <= e && e <= maxZ) vz
  --
  minX = Set.findMin vz - Set.findMax vy
  maxX = Set.findMax vz - Set.findMin vy
  vx' = Set.filter (\e -> minX <= e && e <= maxX) vx
  --
  minY = Set.findMin vz - Set.findMax vx
  maxY = Set.findMax vz - Set.findMin vx
  vy' = Set.filter (\e -> minY <= e && e <= maxY) vy

-- | sub c x y means x - y == c (c is constant value)
sub :: (FDDomain v, Num v) => v -> Var s v -> Var s v -> FD s Bool
sub c = arcConstraint (subConstraint c)

subConstraint :: (Eq a, Num a) => a -> ArcPropagator a a
subConstraint c vx vy = (vx', vy') where
  vx' = Set.filter (\ix -> any (\iy -> ix==iy+c) $ Set.toList vy) vx
  vy' = Set.filter (\iy -> any (\ix -> ix==iy+c) $ Set.toList vx) vy


-- Internal Tests

{-|
>>> testL
(fromList [1,2,3,4,5,6,7,8,9,10],fromList [1,2,3,4,5])
-}
testL :: (Domain Int, Domain Int)
testL = runFD $ do
  p <- newVarList
  v <- newL [1..10]
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
  [x, y] <- newTL [[1,3..11], [5..10]]
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
  [x, y, z] <- newTL [[1,3..11], [5..10], [5]]
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
  x <- newL [1,3..11]
  y <- newL [5..10]
  x `eq` y
  dx <- get x
  dy <- get y
  return (dx, dy)
