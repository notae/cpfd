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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.CPFD
       (
       -- * Monads
         FD
       , runFD, runFD'
       -- * Variables and Domains
       , FDDomain
       , Domain
       , Var
       , Container, ContainerMap (..), ContainerLift (..)
       , CTraversable (..)
       , new, newL, newN, newNL, newT, newTL, newC, newCL
       , set, setS, setL
       -- * Constraint Store
       , Propagator
       , ArcPropagator, arcConstraint
       , MultiPropagator, multiConstraint
       -- * Labelling
       , labelT, labelC
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
import Control.Monad (unless)
import Control.Monad (when)
import Control.Monad.ST (ST)
import Control.Monad.ST (runST)
import Control.Monad.State (StateT)
import Control.Monad.State (evalStateT)
import qualified Control.Monad.State as State
import Control.Monad.Trans (lift)
import Control.Monad.Writer (WriterT)
import Control.Monad.Writer (runWriterT)
import Control.Monad.Writer (tell)
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.Maybe (listToMaybe)
import Data.STRef (STRef)
import Data.STRef (modifySTRef)
import Data.STRef (newSTRef)
import Data.STRef (readSTRef)
import Data.STRef (writeSTRef)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import qualified Data.Traversable as Traversable
import Debug.Trace (traceM)

import Control.CPFD.Internal.Queue (Queue)
import qualified Control.CPFD.Internal.Queue as Queue

-- | Monad for constraints on finite domain
type FD s = WriterT [String] (StateT (FDState s) (ST s))

-- | (for internal use)
liftST :: ST s a -> FD s a
liftST = lift . lift

-- | (for internal use)
data FDState s =
  FDState
  { varList :: VarList s
  , propQueue :: STRef s (Queue (String, Propagator s))
  , propStack :: STRef s [String]
  , traceFlag :: Bool }

-- | Run FD monad
runFD :: (forall s. FD s a) -> a
runFD fd = fst $ runST $ flip evalStateT undefined $ runWriterT $ fdWrapper False fd

-- | Run FD monad with trace
runFD' :: (forall s. FD s a) -> (a, [String])
runFD' fd = runST $ flip evalStateT undefined $ runWriterT $ fdWrapper True fd

-- | (for internal use)
fdWrapper :: Bool -> FD s a -> FD s a
fdWrapper tf fd = do
  vl <- newVarList
  rpq <- liftST $ newSTRef Queue.empty
  rst <- liftST $ newSTRef []
  State.put FDState { varList = vl
                    , propQueue = rpq
                    , propStack = rst
                    , traceFlag = tf }
  tell ["Initialized."]
  a <- fd
  tell ["Terminated."]
  return a

-- | Constraint for domain value
type FDDomain v = (Ord v, Show v)

-- | Domain of variables.
type Domain = Set

-- | Finite domain variable
data Var s v =
  Var
  { varDomain :: STRef s (Domain v)
  , varStack  :: STRef s [Domain v]
  , varAction :: STRef s [(String, Propagator s)] }

-- | (for internal use in variable list)
data NVar s = forall v. FDDomain v => NVar (Var s v)

class ContainerMap c where
  cmapA :: Applicative f =>
           (forall a. FDDomain a => t a -> f (t' a)) -> c t -> f (c t')
  cmapM :: Monad m =>
           (forall a. FDDomain a => t a -> m (t' a)) -> c t -> m (c t')
  cmapM f = unwrapMonad . cmapA (WrapMonad . f)
  fromContainer :: (forall a. FDDomain a => t a -> t') -> c t -> [t']

class ContainerLift c c' where
  cup :: (forall a. a -> t a) -> c' -> c t
  cdown :: (forall a. t a -> a) -> c t -> c'

-- | Container to hold data (variable domain, reference,
-- assignment, etc.) related to variables.
class (ContainerMap c, ContainerLift c c') => Container c c'

-- | (for internal use)
newtype CTraversable t' v t =
  CTraversable { unCTraversable :: t' (t v) } deriving (Eq, Show)

instance (FDDomain v, Traversable t') =>
         ContainerMap (CTraversable t' v) where
  cmapA f (CTraversable ts) = CTraversable <$> Traversable.traverse f ts
  fromContainer f (CTraversable ts) = Foldable.toList $ fmap f ts

instance Traversable t' => ContainerLift (CTraversable t' v) (t' v) where
  cup f ts = CTraversable $ fmap f ts
  cdown f (CTraversable ts) = fmap f ts

instance (ContainerMap (CTraversable t' v),
          ContainerLift (CTraversable t' v) (t' v)) =>
         Container (CTraversable t' v) (t' v)

-- | Variable list
type VarList s = STRef s [NVar s]

-- | Create an empty variable list.
newVarList :: FD s (VarList s)
newVarList = liftST $ newSTRef []

getVarList :: FD s [NVar s]
getVarList = do
  vl <- State.gets varList
  liftST $ readSTRef vl

-- | (for debug)
showNVar :: NVar s -> FD s String
showNVar (NVar (Var vd vs _)) = do
  d <- liftST $ readSTRef vd
  s <- liftST $ readSTRef vs
  return $ show (d, s)

-- | (for debug)
traceM' :: String -> FD s ()
traceM' s = do
  f <- State.gets traceFlag
  when f $ traceM s

-- Primitives for variable domain

-- | Create a new variable with domain.
new :: FDDomain v => Domain v -> FD s (Var s v)
new d = do
  vl <- State.gets varList
  vd <- liftST $ newSTRef d
  vs <- liftST $ newSTRef []
  va <- liftST $ newSTRef []
  let v = Var vd vs va
  liftST $ modifySTRef vl $ \nvs -> NVar v : nvs
  return v

-- | Get domain of the variable.
get :: Var s v -> FD s (Domain v)
get (Var vd _ _) = do
  execProp
  liftST $ readSTRef vd

-- | Set domain of the variable and invoke propagators.
set :: FDDomain v => Var s v -> Domain v -> FD s ()
set (Var vd _ va) d = do
  old <- liftST $ readSTRef vd
  let sd   = Set.size d
  let sold = Set.size old
  if sd < sold
    then do
      liftST $ writeSTRef vd d
      a <- liftST $ readSTRef va
      enqProp a
    else unless (sd == sold) $ do
      pq <- getPropQueue
      error $ "Internal error: tried to enlarge domain: " ++
        show old ++ " -> " ++ show d ++ "\npropQueue:\n" ++ unlines pq

-- | (for debug)
getPropQueue :: FD s [String]
getPropQueue = do
  rpq <- State.gets propQueue
  pq <- liftST $ readSTRef rpq
  return $ map fst $ Queue.toList pq

-- | (for internal)
enqProp :: [(String, Propagator s)] -> FD s ()
enqProp = mapM_ enq where
  enq p@(n, _) = do
    rpq <- State.gets propQueue
    liftST $ modifySTRef rpq $ \pq -> Queue.enq p pq
    traceM' $ "enqProp: " ++ n

-- | (for internal)
execProp :: FD s ()
execProp = do
  rpq <- State.gets propQueue
  q <- liftST $ readSTRef rpq
  unless (Queue.null q) $ do
    let ((n, a), q') = Queue.deq q
    liftST $ writeSTRef rpq q'
    traceM' $ "execProp: > " ++ n
    a
    traceM' $ "execProp: < " ++ n
    execProp

-- | (for debug)
getPropStack :: FD s [String]
getPropStack = do
  rst <- State.gets propStack
  liftST $ readSTRef rst

-- | (for debug)
pushPropStack :: String -> FD s ()
pushPropStack n = do
  rst <- State.gets propStack
  liftST $ modifySTRef rst $ \st -> n:st

-- | (for debug)
popPropStack :: FD s ()
popPropStack = do
  rst <- State.gets propStack
  liftST $ modifySTRef rst $ \(_:st) -> st

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
newC :: ContainerMap c => c Domain -> FD s (c (Var s))
newC = cmapM new

-- | Same as 'new' except to take a Container containing domains.
newCL :: ContainerMap c => c [] -> FD s (c (Var s))
newCL = cmapM newL

-- | Same as 'get' except to return a list as domain.
getL :: FDDomain v => Var s v -> FD s [v]
getL v = liftM Set.toList $ get v

-- | Same as 'get' except to return a Maybe as domain.
getM :: FDDomain v => Var s v -> FD s (Maybe v)
getM v = liftM (listToMaybe . Set.toList) $ get v

-- | Same as 'get' except to return a list as domain in Container.
getCL :: ContainerMap c => c (Var s) -> FD s (c [])
getCL = cmapM getL

-- | Same as 'get' except to return a Maybe as domain in Container.
getCM :: ContainerMap c => c (Var s) -> FD s (c Maybe)
getCM = cmapM getM

-- | Set domain of the variable with singleton value and invoke propagators.
setS :: FDDomain v => Var s v -> v -> FD s ()
setS v val = set v (Set.singleton val)

-- | Same as 'set' except to take a list as domain.
setL :: FDDomain v => Var s v -> [v] -> FD s ()
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
getStack (Var _ vs _) = liftST $ readSTRef vs

__push :: NVar s -> FD s ()
__push (NVar (Var vd vs _)) = do
  d <- liftST $ readSTRef vd
  liftST $ modifySTRef vs $ \ds -> d:ds

__pop :: NVar s -> FD s ()
__pop (NVar (Var vd vs _)) = do
  (d:ds) <- liftST $ readSTRef vs
  liftST $ writeSTRef vd d
  liftST $ writeSTRef vs ds

push :: FD s ()
push = do
  traceM' "push"
  vs <- getVarList
  mapM_ __push vs

pop :: FD s ()
pop = do
  traceM' "pop"
  vs <- getVarList
  mapM_ __pop vs

-- | Label variables specified in Traversable.
labelT :: (FDDomain v, Traversable t) => t (Var s v) -> FD s [t v]
labelT t = labelC' (CTraversable t) (Foldable.toList $ fmap NVar t)

-- | Label variables specified in Container.
labelC :: Container c c' => c (Var s) -> FD s [c']
labelC c = labelC' c (fromContainer NVar c)

labelC' :: Container c c' => c (Var s) -> [NVar s] -> FD s [c']
labelC' c nvs =
  case nvs of
    []        -> do
      c' <- getCL c
      return [cdown head c']
    _ -> do
      (NVar v, nvss) <- deleteFindMin nvs
      d <- getL v
      liftM concat $ forM d $ \i -> do
        push
        setS v i
        s <- labelC' c nvss
        pop
        return s

-- | (for internal)
deleteFindMin :: [NVar s] -> FD s (NVar s, [NVar s])
deleteFindMin nvs = do
  vdss <- forM nvs $ \(NVar (Var vd _ _)) -> liftM Set.size $ liftST $ readSTRef vd
  let smin = minimum vdss
  let (former, latter) = span (\(vds, _) -> vds /= smin) $ zip vdss nvs
  let nvsmin = snd $ head latter
  let cnvs = map snd $ former ++ tail latter
  return (nvsmin, cnvs)

-- Primitives for variable domain propagator

-- | Propagate a domain changing to other domains.
type Propagator s = FD s ()

-- | Add a propagator to the variable
add :: String -> Var s v -> Propagator s -> FD s ()
add n (Var _ _ va) p = do
  liftST $ modifySTRef va $ \as -> (n, p):as
  traceM' $ "add: " ++ n

-- | Add a propagator to the variables and invoke it
add2 :: String -> Var s v1 -> Var s v2 -> Propagator s -> FD s ()
add2 n v1 v2 p = do
  traceM' $ "add2: " ++ n
  add n v1 p
  add n v2 p
  p

-- | Add a propagator to the variables and invoke it
adds :: String -> [Var s v] -> Propagator s -> FD s ()
adds n vs p = do
  traceM' $ "adds: " ++ n
  mapM_ (\v -> add n v p) vs
  p

-- Utilities for variable domain propagator

-- | Domain propagator for arc
type ArcPropagator a b = Domain a -> Domain b -> (Domain a, Domain b)

-- | Create arc constraint from propagator
arcConstraint :: (FDDomain a, FDDomain b) =>
                 String -> ArcPropagator a b -> Var s a -> Var s b -> FD s ()
arcConstraint n c x y = add2 n x y $ do
  dx <- get x
  dy <- get y
  let (dx', dy') =
        if Set.null dx || Set.null dy
        then (Set.empty, Set.empty)
        else c dx dy
  traceM' $ "arcConstraint: " ++ show n ++ ": "
    ++ show dx ++ " -> " ++ show dx' ++ ", "
    ++ show dy ++ " -> " ++ show dy'
  when (Set.size dx < Set.size dx' || Set.size dy < Set.size dy') $
    error $ "arcConstraint: invalid: "
      ++ show dx ++ " -> " ++ show dx' ++ ", "
      ++ show dy ++ " -> " ++ show dy'
  set x dx'
  set y dy'

-- | Domain propagator for multiple-arc
type MultiPropagator v = [Domain v] -> [Domain v]

-- | Create multiple-arc constraint from propagator
multiConstraint :: FDDomain v =>
                   String -> MultiPropagator v -> [Var s v] -> FD s ()
multiConstraint n c vs = adds n vs $ do
  ds <- mapM get vs
  let ds' =
        if any Set.null ds
        then map (const Set.empty) ds
        else c ds
  traceM' $ "multiConstraint: " ++ show n ++ ": "
    ++ show ds ++ " -> " ++ show ds'
  when (any (\(d, d') -> Set.size d < Set.size d') $ zip ds ds') $
    error $ "multiConstraint: invalid: " ++ show ds ++ " -> " ++ show ds'
  (`mapM_` zip vs ds') $ uncurry set

-- Primitive constraints

-- | Equality constraint
eq :: FDDomain v => Var s v -> Var s v -> FD s ()
eq = arcConstraint "eq" eqConstraint

eqConstraint :: FDDomain v => ArcPropagator v v
eqConstraint vx vy = (vz, vz) where
  vz = vx `Set.intersection` vy

-- | Inequality (<=) constraint
le :: FDDomain v => Var s v -> Var s v -> FD s ()
le = arcConstraint "le" leConstraint

leConstraint :: FDDomain v => ArcPropagator v v
leConstraint vx vy = (vx', vy') where
  minX = Set.findMin vx
  maxY = Set.findMax vy
  vx' = Set.filter (<= maxY) vx
  vy' = Set.filter (>= minX) vy

-- | Inequality (/=) constraint
neq :: FDDomain v => Var s v -> Var s v -> FD s ()
neq = arcConstraint "neq" neqConstraint

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
alldiff :: FDDomain v => [Var s v] -> FD s ()
alldiff []     = return ()
alldiff (v:vs) = do
  mapM_ (v `neq`) vs
  alldiff vs

-- | Differ from each other in Foldable
alldiffF :: (FDDomain v, Foldable f) => f (Var s v) ->FD s ()
alldiffF = alldiff . Foldable.toList

-- | x == y (mod m)
eqmod :: (FDDomain v, Integral v) => v -> Var s v -> Var s v -> FD s ()
eqmod m = arcConstraint "eqmod" (eqmodConstraint m)

eqmodConstraint :: Integral v => v -> ArcPropagator v v
eqmodConstraint m vx vy = (vx', vy') where
  vmz = Set.map (`mod` m) vx `Set.intersection` Set.map (`mod` m) vy
  vx' = Set.filter (\e -> (e `mod` m) `Set.member` vmz) vx
  vy' = Set.filter (\e -> (e `mod` m) `Set.member` vmz) vy

-- | x /= y (mod m)
neqmod :: (FDDomain v, Integral v) => v -> Var s v -> Var s v -> FD s ()
neqmod m = arcConstraint "neqmod" (neqmodConstraint m)

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
add' :: (FDDomain v, Num v) => v -> Var s v -> Var s v -> FD s ()
add' c = arcConstraint "add'" (addConstraint c)

addConstraint :: (Eq v, Num v) => v -> ArcPropagator v v
addConstraint c vx vy = (vx', vy') where
  vx' = Set.filter (\ix -> any (\iy -> ix+iy==c) $ Set.toList vy) vx
  vy' = Set.filter (\iy -> any (\ix -> ix+iy==c) $ Set.toList vx) vy

-- | add3 z x y means z = x + y
add3 :: (FDDomain v, Num v) => Var s v -> Var s v -> Var s v -> FD s ()
add3 z x y = multiConstraint "add3" add3Constraint [x, y, z]

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
sub :: (FDDomain v, Num v) => v -> Var s v -> Var s v -> FD s ()
sub c = arcConstraint "sub" (subConstraint c)

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
