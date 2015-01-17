-- | Fuzzy Constraint Satisfaction Problem Solver

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE UndecidableInstances       #-}

module Control.CPFD.Fuzzy
       (
       -- * Monads
         FD, FDState
       , runFD, runFD'
       -- * Variables and Domains
       , FDValue
       , Domain
       , Var
       , Container, ContainerMap (..), ContainerLift (..)
       , CTraversable (..)
       , new, newL, newN, newNL, newT, newTL, newC, newCL
       , set, setS, setL, get, getL
       -- * Constraint Store
       , ArcPropRule, ArcConstraint, arcConstraint
       , MultiPropRule, MultiConstraint, multiConstraint
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
       -- * Fuzzy related (for experimental)
       , arcCons
       ) where

import           Control.Applicative   (Applicative, WrappedMonad (..), (<$>),
                                        (<*>))
import           Control.Monad         (forM, liftM, replicateM, unless, when)
import           Control.Monad.ST.Lazy (ST, runST)
import           Control.Monad.State   (StateT, evalStateT)
import qualified Control.Monad.State   as State
import           Control.Monad.Trans   (lift)
import           Control.Monad.Writer  (WriterT, runWriterT)
import qualified Control.Monad.Writer  as Writer
import           Data.Foldable         (Foldable)
import qualified Data.Foldable         as Foldable
import           Data.List             (foldl')
import           Data.Maybe            (listToMaybe)
import           Data.STRef.Lazy       (STRef)
import qualified Data.STRef.Lazy       as STRef
import           Data.Traversable      (Traversable)
import qualified Data.Traversable      as Traversable
import           Debug.Trace           (traceM)

import           Control.CPFD.Domain         (Domain, FDValue)
import qualified Control.CPFD.Domain         as Domain
import           Control.CPFD.Internal.Queue (Queue)
import qualified Control.CPFD.Internal.Queue as Queue
import           Data.Fuzzy

-- | Monad for constraints on finite domain
newtype FD s a =
  FD { unFD :: WriterT [String] (StateT (FDState s) (ST s)) a }
  deriving (Functor, Applicative, Monad)

-- | (for internal use)
liftST :: ST s a -> FD s a
liftST = FD . lift . lift

-- | (for internal use)
newSTRef :: a -> FD s (STRef s a)
newSTRef = liftST . STRef.newSTRef

-- | (for internal use)
readSTRef :: STRef s a -> FD s a
readSTRef = liftST . STRef.readSTRef

-- | (for internal use)
writeSTRef :: STRef s a -> a -> FD s ()
writeSTRef r a = liftST $ STRef.writeSTRef r a

-- | (for internal use)
modifySTRef :: STRef s a -> (a -> a) -> FD s ()
modifySTRef r f = liftST $ STRef.modifySTRef r f

-- | (for internal use)
liftState :: StateT (FDState s) (ST s) a -> FD s a
liftState = FD . lift

-- | (for internal use)
put :: FDState s -> FD s ()
put = liftState . State.put

-- | (for internal use)
gets :: (FDState s -> a) -> FD s a
gets = liftState . State.gets

-- | (for internal use)
liftWriter :: WriterT [String] (StateT (FDState s) (ST s)) a -> FD s a
liftWriter = FD

traceFD :: String -> FD s ()
traceFD s = liftWriter $ Writer.tell [s]

-- | (for internal use)
data FDState s =
  FDState
  { varList   :: VarList s
  , lastVarId :: STRef s Int
  , propQueue :: STRef s (Queue (Propagator s))
  , propStack :: STRef s [String]
  , traceFlag :: Bool }

-- | Run FD monad
runFD :: (forall s. FD s a) -> a
runFD fd = fst $ runST $ flip evalStateT undefined $ runWriterT $ unFD $ fdWrapper False fd

-- | Run FD monad with trace for debug
runFD' :: (forall s. FD s a) -> (a, [String])
runFD' fd = runST $ flip evalStateT undefined $ runWriterT $ unFD $ fdWrapper True fd

-- | (for internal use)
fdWrapper :: Bool -> FD s a -> FD s a
fdWrapper tf fd = do
  vl <- newVarList
  rvi <- newSTRef 0
  rpq <- newSTRef Queue.empty
  rst <- newSTRef []
  put FDState { varList = vl
              , lastVarId = rvi
              , propQueue = rpq
              , propStack = rst
              , traceFlag = tf }
  traceFD "Initialized."
  a <- fd
  traceFD "Terminated."
  return a

-- | Propagate a domain changing to other domains.
data VarPropagator s =
  VarPropagator
  { vpName   :: String
  , vpVars   :: [NVar s]
  , vpAction :: FD s () }

-- | Propagate the specified domain changing to other domains.
data Propagator s =
  Propagator
  { propVar  :: NVar s
  , propProp :: VarPropagator s }

-- | Finite domain variable
data Var s v =
  Var
  { varId     :: Int
  , varDomain :: STRef s (Domain v)
  , varStack  :: STRef s [Domain v]
  , varProp   :: STRef s [VarPropagator s] }

instance Show (Var s v) where
  show v = "_" ++ show (varId v)

-- | (for internal use in variable list)
data NVar s = forall v. FDValue v => NVar (Var s v)

instance Show (NVar s) where
  show = showNVar'

class ContainerMap c where
  cmapA :: Applicative f =>
           (forall a. FDValue a => t a -> f (t' a)) -> c t -> f (c t')
  cmapM :: Monad m =>
           (forall a. FDValue a => t a -> m (t' a)) -> c t -> m (c t')
  cmapM f = unwrapMonad . cmapA (WrapMonad . f)
  fromContainer :: (forall a. FDValue a => t a -> t') -> c t -> [t']

class ContainerLift c c' where
  cup :: (forall a. a -> t a) -> c' -> c t
  cdown :: (forall a. t a -> a) -> c t -> c'

-- | Container to hold data (variable domain, reference,
-- assignment, etc.) related to variables.
class (ContainerMap c, ContainerLift c c') => Container c c'

-- | (for internal use)
newtype CTraversable t' v t =
  CTraversable { unCTraversable :: t' (t v) } deriving (Eq, Show)

instance (FDValue v, Traversable t') =>
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
newVarList = newSTRef []

getVarList :: FD s [NVar s]
getVarList = do
  vl <- gets varList
  readSTRef vl

-- | (for debug)
showNVar :: NVar s -> FD s String
showNVar (NVar v) = do
  d <- readSTRef (varDomain v)
  s <- readSTRef (varStack v)
  return $ show (varId v, d, s)

-- | (for debug)
showNVar' :: NVar s -> String
showNVar' (NVar v) = "_" ++ show (varId v)

-- | (for debug)
traceM' :: String -> FD s ()
traceM' s = do
  f <- gets traceFlag
  when f $ traceM s

-- Primitives for variable domain

-- | Create a new variable with domain.
new :: FDValue v => Domain v -> FD s (Var s v)
new d = do
  vl <- gets varList
  vi <- newVarId
  vd <- newSTRef d
  vs <- newSTRef []
  vp <- newSTRef []
  let v = Var { varId = vi, varDomain = vd, varStack = vs, varProp = vp }
  modifySTRef vl $ \nvs -> NVar v : nvs
  return v

-- | (for internal)
newVarId :: FD s Int
newVarId = do
  rvi <- gets lastVarId
  vi <- readSTRef rvi
  let vi' = vi + 1
  writeSTRef rvi vi'
  return vi'

-- | Get domain of the variable.
get :: Var s v -> FD s (Domain v)
get v = do
  execProp
  readSTRef (varDomain v)

-- | Set domain of the variable and invoke propagators.
set :: FDValue v => Var s v -> Domain v -> FD s ()
set v d = do
  let vd = varDomain v
  let vp = varProp v
  old <- readSTRef vd
  let sd   = Domain.size d
  let sold = Domain.size old
  if sd < sold
    then do
      writeSTRef vd d
      p <- readSTRef vp
      enqProp v p
    else unless (sd == sold) $ do
      pq <- getPropQueue
      error $ "Internal error: tried to enlarge domain: " ++
        show old ++ " -> " ++ show d ++ "\npropQueue:\n" ++ unlines pq

-- | (for debug)
getPropQueue :: FD s [String]
getPropQueue = do
  rpq <- gets propQueue
  pq <- readSTRef rpq
  return $ map (vpName . propProp) $ Queue.toList pq

-- | (for internal)
enqProp :: FDValue v => Var s v -> [VarPropagator s] -> FD s ()
enqProp v = mapM_ enq where
  enq vp = do
    rpq <- gets propQueue
    let nv = NVar v
    let p = Propagator { propVar = nv, propProp = vp }
    modifySTRef rpq $ \pq -> Queue.enq p pq
    traceM' $ "enqProp: " ++ show v ++ " -> " ++ vpName vp ++ show (vpVars vp)

-- | (for internal)
execProp :: FD s ()
execProp = do
  rpq <- gets propQueue
  q <- readSTRef rpq
  unless (Queue.null q) $ do
    let (p, q') = Queue.deq q
    let v  = propVar  p
    let vp = propProp p
    writeSTRef rpq q'
    traceM' $ "execProp: > " ++ show v ++ " -> " ++ vpName vp ++ show (vpVars vp)
    vpAction vp
    traceM' $ "execProp: < " ++ show v ++ " -> " ++ vpName vp ++ show (vpVars vp)
    execProp

-- | (for debug)
getPropStack :: FD s [String]
getPropStack = do
  rst <- gets propStack
  readSTRef rst

-- | (for debug)
pushPropStack :: String -> FD s ()
pushPropStack n = do
  rst <- gets propStack
  modifySTRef rst $ \st -> n:st

-- | (for debug)
popPropStack :: FD s ()
popPropStack = do
  rst <- gets propStack
  modifySTRef rst $ \(_:st) -> st

-- Utilities for variable domain

-- | Same as 'new' except to take a list as domain.
newL :: FDValue v => [v] -> FD s (Var s v)
newL d = new (Domain.fromList d)

-- | Same as 'new' except to take a number of variables to create.
newN :: FDValue v => Int -> Domain v -> FD s [Var s v]
newN n d = replicateM n (new d)

-- | Same as 'newN' except to take a list as domain.
newNL :: FDValue v => Int -> [v] -> FD s [Var s v]
newNL n d = replicateM n (newL d)

-- | Same as 'new' except to take a Traversable containing domains.
newT :: (FDValue v, Traversable t) => t (Domain v) -> FD s (t (Var s v))
newT = Traversable.mapM new

-- | Same as 'new' except to take a Traversable containing lists as domains.
newTL :: (FDValue v, Traversable t) => t [v] -> FD s (t (Var s v))
newTL = Traversable.mapM newL

-- | Same as 'new' except to take a Container containing domains.
newC :: ContainerMap c => c Domain -> FD s (c (Var s))
newC = cmapM new

-- | Same as 'new' except to take a Container containing domains.
newCL :: ContainerMap c => c [] -> FD s (c (Var s))
newCL = cmapM newL

-- | Same as 'get' except to return a list as domain.
getL :: FDValue v => Var s v -> FD s [v]
getL v = Domain.toList <$> get v

-- | Same as 'get' except to return a Maybe as domain.
getM :: FDValue v => Var s v -> FD s (Maybe v)
getM v = (listToMaybe . Domain.toList) <$> get v

-- | Same as 'get' except to return a list as domain in Container.
getCL :: ContainerMap c => c (Var s) -> FD s (c [])
getCL = cmapM getL

-- | Same as 'get' except to return a Maybe as domain in Container.
getCM :: ContainerMap c => c (Var s) -> FD s (c Maybe)
getCM = cmapM getM

-- | Set domain of the variable with singleton value and invoke propagators.
setS :: FDValue v => Var s v -> v -> FD s ()
setS v val = set v (Domain.singleton val)

-- | Same as 'set' except to take a list as domain.
setL :: FDValue v => Var s v -> [v] -> FD s ()
setL v d = set v (Domain.fromList d)

-- Labeling

-- | (for debug)
getStack :: Var s v -> FD s [Domain v]
getStack v = readSTRef (varStack v)

__push :: NVar s -> FD s ()
__push (NVar v) = do
  d <- readSTRef (varDomain v)
  modifySTRef (varStack v) $ \ds -> d:ds

__pop :: NVar s -> FD s ()
__pop (NVar v) = do
  (d:ds) <- readSTRef (varStack v)
  writeSTRef (varDomain v) d
  writeSTRef (varStack v) ds

push :: FD s ()
push = do
  traceM' "{ -- push"
  vs <- getVarList
  mapM_ __push vs

pop :: FD s ()
pop = do
  traceM' "} -- pop"
  vs <- getVarList
  mapM_ __pop vs

-- | Label variables specified in Traversable.
labelT :: (FDValue v, Traversable t) => t (Var s v) -> FD s [t v]
labelT t = labelC' (CTraversable t) (Foldable.toList $ fmap NVar t)

-- | Label variables specified in Container.
labelC :: Container c c' => c (Var s) -> FD s [c']
labelC c = labelC' c (fromContainer NVar c)

labelC' :: Container c c' => c (Var s) -> [NVar s] -> FD s [c']
labelC' c nvs =
  case nvs of
    [] -> do
      c' <- getCL c
      return [cdown head c']
    _ -> do
      (NVar v, nvss) <- deleteFindMin nvs
      d <- getL v
      liftM concat $ forM d $ \i -> do
        push
        traceM' $ "labelC': " ++ show v ++ "=" ++ show i
        setS v i
        s <- labelC' c nvss
        pop
        return s

-- | (for internal)
deleteFindMin :: [NVar s] -> FD s (NVar s, [NVar s])
deleteFindMin nvs = do
  vdss <- forM nvs $
          \(NVar v) -> Domain.size <$> readSTRef (varDomain v)
  let smin = minimum vdss
  let (former, latter) = span (\(vds, _) -> vds /= smin) $ zip vdss nvs
  let nvsmin = snd $ head latter
  let cnvs = map snd $ former ++ tail latter
  return (nvsmin, cnvs)

-- Primitives for variable domain propagator

-- | Add a propagator to the variable
add :: Var s v -> VarPropagator s -> FD s ()
add v p = modifySTRef (varProp v) $ \ps -> p:ps

-- | Add a propagator to the variables and invoke it
add2 :: (FDValue v1, FDValue v2) =>
        String -> Var s v1 -> Var s v2 -> FD s () -> FD s ()
add2 n v1 v2 a = do
  traceM' $ "add2: " ++ n ++ " " ++ show (v1, v2)
  let vp = VarPropagator { vpName = n, vpVars = [NVar v1, NVar v2], vpAction = a }
  add v1 vp
  add v2 vp
  a

-- | Add a propagator to the variables and invoke it
adds :: FDValue v => String -> [Var s v] -> FD s () -> FD s ()
adds n vs a = do
  traceM' $ "adds: " ++ n ++ " " ++ show vs
  let vp = VarPropagator { vpName = n, vpVars = map NVar vs, vpAction = a}
  mapM_ (`add` vp) vs
  a

-- Utilities for variable domain propagator

-- | Domain propagator for arc
type ArcPropRule a b = Domain a -> Domain b -> (Domain a, Domain b)

type ArcConstraint s a b = Var s a -> Var s b -> FD s ()

-- | Create arc constraint from propagator
arcConstraint :: (FDValue a, FDValue b) =>
                 String -> ArcPropRule a b -> ArcConstraint s a b
arcConstraint n c x y = add2 n x y $ do
  dx <- get x
  dy <- get y
  let (dx', dy') =
        if Domain.null dx || Domain.null dy
        then (Domain.empty, Domain.empty)
        else c dx dy
  traceM' $ "arcConstraint: " ++ n ++ show (x, y) ++ ": "
    ++ show dx ++ " -> " ++ show dx' ++ ", "
    ++ show dy ++ " -> " ++ show dy'
  when (Domain.size dx < Domain.size dx' || Domain.size dy < Domain.size dy') $
    error $ "arcConstraint: invalid: "
      ++ show dx ++ " -> " ++ show dx' ++ ", "
      ++ show dy ++ " -> " ++ show dy'
  set x dx'
  set y dy'

-- | Domain propagator for multiple-arc
type MultiPropRule v = [Domain v] -> [Domain v]

type MultiConstraint s v = [Var s v] -> FD s ()

-- | Create hyper-arc constraint from propagator
multiConstraint :: FDValue v =>
                   String -> MultiPropRule v -> MultiConstraint s v
multiConstraint n c vs = adds n vs $ do
  ds <- mapM get vs
  let ds' =
        if any Domain.null ds
        then map (const Domain.empty) ds
        else c ds
  traceM' $ "multiConstraint: " ++ n ++ show vs ++  ": "
    ++ show ds ++ " -> " ++ show ds'
  when (any (\(d, d') -> Domain.size d < Domain.size d') $ zip ds ds') $
    error $ "multiConstraint: invalid: " ++ show ds ++ " -> " ++ show ds'
  (`mapM_` zip vs ds') $ uncurry set

-- | General arc constraint
cGeneralArc :: (FDValue a, FDValue b) =>
               String -> (a -> b -> Bool) -> ArcConstraint s a b
cGeneralArc n p = arcConstraint n (pGeneralArc p)

pGeneralArc :: (FDValue a, FDValue b) => (a -> b -> Bool) -> ArcPropRule a b
pGeneralArc p dx dy = (dx', dy') where
  dx' = Domain.filter (\x -> any (x `p`) (Domain.toList dy)) dx
  dy' = Domain.filter (\y -> any (`p` y) (Domain.toList dx)) dy

-- Primitive constraints

-- | Equality constraint
eq :: FDValue v => Var s v -> Var s v -> FD s ()
eq = arcConstraint "eq" eqConstraint

eqConstraint :: FDValue v => ArcPropRule v v
eqConstraint vx vy = (vz, vz) where
  vz = vx `Domain.intersection` vy

-- | Inequality (<=) constraint
le :: FDValue v => Var s v -> Var s v -> FD s ()
le = arcConstraint "le" leConstraint

leConstraint :: FDValue v => ArcPropRule v v
leConstraint vx vy = (vx', vy') where
  minX = Domain.findMin vx
  maxY = Domain.findMax vy
  vx' = Domain.filter (<= maxY) vx
  vy' = Domain.filter (>= minX) vy

-- | Inequality (/=) constraint
neq :: FDValue v => Var s v -> Var s v -> FD s ()
neq = arcConstraint "neq" neqConstraint

neqConstraint :: FDValue v => ArcPropRule v v
neqConstraint vx vy
  | Domain.single vx && Domain.single vy =
    if vx == vy
    then (Domain.empty, Domain.empty)
    else (vx, vy)
  | Domain.single vx && vx `Domain.isProperSubsetOf` vy = (vx, vy Domain.\\ vx)
  | Domain.single vy && vy `Domain.isProperSubsetOf` vx = (vx Domain.\\ vy, vy)
  | otherwise = (vx, vy)

-- | Differ from each other in list
alldiff :: FDValue v => [Var s v] -> FD s ()
alldiff []     = return ()
alldiff (v:vs) = do
  mapM_ (v `neq`) vs
  alldiff vs

-- | Differ from each other in Foldable
alldiffF :: (FDValue v, Foldable f) => f (Var s v) ->FD s ()
alldiffF = alldiff . Foldable.toList

-- | x == y (mod m)
eqmod :: (FDValue v, Integral v) => v -> Var s v -> Var s v -> FD s ()
eqmod m = arcConstraint "eqmod" (eqmodConstraint m)

eqmodConstraint :: Integral v => v -> ArcPropRule v v
eqmodConstraint m vx vy = (vx', vy') where
  vmz = Domain.map (`mod` m) vx `Domain.intersection` Domain.map (`mod` m) vy
  vx' = Domain.filter (\e -> (e `mod` m) `Domain.member` vmz) vx
  vy' = Domain.filter (\e -> (e `mod` m) `Domain.member` vmz) vy

-- | x /= y (mod m)
neqmod :: (FDValue v, Integral v) => v -> Var s v -> Var s v -> FD s ()
neqmod m = arcConstraint "neqmod" (neqmodConstraint m)

neqmodConstraint :: Integral v => v -> ArcPropRule v v
neqmodConstraint m vx vy = (vx'', vy'') where
  vmx = Domain.map (`mod` m) vx
  vmy = Domain.map (`mod` m) vy
  vy' = Domain.filter (\e -> (e `mod` m) `Domain.notMember` vmx) vy
  vx' = Domain.filter (\e -> (e `mod` m) `Domain.notMember` vmy) vx
  (vx'', vy'')
    | Domain.single vmx && Domain.single vmy =
      if vmx == vmy
      then (Domain.empty, Domain.empty)
      else (vx, vy)
    | Domain.single vmx && vmx `Domain.isProperSubsetOf` vmy = (vx, vy')
    | Domain.single vmy && vmy `Domain.isProperSubsetOf` vmx = (vx', vy)
    | otherwise = (vx, vy)

-- | Differ from each other in list (mod m)
alldiffmod :: (FDValue v, Integral v) => v -> [Var s v] -> FD s ()
alldiffmod _ []     = return ()
alldiffmod m (v:vs) = do
  mapM_ (neqmod m v) vs
  alldiffmod m vs

-- | add' c x y means c = x + y (c is constant value)
add' :: (FDValue v, Num v) => v -> Var s v -> Var s v -> FD s ()
add' c = arcConstraint "add'" (addConstraint c)

addConstraint :: (Eq v, Num v) => v -> ArcPropRule v v
addConstraint c vx vy = (vx', vy') where
  vx' = Domain.filter (\ix -> any (\iy -> ix+iy==c) $ Domain.toList vy) vx
  vy' = Domain.filter (\iy -> any (\ix -> ix+iy==c) $ Domain.toList vx) vy

-- | add3 z x y means z = x + y
add3 :: (FDValue v, Num v) => Var s v -> Var s v -> Var s v -> FD s ()
add3 z x y = multiConstraint "add3" add3Constraint [x, y, z]

add3Constraint :: (Ord a, Num a) => MultiPropRule a
add3Constraint [vx, vy, vz] = [vx', vy', vz'] where
  minZ = Domain.findMin vx + Domain.findMin vy
  maxZ = Domain.findMax vx + Domain.findMax vy
  vz' = Domain.filter (\e -> minZ <= e && e <= maxZ) vz
  --
  minX = Domain.findMin vz - Domain.findMax vy
  maxX = Domain.findMax vz - Domain.findMin vy
  vx' = Domain.filter (\e -> minX <= e && e <= maxX) vx
  --
  minY = Domain.findMin vz - Domain.findMax vx
  maxY = Domain.findMax vz - Domain.findMin vx
  vy' = Domain.filter (\e -> minY <= e && e <= maxY) vy

-- | sub c x y means x - y == c (c is constant value)
sub :: (FDValue v, Num v) => v -> Var s v -> Var s v -> FD s ()
sub c = arcConstraint "sub" (subConstraint c)

subConstraint :: (Eq a, Num a) => a -> ArcPropRule a a
subConstraint c vx vy = (vx', vy') where
  vx' = Domain.filter (\ix -> any (\iy -> ix==iy+c) $ Domain.toList vy) vx
  vy' = Domain.filter (\iy -> any (\ix -> ix==iy+c) $ Domain.toList vx) vy

-- Fuzzy related definitions

revise :: (Fuzzy (r (a, b) g), FSet r,
           Fuzzy (s a g), Fuzzy (s b g), FSet s, FSetUpdate s,
           FValue a, FValue b, Grade g) =>
           r (a, b) g -> s a g -> s b g -> g -> (g, Bool, s a g)
revise r x1 x2 sup = (sup', changed, x1') where
  sup' = sup ?& height
  (changed, height, x1') = foldArc (revise0 r x2) (False, minBound, x1) x1 x2

revise0 :: (Fuzzy (r (a, b) g), FSet r,
            Fuzzy (s a g), Fuzzy (s b g), FSet s, FSetUpdate s,
            FValue a, FValue b, Grade g) =>
           r (a, b) g -> s b g -> (Bool, g, s a g) -> (a, b) ->
           (Bool, g, s a g)
-- revise0 r x2 (ch, h, x1) (d1, d2)
--   | traceShow ("revise0", ((d1, d2), h)) False = undefined
revise0 r x2 (ch, h, x1) (d1, d2) = (ch', h', x1') where
  nd = arcCons r x1 x2 d1 d2
  h' = nd ?| h
  (ch', x1') =
    if nd /= mu x1 d1
    then (True, update x1 d1 nd)
    else (ch,   x1)

foldArc :: (Fuzzy (s a g), FSet s, Ord a, Ord b, Grade g) =>
           (c -> (a, b) -> c) -> c -> s a g -> s b g -> c
foldArc f c x1 x2 = foldl' g c (support x1) where
  g c' d1 = foldl' (\c'' d2 -> f c'' (d1, d2)) c' (support x2)

-- | Degree of consistency
arcCons :: (Fuzzy (r (a, b) g), FSet r,
            Fuzzy (s a g), Fuzzy (s b g), FSet s,
            Ord a, Ord b, Grade g) =>
           r (a, b) g -> s a g -> s b g -> a -> b -> g
arcCons r x1 x2 d1 d2 = mu x1 d1 ?& mu r (d1, d2) ?& mu x2 d2


-- Internal Tests

{-|
>>> testL
([1,2,3,4,5,6,7,8,9,10],[1,2,3,4,5])
-}
testL :: ([Int], [Int])
testL = runFD $ do
  v <- newL [1..10]
  val <- getL v
  setL v [1..5]
  val' <- getL v
  return (val, val')

{-|
>>> testTLProp
([5,7,9],[5,7,9])
-}
testTLProp :: ([Int], [Int])
testTLProp = runFD $ do
  [x, y] <- newTL [[1,3..11], [5..10]]
  x `eq` y
  dx <- getL x
  dy <- getL y
  return (dx, dy)

{-|
>>> testAlldiff
([1,3,7,9,11],[6,7,8,9,10],[5])
-}
testAlldiff :: ([Int], [Int], [Int])
testAlldiff = runFD $ do
  [x, y, z] <- newTL [[1,3..11], [5..10], [5]]
  alldiff [x, y, z]
  dx <- getL x
  dy <- getL y
  dz <- getL z
  return (dx, dy, dz)

{-|
>>> testProp
([5,7,9],[5,7,9])
-}
testProp :: ([Int], [Int])
testProp = runFD $ do
  x <- newL [1,3..11]
  y <- newL [5..10]
  x `eq` y
  dx <- getL x
  dy <- getL y
  return (dx, dy)
