-- | Fuzzy Constraint Satisfaction Problem Solver

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}

module Control.CPFD.Fuzzy.Solver2
       (
       -- * Monads
         FD, FDState
       , runFD, runFD', runFD''
       -- * Variables and Domains
       , Grade, RGrade, Domain, FDValue, Var
       , Container, ContainerMap (..), ContainerLift (..)
       , CTraversable (..)
       , new, newL, newN, newNL, newT, newTL, newCL
       , set, setS, setL, get, getL
       -- * Constraint Store
       , add1, add2, addN
       -- * Labelling
       , labelT, labelC
       -- * Optmization
       , optimizeT, optimizeC
       , optimizeAllT, optimizeAllC
       -- * (for debug)
       , revise, arcCons
       ) where

import           Control.Applicative   (Applicative, (<$>))
import           Control.Monad         (foldM, forM, replicateM, unless, when)
import           Control.Monad.ST.Lazy (ST, runST)
import           Control.Monad.State   (StateT, evalStateT)
import qualified Control.Monad.State   as State
import           Control.Monad.Trans   (lift)
import           Control.Monad.Writer  (WriterT, runWriterT)
import qualified Control.Monad.Writer  as Writer
import qualified Data.Foldable         as Foldable
import           Data.List             (foldl')
import           Data.Maybe            (fromMaybe, listToMaybe)
import           Data.STRef.Lazy       (STRef)
import qualified Data.STRef.Lazy       as STRef
import           Data.Traversable      (Traversable)
import qualified Data.Traversable      as Traversable
import           Debug.Trace           (traceM)

import Control.Lens

import           Control.CPFD.Internal.Queue (Queue)
import qualified Control.CPFD.Internal.Queue as Queue
import           Data.Container
import           Data.Fuzzy                  ((?&), (?|))
import           Data.Fuzzy                  (FR, FR1, FR2, FRN, FS, FSet,
                                              FSetUpdate, FValue, Fuzzy, Grade,
                                              RGrade)
import qualified Data.Fuzzy                  as Fuzzy

-- | Monad for constraints on finite domain
newtype FD s a =
  FD { unFD :: WriterT [String] (StateT (FDState s) (ST s)) a }
  deriving (Functor, Applicative, Monad)

instance Show (FD s a) where
  show _ = "<FD>"

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
  , propStack :: STRef s [String]               -- ^ for trace of backtracking
  , fdCons    :: STRef s [Constraint s]
  , traceFlag :: Bool                           -- ^ switch for all the traces
  }

-- | Run FD monad
runFD :: (forall s. FD s a) -> a
runFD fd = fst $ runST $ flip evalStateT undefined $ runWriterT $ unFD $ fdWrapper False fd

-- | Run FD monad with trace for debug
runFD' :: (forall s. FD s a) -> a
runFD' fd = fst $ runST $ flip evalStateT undefined $ runWriterT $ unFD $ fdWrapper True fd

-- | Run FD monad with trace for debug
runFD'' :: (forall s. FD s a) -> (a, [String])
runFD'' fd = runST $ flip evalStateT undefined $ runWriterT $ unFD $ fdWrapper True fd

-- | (for internal use)
fdWrapper :: Bool -> FD s a -> FD s a
fdWrapper tf fd = do
  vl  <- newVarList
  rvi <- newSTRef 0
  rpq <- newSTRef Queue.empty
  rst <- newSTRef []
  rc  <- newSTRef []
  put FDState { varList = vl
              , lastVarId = rvi
              , propQueue = rpq
              , propStack = rst
              , fdCons    = rc
              , traceFlag = tf }
  traceFD "Initialized."
  a <- fd
  traceFD "Terminated."
  return a

-- | Propagate a domain changing to others.
data VarPropagator s =
  VarPropagator
  { vpName   :: String
  , vpVars   :: [NVar s]
  , vpAction :: FD s () }
  deriving (Show)

-- | Queue elements for propagating the specified domain changing to others.
data Propagator s =
  Propagator
  { propVar  :: NVar s
  , propProp :: VarPropagator s }
  deriving (Show)

-- | Finite domain variable
data Var s v =
  Var
  { varId     :: Int
  , varDomain :: STRef s (Domain v)
  , varStack  :: STRef s [Domain v]
  , varProp   :: STRef s [VarPropagator s] }

type Domain v = FS v RGrade
type FDValue v = Fuzzy.FValue v

instance Show (Var s v) where
  show v = "_" ++ show (varId v)

-- | (for internal use in variable list)
data NVar s = forall v. FDValue v => NVar (Var s v)

instance Show (NVar s) where
  show = showNVar'

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

data Constraint s =
  Constraint
  { consName  :: String        -- ^ for debug
  , consVars  :: [NVar s]      -- ^ for debug
  , consGrade :: FD s RGrade
  } deriving (Show)

getCons :: FD s [Constraint s]
getCons = do
  rc <- gets fdCons
  readSTRef rc

addCons :: Constraint s -> FD s ()
addCons c = do
  rc <- gets fdCons
  modifySTRef rc $ \cs -> c : cs

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
setV :: FDValue v => Var s v -> Domain v -> FD s ()
setV v d = do
  writeSTRef (varDomain v) d
  p <- readSTRef (varProp v)
  enqProp v p

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
newL d = new (Fuzzy.fromCoreList d)

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

{-
-- | Same as 'new' except to take a Container containing domains.
newC :: ContainerMap c => c Domain -> FD s (c (Var s))
newC = cmapM new
-}

-- | Same as 'new' except to take a Container containing domains.
newCL :: ContainerMap c => c [] -> FD s (c (Var s))
newCL = cmapM newL

-- | Same as 'get' except to return a list as domain.
getL :: FDValue v => Var s v -> FD s [v]
getL v = Fuzzy.support <$> get v

-- | Same as 'get' except to return a Maybe as domain.
getM :: FDValue v => Var s v -> FD s (Maybe v)
getM v = (listToMaybe . Fuzzy.support) <$> get v

-- | Same as 'get' except to return a list as domain in Container.
getCL :: ContainerMap c => c (Var s) -> FD s (c [])
getCL = cmapM getL

-- | Same as 'get' except to return a Maybe as domain in Container.
getCM :: ContainerMap c => c (Var s) -> FD s (c Maybe)
getCM = cmapM getM

-- | Set domain of the variable with singleton value and invoke propagators.
setS :: FDValue v => Var s v -> v -> FD s ()
setS v val = setV v (Fuzzy.fromCoreList [val])

-- | Same as 'set' except to take a list as domain.
setL :: FDValue v => Var s v -> [v] -> FD s ()
setL v d = setV v (Fuzzy.fromCoreList d)

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
labelT :: (FDValue v, Traversable t) => t (Var s v) -> FD s [(t v, RGrade)]
labelT t = labelC' (CTraversable t) (Foldable.toList $ fmap NVar t)

-- | Label variables specified in Container.
labelC :: Container c c' => c (Var s) -> FD s [(c', RGrade)]
labelC c = labelC' c (fromContainer NVar c)

labelC' :: Container c c' => c (Var s) -> [NVar s] -> FD s [(c', RGrade)]
labelC' c nvs =
  case nvs of
    [] -> do
      c' <- getCL c
      g <- getConsDeg
      let c'' = cdown head c'
      return [(c'', g)]
    _ -> do
      (NVar v, nvss) <- deleteFindMin nvs
      d <- getL v
      flip (`foldM` []) d $ \ss i -> do
        push
        traceM' $ "labelC': " ++ show v ++ "=" ++ show i
        setS v i
        s <- labelC' c nvss
        pop
        return (ss ++ s)

type BestSolution a = (Maybe a, RGrade, RGrade)
initBestSolution :: BestSolution a
initBestSolution = (Nothing, minBound, maxBound)

-- | Optimize variables specified in 'Traversable'.
optimizeT :: (FDValue v, Traversable t)
          => t (Var s v) -> FD s (Maybe (t v), RGrade)
optimizeT t = do
  (_, (best, g, _)) <-
    optimizeC' (CTraversable t) (Foldable.toList $ fmap NVar t) initBestSolution
  return (best, g)

-- | Optimize variables specified in 'Container'.
optimizeC :: Container c c' => c (Var s) -> FD s (Maybe c', RGrade)
optimizeC c = do
  (_, (best, g, _)) <-
    optimizeC' c (fromContainer NVar c) initBestSolution
  return (best, g)

optimizeC' :: Container c c'
           => c (Var s) -> [NVar s] -> BestSolution c'
           -> FD s ([(c', RGrade)], BestSolution c')
optimizeC' c nvs b@(_, bInf, bSup) =
  case nvs of
    [] -> do
      c' <- getCL c
      g <- getConsDeg
      let c'' = cdown head c'
      let (best', bInf', bSup') =
            if g > bInf
            then (Just c'', g, bSup)
            else b
      return ([(c'', g)], (best', bInf', bSup'))
    _ -> do
      (NVar v, nvss) <- deleteFindMin nvs
      d <- getL v
      flip (`foldM` ([], b)) d $ \(ss, b2@(_, bInf2, bSup2)) i -> do
        push
        traceM' $ "optimizeC': " ++ show v ++ "=" ++ show i
        setS v i
        g <- getConsDeg
        traceM' $ "optimizeC': g=" ++ show g
        (s, b2') <- if g > bInf2 -- && bInf2 < bSup2
                    then do
                      traceM' $ "optimizeC': >" ++ show v ++ "=" ++ show i
                      optimizeC' c nvss b2
                    else do
                      traceM' $ "optimizeC': skip"
                      return ([], b2)
        pop
        return (ss ++ s, b2')

type AllState a = ([a], RGrade, RGrade)
allState0 :: AllState a
allState0 = ([], minBound, maxBound)

-- | Optimize variables specified in 'Traversable' and return all solutions.
optimizeAllT :: (FDValue v, Traversable t)
             => t (Var s v) -> FD s ([t v], RGrade)
optimizeAllT t = do
  (ss, bInf, _) <-
    optimizeAllC' (CTraversable t) (Foldable.toList $ fmap NVar t) allState0
  return (ss, bInf)

-- | Optimize variables specified in 'Container' and return all solutions.
optimizeAllC :: Container c c' => c (Var s) -> FD s ([c'], RGrade)
optimizeAllC c = do
  (ss, bInf, _) <-
    optimizeAllC' c (fromContainer NVar c) allState0
  return (ss, bInf)

optimizeAllC' :: Container c c'
              => c (Var s) -> [NVar s] -> AllState c' -> FD s (AllState c')
optimizeAllC' c nvs b@(best, bInf, bSup) =
  case nvs of
    [] -> do
      c' <- getCL c
      g <- getConsDeg
      traceM' $ "optimizeC': g=" ++ show g
      let c'' = cdown head c'
      let (best', bInf', bSup')
            | g >  bInf = ([c''],         g,    bSup)
            | g == bInf = (best ++ [c''], bInf, bSup)
            | otherwise = b
      return (best', bInf', bSup')
    _ -> do
      (NVar v, nvss) <- deleteFindMin nvs
      d <- getL v
      flip (`foldM` b) d $ \b2@(_, bInf2, bSup2) i -> do
        push
        traceM' $ "optimizeAllC': " ++ show v ++ "=" ++ show i
        setS v i
        g <- getConsDeg
        traceM' $ "optimizeAllC': g=" ++ show g
        b2' <- if g >= bInf2
               then do
                 traceM' $ "optimizeAllC': >" ++ show v ++ "=" ++ show i
                 optimizeAllC' c nvss b2
               else do
                 traceM' $ "optimizeAllC': skip"
                 return b2
        pop
        return b2'

-- | Degree of consistency
getConsDeg :: FD s RGrade
getConsDeg = do
  cr <- getCons
  gs <- mapM consGrade cr
  return $ foldl' (?&) maxBound gs

-- | (for internal)
deleteFindMin :: [NVar s] -> FD s (NVar s, [NVar s])
deleteFindMin nvs = do
  vdss <- forM nvs $
          \(NVar v) -> Fuzzy.size <$> readSTRef (varDomain v)
  let smin = minimum vdss
  let (former, latter) = span (\(vds, _) -> vds /= smin) $ zip vdss nvs
  let nvsmin = snd $ head latter
  let cnvs = map snd $ former ++ tail latter
  return (nvsmin, cnvs)

-- Primitives for variable domain propagator

-- | Add a propagator to the variable
add :: Var s v -> VarPropagator s -> FD s ()
add v p = modifySTRef (varProp v) $ \ps -> p:ps

add1 :: FDValue v => String -> FR1 v RGrade -> Var s v -> FD s ()
add1 n r v = do
  traceM' $ "add1: " ++ n ++ " " ++ show v
  addCons Constraint { consName = n, consVars = [NVar v],
                       consGrade = primCons1 r v }

primCons1 :: FDValue v => FR1 v RGrade -> Var s v -> FD s RGrade
primCons1 r v = do
  mx <- getS v
  let g = r <$> mx
  return $ fromMaybe maxBound g

add2 :: (FDValue v1, FDValue v2) =>
        String -> FR2 v1 v2 RGrade -> Var s v1 -> Var s v2 -> FD s ()
add2 n r v1 v2 = do
  traceM' $ "add2: " ++ n ++ " " ++ show (v1, v2)
  addCons Constraint { consName = n, consVars = [NVar v1, NVar v2],
                       consGrade = primCons2 r v1 v2 }
{-
  let vp1 = VarPropagator { vpName = n, vpVars = [NVar v1, NVar v2],
                            vpAction = arcProp r v2 v1 }
  let vp2 = VarPropagator { vpName = n, vpVars = [NVar v2, NVar v1],
                            vpAction = arcProp r v2 v1}
  add v1 vp1
  add v2 vp2
  arcProp r v1 v2
  arcProp r v2 v1
-}

primCons2 :: (FDValue v1, FDValue v2) =>
             FR2 v1 v2 RGrade -> Var s v1 -> Var s v2 -> FD s RGrade
primCons2 r v1 v2 = do
  mx1 <- getS v1
  mx2 <- getS v2
  let g = do
        x1 <- mx1
        x2 <- mx2
        return $ r (x1, x2)
  return $ fromMaybe maxBound g

getS :: FDValue v => Var s v -> FD s (Maybe v)
getS v = do
  x <- get v
  return $ if Fuzzy.size x == 1 then Just (head (Fuzzy.support x)) else Nothing

arcProp :: (FDValue v1, FDValue v2) =>
           FR2 v1 v2 RGrade -> Var s v1 -> Var s v2 -> FD s ()
arcProp r v1 v2 = do
  let sup = maxBound
  -- sup <- getSup
  x1 <- get v1
  x2 <- get v2
  let (sup', changed, x1') = revise r x1 x2 sup
  -- setSup sup'
  when changed $ do
    setV v1 x1'
    return ()

addN :: FDValue v => String -> FRN v RGrade -> [Var s v] -> FD s ()
addN n r vs = do
  traceM' $ "addN: " ++ n ++ " " ++ show vs
  addCons Constraint { consName = n, consVars = map NVar vs,
                       consGrade = primConsN r vs }
{-
  let vp = VarPropagator { vpName = n, vpVars = map NVar vs, vpAction = a}
  mapM_ (`add` vp) vs
  a
-}

primConsN :: FDValue v => FRN v RGrade -> [Var s v] -> FD s RGrade
primConsN r vs = do
  mxs <- mapM getS vs
  let xs = sequence mxs
  let g = r <$> xs
  return $ fromMaybe maxBound g

-- Primitive constraints

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
    if nd /= Fuzzy.mu x1 d1
    then (True, Fuzzy.update x1 d1 nd)
    else (ch,   x1)

foldArc :: (Fuzzy (s a g), FSet s, Ord a, Ord b, Grade g) =>
           (c -> (a, b) -> c) -> c -> s a g -> s b g -> c
foldArc f c x1 x2 = foldl' g c (Fuzzy.support x1) where
  g c' d1 = foldl' (\c'' d2 -> f c'' (d1, d2)) c' (Fuzzy.support x2)

-- | Degree of consistency
arcCons :: (Fuzzy (r (a, b) g), FSet r,
            Fuzzy (s a g), Fuzzy (s b g), FSet s,
            Ord a, Ord b, Grade g) =>
           r (a, b) g -> s a g -> s b g -> a -> b -> g
arcCons r x1 x2 d1 d2 = Fuzzy.mu x1 d1 ?& Fuzzy.mu r (d1, d2) ?& Fuzzy.mu x2 d2

-- Tests

test1 = do
  v <- newL [1..3]
  add1 "test1FR1" test1FR1 v
  return [v]
test1FR1 x = case x of 1         -> 0.2
                       2         -> 0.8
                       3         -> 0.5
                       otherwise -> 0
test1Best = test1 >>= optimizeT
test1All  = test1 >>= optimizeAllT

{-|
>>> runFD testFCSPBest
(Just [0,2,4,6],4 % 5)
-}
testFCSPBest = testFCSP >>= optimizeT

{-|
>>> runFD testFCSPAll
([[0,2,4,6],[1,2,4,6],[1,3,4,6],[1,3,5,6],[1,3,5,7],[2,2,4,6],[2,3,4,6],[2,3,5,6],[2,3,5,7],[2,4,4,6],[2,4,5,6],[2,4,5,7],[2,4,6,6],[2,4,6,7],[2,4,6,8]],4 % 5)
-}
testFCSPAll = testFCSP >>= optimizeAllT

testFCSP = do
  x <- newL [0..2]
  y <- newL [2..4]
  z <- newL [4..6]
  w <- newL [6..8]
  x `fcIntEq` y
  y `fcIntEq` z
  z `fcIntEq` w
  return [x, y, z, w]

fcIntEq :: Var s Int -> Var s Int -> FD s ()
fcIntEq = add2 "fcIntEq" frIntEq

frIntEq :: FR Int RGrade
frIntEq (x, y) = fromRational g where
  d = abs (x - y)
  c = 10
  r = toRational d / toRational c
  g, minB, maxB :: Rational
  minB = toRational (minBound :: RGrade)
  maxB = toRational (maxBound :: RGrade)
  g = if d < c then maxB - r else minB

{-
revise rIntEq (fromCoreList [1..3] :: FS Int RGrade) (fromCoreList [1..3]) maxBound
expected: x1'=[1..3] (unchanged)
actual  : x1'=[]
-}
rIntEq :: FR Int RGrade
rIntEq (x, y) | x == y    = maxBound
              | otherwise = minBound
