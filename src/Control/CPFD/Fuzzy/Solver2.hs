-- | Fuzzy Constraint Satisfaction Problem Solver

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverlappingInstances       #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module Control.CPFD.Fuzzy.Solver2
       (
       -- * Monads
         FD, FDS, FDState
       , runFD, runFD'
       -- * Variables and Domains
       , Grade, RGrade, Domain, FDValue, Var, NVar
       , Container, ContainerMap (..), ContainerLift (..)
       , CTraversable (..)
       , new, newL, newN, newNL, newT, newTL, newCL
       -- * Constraint Store
       , add1, add2, addN
       -- * Labelling
       , labelAll, labelAllT
       , label, labelT
       -- -- * (Old) Optimization
       -- , optimizeT, optimizeC
       -- , optimizeAllT, optimizeAllC
       -- * Optimization
       , optimize, optimizeT
       -- * (for debug)
       , revise, arcCons
       ) where

import           Control.Applicative    (Applicative, (<$>), (<*>))
import           Control.Monad          (foldM, forM, replicateM, unless, when)
import           Control.Monad          (MonadPlus, mplus, msum, mzero)
import           Control.Monad.RWS.Lazy (RWST, runRWST)
import           Control.Monad.ST.Lazy  (ST, runST)
import           Control.Monad.Trans    (lift)
import           Data.List              (foldl')
import           Data.Maybe             (fromMaybe, listToMaybe, maybeToList)
import           Data.STRef.Lazy        (STRef)
import           Data.Traversable       (Traversable)
import           Data.Typeable
import           Debug.Trace            (traceM)
import           Data.Dynamic
import qualified GHC.Exts               as Exts (Constraint)


import qualified Control.Monad.State  as State
import qualified Control.Monad.Writer as Writer
import qualified Data.Foldable        as Foldable
import qualified Data.STRef.Lazy      as STRef
import qualified Data.Traversable     as Traversable

import Control.Lens
import Control.Lens.Action

import Control.CPFD.Internal.Queue (Queue)
import Data.Container
import Data.Fuzzy                  (FR, FR1, FR2, FRN, FS, FSet, FSetUpdate,
                                    FValue, Fuzzy, Grade, RGrade, (?&), (?|))

import qualified Control.CPFD.Internal.Queue as Queue
import qualified Data.Fuzzy                  as Fuzzy

-- class Monad m => FD m where

-- | Monad for constraints on finite domain
newtype FD s a =
  FD { unFD :: RWST FDEnv FDLog FDState (ST s) a }
  deriving (Functor, Applicative, Monad)

instance Show (FD s a) where
  show _ = "<FD>"

data FDEnv =
  FDEnv
  { _traceFlag :: Bool                           -- ^ switch for all the traces
  } deriving (Show)

type FDLog = [String]

data FDState =
  FDState
  { _cnt        :: Int
  , _cntVarGet  :: Int
  , _cntVarSet  :: Int
  , _cntConsDeg :: Int
  } deriving (Show)

initState :: FDState
initState = FDState 0 0 0 0

incrCnt :: Enum a => Setting' (->) FDState a -> FD s ()
incrCnt l = FD $ l %= succ

-- | (for internal use)
data FDStore s =
  FDStore
  { _varList   :: STRef s [NVar s]
  , _lastVarId :: STRef s Int
  , _fdCons    :: STRef s [Constraint s]
  , _varPopper :: STRef s [Popper s]
  , _varPStack :: STRef s [[Popper s]]
  , _propQueue :: STRef s (Queue (Propagator s))
  , _propStack :: STRef s [String]               -- ^ for trace of backtracking
  }

type FDS s a = (?store::FDStore s) => FD s a

-- | (for internal use in variable list)
data NVar s = forall v. FDValue v => NVar (Var s v)

instance Show (NVar s) where
  show = showNVar'

-- | (for debug)
showNVar' :: NVar s -> String
showNVar' (NVar v) = "_" ++ show (_varId v)

-- | Finite domain variable
data Var s v =
  Var
  { _varId     :: Int
  , _varDomain :: STRef s (Domain v)
  , _varStack  :: STRef s [Domain v]
  , _varProp   :: STRef s [VarPropagator s] }

type Domain v = FS v RGrade
type FDValue v = Fuzzy.FValue v
class FDValue v => FDValue' v

instance Show (Var s v) where
  show v = "_" ++ show (_varId v)

type Popper s = FD s ()

-- | Propagate a domain changing to others.
data VarPropagator s =
  VarPropagator
  { _vpName   :: String
  , _vpVars   :: [NVar s]
  , _vpAction :: FD s () }
  deriving (Show)

-- | Queue elements for propagating the specified domain changing to others.
data Propagator s =
  Propagator
  { _propVar  :: NVar s
  , _propProp :: VarPropagator s }
  deriving (Show)

data Constraint s =
  Constraint
  { _consName  :: String        -- ^ for debug
  , _consVars  :: [NVar s]      -- ^ for debug
  , _consGrade :: FD s RGrade
  } deriving (Show)

makeLenses ''FDEnv
makeLenses ''FDState
makeLenses ''FDStore
makeLenses ''Var
makeLenses ''VarPropagator
makeLenses ''Propagator
makeLenses ''Constraint

-- | (for debug)
showNVar :: NVar s -> FD s String
showNVar (NVar v) = do
  d <- readSTRef (_varDomain v)
  s <- readSTRef (_varStack v)
  return $ show (_varId v, d, s)

{-
r |. l = readSTRef (r ^. l)

(%|) l f r = modifySTRef (r ^. l) f
-}

{-|
useR :: (?store::FDStore s)
     => Getting (STRef s a) (FDStore s) (STRef s a) -> FD s a
useR l = readSTRef (?store ^. l)

(%|) :: (?store::FDStore s)
     => Getting (STRef s a) (FDStore s) (STRef s a) -> (a -> a) -> FD s ()
l %| f = modifySTRef (?store ^. l) f
-}

{-
use' :: Getting a (FDState s0) a -> FD s0 a
use' = FD . use

(%$) :: Profunctor p
     => Setting p (FDState s) (FDState s) a b -> p a b -> FD s ()
l %$ f = FD $ l %= f
-}

-- | (for internal use)
liftST :: ST s a -> FD s a
liftST = FD . lift

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

traceFD :: String -> FD s ()
traceFD s = FD $ Writer.tell [s]

-- | Run FD monad
runFD :: (forall s. FDS s a) -> (a, FDState, FDLog)
runFD fd = runST $ runRWST (unFD $ fdWrapper fd) (FDEnv False) initState

-- | Run FD monad with trace for debug
runFD' :: (forall s. FDS s a) -> (a, FDState, FDLog)
runFD' fd = runST $ runRWST (unFD $ fdWrapper fd) (FDEnv True) initState

-- | (for internal use)
fdWrapper :: FDS s a -> FD s a
fdWrapper fd = do
  vl  <- newSTRef []
  rvi <- newSTRef 0
  rc  <- newSTRef []
  rvp <- newSTRef []
  rvs <- newSTRef []
  rpq <- newSTRef Queue.empty
  rst <- newSTRef []
  let ?store =
        FDStore { _varList = vl
                , _lastVarId = rvi
                , _fdCons    = rc
                , _varPopper = rvp
                , _varPStack = rvs
                , _propQueue = rpq
                , _propStack = rst
                }
  traceFD "Initialized."
  a <- fd
  traceFD "Terminated."
  return a

-- | (for debug)
getVarList :: FDS s [NVar s]
getVarList = (?store ^. varList) ^! act readSTRef

-- | (for debug)
traceM' :: String -> FD s ()
traceM' s = do
  f <- FD $ view traceFlag
  when f $ traceM s

getCons :: FDS s [Constraint s]
getCons = (?store ^. fdCons) ^! act readSTRef

addCons :: Constraint s -> FDS s ()
addCons c = (?store ^. fdCons) ^! act (`modifySTRef` (c:))

-- Primitives for variable domain

-- | Create a new variable with domain.
new :: FDValue v => Domain v -> FDS s (Var s v)
new d = do
  vi <- newVarId
  vd <- newSTRef d
  vs <- newSTRef []
  vp <- newSTRef []
  let v = Var { _varId = vi, _varDomain = vd, _varStack = vs, _varProp = vp }
  (?store ^. varList) ^! act (`modifySTRef` (NVar v:))
  return v

-- | (for internal)
newVarId :: FDS s Int
newVarId = do
  (?store ^. lastVarId) ^! act (`modifySTRef` succ)
  (?store ^. lastVarId) ^! act readSTRef

-- | Get domain of the variable.
getV :: Var s v -> FDS s (Domain v)
getV v = do
  incrCnt cntVarGet
  execProp
  (v ^. varDomain) ^! act readSTRef

-- | Set domain of the variable and invoke propagators.
setV :: FDValue v => Var s v -> Domain v -> FDS s ()
setV v d = do
  incrCnt cntVarSet
  pushV v
  (?store ^. varPopper) ^! act (`modifySTRef` (popV v:))
  (v ^. varDomain) ^! act (`writeSTRef` d)
  p <- (v ^. varProp) ^! act readSTRef
  enqProp v p

-- | (for debug)
getPropQueue :: FDS s [String]
getPropQueue = do
  q <- (?store ^. propQueue) ^! act readSTRef
  return $ Queue.toList q & map (_vpName . _propProp)

-- | (for internal)
enqProp :: FDValue v => Var s v -> [VarPropagator s] -> FDS s ()
enqProp v = mapM_ enq where
  enq vp = do
    let p = Propagator { _propVar = NVar v, _propProp = vp }
    (?store ^. propQueue) ^! act modifySTRef $ Queue.enq p
    traceM' $ "enqProp: " ++ show v ++ " -> " ++ _vpName vp ++ show (_vpVars vp)

-- | (for internal)
execProp :: FDS s ()
execProp = do
  q <- (?store ^. propQueue) ^! act readSTRef
  unless (Queue.null q) $ do
    let (p, q') = Queue.deq q
    let v  = _propVar  p
    let vp = _propProp p
    (?store ^. propQueue) ^! act (`writeSTRef` q')
    traceM' $ "execProp: > " ++ show v ++ " -> " ++ _vpName vp ++ show (_vpVars vp)
    vp ^. vpAction
    traceM' $ "execProp: < " ++ show v ++ " -> " ++ _vpName vp ++ show (_vpVars vp)
    execProp

-- | (for debug)
getPropStack :: FDS s [String]
getPropStack = (?store ^. propStack) ^! act readSTRef

-- | (for debug)
pushPropStack :: String -> FDS s ()
pushPropStack n = (?store ^. propStack) ^! act (`modifySTRef` (n:))

-- | (for debug)
popPropStack :: FDS s ()
popPropStack = (?store ^. propStack) ^! act (`modifySTRef` tail)

-- Utilities for variable domain

-- | Same as 'new' except to take a list as domain.
newL :: FDValue v => [v] -> FDS s (Var s v)
newL d = new (Fuzzy.fromCoreList d)

-- | Same as 'new' except to take a number of variables to create.
newN :: FDValue v => Int -> Domain v -> FDS s [Var s v]
newN n d = replicateM n (new d)

-- | Same as 'newN' except to take a list as domain.
newNL :: FDValue v => Int -> [v] -> FDS s [Var s v]
newNL n d = replicateM n (newL d)

-- | Same as 'new' except to take a Traversable containing domains.
newT :: (FDValue v, Traversable t) => t (Domain v) -> FDS s (t (Var s v))
newT = Traversable.mapM new

-- | Same as 'new' except to take a Traversable containing lists as domains.
newTL :: (FDValue v, Traversable t) => t [v] -> FDS s (t (Var s v))
newTL = Traversable.mapM newL

{-
-- | Same as 'new' except to take a Container containing domains.
newC :: ContainerMap c => c Domain -> FDS s (c (Var s))
newC = cmapM new
-}

-- | Same as 'new' except to take a Container containing domains.
newCL :: ContainerMap c => c [] -> FDS s (c (Var s))
newCL = cmapM newL

-- -- | Same as 'new' except to take a stracture containing domains.
-- newPL :: GNT s t [] (Var s) => s -> FDS s t
-- newPL = undefined -- gntA newL

-- | Same as 'get' except to return a list as domain.
getL :: FDValue v => Var s v -> FDS s [v]
getL v = Fuzzy.support <$> getV v

-- | Same as 'get' except to return a list as domain in Container.
getCL :: ContainerMap c => c (Var s) -> FDS s (c [])
getCL = cmapM getL

-- | Set domain of the variable with singleton value and invoke propagators.
setS :: FDValue v => Var s v -> v -> FDS s ()
setS v val = setV v (Fuzzy.fromCoreList [val])

-- | Same as 'set' except to take a list as domain.
setL :: FDValue v => Var s v -> [v] -> FDS s ()
setL v d = setV v (Fuzzy.fromCoreList d)

-- Labeling

-- | (for debug)
getStack :: Var s v -> FD s [Domain v]
getStack v = (v ^. varStack) ^! act readSTRef

pushV :: Var s a -> FD s ()
pushV v = do
  traceM' $ "{ -- pushV:" ++ show v
  d <- (v ^. varDomain) ^! act readSTRef
  (v ^. varStack) ^! act (`modifySTRef` (d:))

popV :: Var s a -> FD s ()
popV v = do
  traceM' $ "} -- popV:" ++ show v
  (d:ds) <- (v ^. varStack) ^! act readSTRef
  (v ^. varDomain) ^! act (`writeSTRef` d)
  (v ^. varStack) ^! act (`writeSTRef` ds)

push :: FDS s ()
push = do
  traceM' "{ -- push"
  s <- (?store ^. varPopper) ^! act readSTRef
  (?store ^. varPStack) ^! act (`modifySTRef` (s:))
  (?store ^. varPopper) ^! act (`writeSTRef` [])

pop :: FDS s ()
pop = do
  traceM' "} -- pop"
  s <- (?store ^. varPopper) ^! act readSTRef
  _ <- sequence s
  (st:ss) <- (?store ^. varPStack) ^! act readSTRef
  (?store ^. varPopper) ^! act (`writeSTRef` st)
  (?store ^. varPStack) ^! act (`writeSTRef` ss)

local :: FDS s a -> FDS s a
local action = do
  push
  a <- action
  pop
  return a

-- | Label variables specified in Traversable.
labelT_ :: (FDValue v, Traversable t) => t (Var s v) -> FDS s [(t v, RGrade)]
labelT_ t = labelC'_ (CTraversable t) (Foldable.toList $ fmap NVar t)

-- | Label variables specified in Container.
labelC_ :: Container c c' => c (Var s) -> FDS s [(c', RGrade)]
labelC_ c = labelC'_ c (fromContainer NVar c)

labelC'_ :: Container c c' => c (Var s) -> [NVar s] -> FDS s [(c', RGrade)]
labelC'_ c nvs =
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
        s <- labelC'_ c nvss
        pop
        return (ss ++ s)

type BestSolution_ a = (Maybe a, RGrade, RGrade)
initBestSolution_ :: BestSolution_ a
initBestSolution_ = (Nothing, minBound, maxBound)

-- | Optimize variables specified in 'Traversable'.
optimizeT_ :: (FDValue v, Traversable t)
          => t (Var s v) -> FDS s (Maybe (t v), RGrade)
optimizeT_ t = do
  (_, (best, g, _)) <-
    optimizeC'_ (CTraversable t) (Foldable.toList $ fmap NVar t) initBestSolution_
  return (best, g)

-- | Optimize variables specified in 'Container'.
optimizeC_ :: Container c c' => c (Var s) -> FDS s (Maybe c', RGrade)
optimizeC_ c = do
  (_, (best, g, _)) <-
    optimizeC'_ c (fromContainer NVar c) initBestSolution_
  return (best, g)

optimizeC'_ :: Container c c'
           => c (Var s) -> [NVar s] -> BestSolution_ c'
           -> FDS s ([(c', RGrade)], BestSolution_ c')
optimizeC'_ c nvs b@(_, bInf, bSup) =
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
                      optimizeC'_ c nvss b2
                    else do
                      traceM' $ "optimizeC': skip"
                      return ([], b2)
        pop
        return (ss ++ s, b2')

type AllState_ a = ([a], RGrade, RGrade)
allState0_ :: AllState_ a
allState0_ = ([], minBound, maxBound)

-- | Optimize variables specified in 'Traversable' and return all solutions.
optimizeAllT_ :: (FDValue v, Traversable t)
             => t (Var s v) -> FDS s ([t v], RGrade)
optimizeAllT_ t = do
  (ss, bInf, _) <-
    optimizeAllC'_ (CTraversable t) (Foldable.toList $ fmap NVar t) allState0_
  return (ss, bInf)

-- | Optimize variables specified in 'Container' and return all solutions.
optimizeAllC_ :: Container c c' => c (Var s) -> FDS s ([c'], RGrade)
optimizeAllC_ c = do
  (ss, bInf, _) <-
    optimizeAllC'_ c (fromContainer NVar c) allState0_
  return (ss, bInf)

optimizeAllC'_ :: Container c c'
              => c (Var s) -> [NVar s] -> AllState_ c' -> FDS s (AllState_ c')
optimizeAllC'_ c nvs b@(best, bInf, bSup) =
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
                 optimizeAllC'_ c nvss b2
               else do
                 traceM' $ "optimizeAllC': skip"
                 return b2
        pop
        return b2'

-- | Degree of consistency
getConsDeg :: FDS s RGrade
getConsDeg = do
  incrCnt cntConsDeg
  cr <- getCons
  gs <- mapM _consGrade cr
  return $ foldl' (?&) maxBound gs

-- | (for internal)
deleteFindMin :: [NVar s] -> FD s (NVar s, [NVar s])
deleteFindMin nvs = do
  vdss <- forM nvs $
          \(NVar v) -> Fuzzy.size <$> readSTRef (_varDomain v)
  let smin = minimum vdss
  let (former, latter) = span (\(vds, _) -> vds /= smin) $ zip vdss nvs
  let nvsmin = snd $ head latter
  let cnvs = map snd $ former ++ tail latter
  return (nvsmin, cnvs)

-- Primitives for variable domain propagator

-- | Add a propagator to the variable
add :: Var s v -> VarPropagator s -> FD s ()
add v p = (v ^. varProp) ^! act (`modifySTRef` (p:))

add1 :: FDValue v => String -> FR1 v RGrade -> Var s v -> FDS s ()
add1 n r v = do
  traceM' $ "add1: " ++ n ++ " " ++ show v
  addCons Constraint { _consName = n, _consVars = [NVar v],
                       _consGrade = primCons1 r v }

primCons1 :: FDValue v => FR1 v RGrade -> Var s v -> FDS s RGrade
primCons1 r v = do
  mx <- getS v
  let g = r <$> mx
  return $ fromMaybe maxBound g

add2 :: (FDValue v1, FDValue v2) =>
        String -> FR2 v1 v2 RGrade -> Var s v1 -> Var s v2 -> FDS s ()
add2 n r v1 v2 = do
  traceM' $ "add2: " ++ n ++ " " ++ show (v1, v2)
  addCons Constraint { _consName = n, _consVars = [NVar v1, NVar v2],
                       _consGrade = primCons2 r v1 v2 }
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
             FR2 v1 v2 RGrade -> Var s v1 -> Var s v2 -> FDS s RGrade
primCons2 r v1 v2 = do
  mx1 <- getS v1
  mx2 <- getS v2
  let g = do
        x1 <- mx1
        x2 <- mx2
        return $ r (x1, x2)
  return $ fromMaybe maxBound g

getS :: FDValue v => Var s v -> FDS s (Maybe v)
getS v = do
  x <- getV v
  return $ if Fuzzy.size x == 1 then Just (head (Fuzzy.support x)) else Nothing

arcProp :: (FDValue v1, FDValue v2) =>
           FR2 v1 v2 RGrade -> Var s v1 -> Var s v2 -> FDS s ()
arcProp r v1 v2 = do
  let sup = maxBound
  -- sup <- getSup
  x1 <- getV v1
  x2 <- getV v2
  let (sup', changed, x1') = revise r x1 x2 sup
  -- setSup sup'
  when changed $ do
    setV v1 x1'
    return ()

addN :: FDValue v => String -> FRN v RGrade -> [Var s v] -> FDS s ()
addN n r vs = do
  traceM' $ "addN: " ++ n ++ " " ++ show vs
  addCons Constraint { _consName = n, _consVars = map NVar vs,
                       _consGrade = primConsN r vs }
{-
  let vp = VarPropagator { vpName = n, vpVars = map NVar vs, vpAction = a}
  mapM_ (`add` vp) vs
  a
-}

primConsN :: FDValue v => FRN v RGrade -> [Var s v] -> FDS s RGrade
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

-- New API

-- | Data stream
type Stream m = (MonadPlus m, Applicative m)

select :: Stream m => [a] -> m a
select = foldr (\x m -> return x `mplus` m) mzero

-- NT-like transformation

class Applicative (NTCxt f g) => NTLike f g where
  type NTTyCxt (f :: * -> *) (g :: * -> *) a :: Exts.Constraint
  type NTCxt (f :: * -> *) (g :: * -> *) :: * -> *
  ntA :: forall a. NTTyCxt f g a => f a -> (NTCxt f g) (g a)

instance NTLike [] (Var s) where
  type NTTyCxt [] (Var s) a = (FDValue a, ?store::FDStore s)
  type NTCxt [] (Var s) = FD s
  ntA = newL

instance NTLike (Var s) [] where
  type NTTyCxt (Var s) [] a = (FDValue a, ?store::FDStore s)
  type NTCxt (Var s) [] = FD s
  ntA = getL

instance NTLike [] Maybe where
  type NTTyCxt [] Maybe a = ()
  type NTCxt [] Maybe = Identity
  ntA = Identity . listToMaybe

instance NTLike f (Const Dynamic) where
  type NTTyCxt f (Const Dynamic) a = (Typeable f, Typeable a)
  type NTCxt f (Const Dynamic) = Identity
  ntA = Identity . Const . toDyn

instance NTLike (Var s) (Const (NVar s)) where
  type NTTyCxt (Var s) (Const (NVar s)) a = (FDValue a)
  type NTCxt (Var s) (Const (NVar s)) = Identity
  ntA = Identity . Const . NVar

-- type class for NT-like in containers

class NTLike f g => GNTLike t f g where
  gntA :: t f -> (NTCxt f g) (t g)

newtype TupleV a b f = TupleV { getTupleV :: (f a, f b) } deriving (Show, Eq)
instance (t ~ TupleV a b f) => Rewrapped (TupleV a b g) t
instance Wrapped (TupleV a b f) where
  type Unwrapped (TupleV a b f) = (f a, f b)
  _Wrapped' = iso getTupleV TupleV
  {-# INLINE _Wrapped' #-}

instance (NTLike f g, NTTyCxt f g a, NTTyCxt f g b) =>
         GNTLike (TupleV a b) f g where
  gntA (TupleV (a, b)) = TupleV <$> ((,) <$> ntA a <*> ntA b)

newtype TraversableV t a f = TraversableV { getTraversableV :: t (f a) }
                           deriving (Show, Eq)
instance (t' ~ TraversableV t a f) => Rewrapped (TraversableV t a g) t'
instance Wrapped (TraversableV t a f) where
  type Unwrapped (TraversableV t a f) = t (f a)
  _Wrapped' = iso getTraversableV TraversableV
  {-# INLINE _Wrapped' #-}

instance (NTLike f g, NTTyCxt f g a, Traversable t) =>
         GNTLike (TraversableV t a) f g where
  gntA (TraversableV t) = TraversableV <$> traverse ntA t

-- unlifting

class Applicative f => HasLift b t f where
  unlift :: t f -> f b

instance Applicative f => HasLift (a, b) (TupleV a b) f where
  unlift (TupleV (a, b)) = (,) <$> a <*> b

instance (Applicative f, Traversable t) =>
         HasLift (t a) (TraversableV t a) f where
  unlift (TraversableV t) = traverse id t

-- to list

class ToList t f where
  toList :: (forall a. FDValue a => f a -> g) -> t -> [g]

instance (FDValue a, FDValue b) => ToList (TupleV a b f) f where
  toList f (TupleV (a, b)) = [f a, f b]

-- to list without context

class ToList' t f g where
  toList' :: (forall a. f a -> g) -> t f -> [g]

instance ToList' (TupleV a b) f g where
  toList' f (TupleV (a, b)) = [f a, f b]

instance Traversable t => ToList' (TraversableV t a) f g where
  toList' f (TraversableV t) = Foldable.toList $ fmap f t

toNVarList :: (GNTLike t (Var s) (Const (NVar s)),
               ToList' t (Const (NVar s)) (NVar s))
              => t (Var s) -> [NVar s]
toNVarList = toList' getConst . runIdentity . gntA

-- Label and Optimize

-- | Optimize given variables and return the captured solutions.
labelAll ::
  (Stream m,
   ToList' t (Const (NVar s)) (NVar s),
   GNTLike t (Var s) (Const (NVar s)),
   GNTLike t (Var s) [],
   HasLift b t [])
  => t (Var s)              -- ^ Wrapped varibales to label.
  -> FDS s (m (b, RGrade))  -- ^ Stream of solutions with satisfaction grade.
labelAll t = labelAll' t (toNVarList t)

labelAll' ::
  (Stream m,
   GNTLike t (Var s) [],
   HasLift b t [])
  => t (Var s)              -- ^ Wrapped varibales to label.
  -> [NVar s]
  -> FDS s (m (b, RGrade))  -- ^ Stream of solutions with satisfaction grade.
labelAll' c [] = do
  d <- gntA c
  let s = unlift d
  g <- getConsDeg
  return $ select $ fmap (,g) s
labelAll' c (NVar v:vs) = do
  d <- getL v
  s <- forM d $ \i -> do
    local $ do
      setS v i
      labelAll' c vs
  return $ msum s

labelAllT ::
  (Stream m, Traversable t, FDValue a)
  => t (Var s a)             -- ^ Wrapped varibales to label.
  -> FDS s (m (t a, RGrade)) -- ^ Stream of solutions with satisfaction grade.
labelAllT t = labelAll (TraversableV t)

-- | Optimize given variables and return the captured solutions.
label ::
  (Stream m,
   ToList' t (Const (NVar s)) (NVar s),
   GNTLike t (Var s) (Const (NVar s)),
   GNTLike t (Var s) [],
   HasLift b t [])
  => RGrade                 -- ^ Lower threashold of consitency grade.
  -> t (Var s)              -- ^ Wrapped varibales to label.
  -> FDS s (m (b, RGrade))  -- ^ Stream of solutions with satisfaction grade.
label bInf t = label' bInf t (toNVarList t)

label' ::
  (Stream m,
   GNTLike t (Var s) [],
   HasLift b t [])
  => RGrade                 -- ^ Lower threashold of consitency grade.
  -> t (Var s)              -- ^ Wrapped varibales to label.
  -> [NVar s]
  -> FDS s (m (b, RGrade))  -- ^ Stream of solutions with satisfaction grade.
label' bInf c [] = do
  d <- gntA c
  let s = unlift d
  g <- getConsDeg
  if g >= bInf
  then return $ select $ fmap (,g) s
  else return $ mzero
label' bInf c (NVar v:vs) = do
  d <- getL v
  s <- forM d $ \i -> do
    local $ do
      setS v i
      g <- getConsDeg
      if g >= bInf
      then label' bInf c vs
      else return mzero
  return $ msum s

labelT ::
  (Stream m, Traversable t, FDValue a)
  => RGrade                  -- ^ Lower threashold of consitency grade.
  -> t (Var s a)             -- ^ Wrapped varibales to label.
  -> FDS s (m (t a, RGrade)) -- ^ Stream of solutions with satisfaction grade.
labelT bInf t = label bInf (TraversableV t)

-- Optimize

data OptState m b =
  OptState
  { _optSol :: m (b, RGrade)
  , _optBoundInf :: RGrade
  , _optBoundSup :: RGrade
  }

deriving instance (Show (m (b, RGrade))) => Show (OptState m b)

makeLenses ''OptState

initOptState :: MonadPlus m => OptState m b
initOptState = OptState mzero minBound maxBound

-- | Optimize given variables and return the captured solutions.
optimize ::
  (Stream m,
   ToList' t (Const (NVar s)) (NVar s),
   GNTLike t (Var s) (Const (NVar s)),
   GNTLike t (Var s) [],
   HasLift b t [])
  => t (Var s)              -- ^ Wrapped varibales to label.
  -> FDS s (m (b, RGrade))  -- ^ Stream of solutions with satisfaction grade.
optimize t = do
  state <- optimize' initOptState t (toNVarList t)
  return $ state^.optSol

optimize' ::
  (Stream m,
   GNTLike t (Var s) [],
   HasLift b t [])
  => OptState m b           -- ^ Current optimization state
  -> t (Var s)              -- ^ Wrapped varibales to label.
  -> [NVar s]
  -> FDS s (OptState m b)   -- ^ Last optimization state.
optimize' state c [] = do
  d <- gntA c
  let sol = unlift d
  g <- getConsDeg
  let state' = case g `compare` (state ^. optBoundInf) of
        GT -> state { _optSol = select $ fmap (,g) sol
                    , _optBoundInf = g }
        EQ -> state & optSol %~ (`mplus` select (fmap (,g) sol))
        LT -> state
  return state'
optimize' state c (NVar v:vs) = do
  d <- getL v
  foldM f state d
  where
    f s i = local $ do
      setS v i
      g <- getConsDeg
      if g >= s ^. optBoundInf
      then optimize' s c vs
      else return s

optimizeT ::
  (Stream m, Traversable t, FDValue a)
  => t (Var s a)             -- ^ Wrapped varibales to label.
  -> FDS s (m (t a, RGrade)) -- ^ Stream of solutions with satisfaction grade.
optimizeT t = optimize (TraversableV t)

-- Examples

p1 :: ([Int], [Bool])
p1 = ([1, 2], [True, False])

p2 :: (Domain Int, Domain Bool)
p2 = (Fuzzy.fromList [(1, 0.7), (2, 0.3)],
      Fuzzy.fromList [(True, 0.4), (False, 0.6)])

usecase1 :: (Maybe Int, Maybe Bool)
usecase1 = getTupleV $ runIdentity $ gntA (TupleV p1)

usecase2 :: FDS s (Var s Int, Var s Bool)
usecase2 = do -- under (_Wrapping TupleV) gntA p1
  let wd = p1 ^. _Unwrapping TupleV -- :: TupleV Int Bool []
  wv <- gntA wd -- :: FDS s (TupleV Int Bool (Var s))
  let v = wv ^. _Wrapped
  return v

usecase3 :: FDS s [(Int, Bool)]
usecase3 = do
  (TupleV v) <- gntA (TupleV p1)
  add2 "parity" parity (v^._1) (v^._2)
  (TupleV d) <- gntA (TupleV v)
  return $ unlift (TupleV d) -- unlift from user code

testopt1 :: (Stream m, HasLift b t []) => t [] -> FDS s (m b)
testopt1 d = do
  return $ select $ unlift d

testopt' :: (Stream m, GNTLike t (Var s) []) => t (Var s) -> FDS s (m (t []))
testopt' l = do
  d <- gntA l
  return $ select [d]

usecase4 :: FDS s [(Int, Bool)]
usecase4 = do
  (TupleV v) <- gntA (TupleV p1)
  add2 "parity" parity (v^._1) (v^._2)
  ds <- testopt' (TupleV v)
  return $ concatMap unlift ds

testopt :: forall s m t b.
           (Stream m, GNTLike t (Var s) [], HasLift b t [])
           => t (Var s) -> FDS s (m b)
testopt l = do
  d <- gntA l :: FDS s (t [])
  let ds = unlift d
  return $ select ds

usecase5 :: FDS s [(Int, Bool)]
usecase5 = do
  (TupleV v) <- gntA (TupleV p1)
  add2 "parity" parity (v^._1) (v^._2)
  testopt (TupleV v)

parity :: FR2 Int Bool RGrade
parity (i, b) = if (i `mod` 2 == 0) == b then 0.7 else 0.3

{-|
>>> testToList'
[<<[Int]>>,<<[Bool]>>]
-}
testToList' :: [Dynamic]
testToList' = toList' getConst . runIdentity . gntA $ TupleV p1


{-|
>>> (runFD testNewOpt ^. _1 :: [((Int, Bool), RGrade)]) & mapMOf_ each print
((1,False),7 % 10)
((1,True),3 % 10)
((2,False),3 % 10)
((2,True),7 % 10)
-}
-- Elements stored in wrapped user-defined data
testNewOpt :: Stream m => FDS s (m ((Int, Bool), RGrade))
testNewOpt = do
  (TupleV v) <- gntA (TupleV p1)
  add2 "parity" parity (v^._1) (v^._2)
  labelAll (TupleV v)

-- Elements stored in Traversable
testNewOpt2 :: Stream m => FDS s (m ([Int], RGrade))
testNewOpt2 = do
  let d = [1, 2, 3, 4, 5]
  -- (TraversableV v) <- gntA (TraversableV [d,d])
  -- v <- traverse newL [d, d]
  -- v <- newNL 2 d
  v <- newTL [d, d]
  add2 "dist" dist (v !! 0) (v !! 1)
  -- labelAll (TraversableV v)
  labelAllT v

dist :: FR2 Int Int RGrade
dist (x, y) = if x == y then 0.7 else 0.3

-- Tests

test1 :: FDS s [Var s Int]
test1 = do
  v <- newL [1..3]
  add1 "test1FR1" test1FR1 v
  return [v]
test1FR1 :: Int -> RGrade
test1FR1 x = case x of 1 -> 0.2
                       2 -> 0.8
                       3 -> 0.5
                       _ -> 0
test1Best :: FDS s [([Int], RGrade)]
test1Best = test1 >>= optimizeT
test1All :: FDS s [([Int], RGrade)]
test1All  = test1 >>= labelAllT

{-|
>>> runFD testFCSPBest ^. _1
(Just [0,2,4,6],4 % 5)
-}
testFCSPBest :: FDS s [([Int], RGrade)]
testFCSPBest = testFCSP >>= optimizeT

{-|
>>> runFD testFCSPAll ^. _1
([[0,2,4,6],[1,2,4,6],[1,3,4,6],[1,3,5,6],[1,3,5,7],[2,2,4,6],[2,3,4,6],[2,3,5,6],[2,3,5,7],[2,4,4,6],[2,4,5,6],[2,4,5,7],[2,4,6,6],[2,4,6,7],[2,4,6,8]],4 % 5)
-}
testFCSPAll :: FDS s [([Int], RGrade)]
testFCSPAll = testFCSP >>= labelAllT

testFCSP :: FDS s [Var s Int]
testFCSP = do
  x <- newL [0..2]
  y <- newL [2..4]
  z <- newL [4..6]
  w <- newL [6..8]
  x `fcIntEq` y
  y `fcIntEq` z
  z `fcIntEq` w
  return [x, y, z, w]

fcIntEq :: Var s Int -> Var s Int -> FDS s ()
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
