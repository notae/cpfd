{-# LANGUAGE ConstraintKinds #-}

module Control.CPFD.Crisp.Primitives
       (
       -- * Primitive Constraint
       -- ** Core Constraint
         alldiff
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

import           Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable

import           Control.CPFD.Crisp.Solver
import qualified Data.Domain               as Domain

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

-- Internal Tests

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
