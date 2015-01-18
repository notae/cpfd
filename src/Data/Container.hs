{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Container where

import           Control.Applicative (Applicative, WrappedMonad (..), (<$>))
import qualified Data.Foldable       as Foldable
import           Data.Traversable    (Traversable)
import qualified Data.Traversable    as Traversable

import Data.Domain (FDValue)

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
