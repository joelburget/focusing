{-# language LambdaCase #-}
module Data.Plur where

import Data.Monoid

data Plur a
  = Zero
  | One a
  | Two a a
  deriving (Show, Eq, Ord)

instance Functor Plur where
  fmap f = \case
    Zero      -> Zero
    One a     -> One (f a)
    Two a1 a2 -> Two (f a1) (f a2)

instance Foldable Plur where
  foldMap f = \case
    Zero      -> mempty
    One a     -> f a
    Two a1 a2 -> f a1 <> f a2

instance Traversable Plur where
  traverse f = \case
    Zero      -> pure Zero
    One a     -> One <$> f a
    Two a1 a2 -> Two <$> f a1 <*> f a2

instance Monoid (Plur a) where
  mempty = Zero

  mappend r1 Zero = r1
  mappend Zero r2 = r2
  mappend (One x)   (One y)   = Two x y
  mappend (One x)   (Two y _) = Two x y
  mappend (Two x _) (One y)   = Two x y
  mappend (Two x _) (Two y _) = Two x y
