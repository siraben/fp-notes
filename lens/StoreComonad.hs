{-# LANGUAGE RankNTypes #-}
module StoreComonad(Store(..)) where

-- Generalize to store

-- Reason with type isomorphisms.
type Lens'' a b = (a -> b, b -> a -> a)
-- { flipping }
type Lens' a b = (a -> b, a -> b -> a)
-- { (a ->) distributes over (,) }
type Lens a b = a -> (b, b -> a)

instance Functor (Store b) where
  fmap f (Store piece hole) = Store piece (f . hole)

data Store b a = Store b (b -> a)

-- A comonad is a monad in the opposite category
class Comonad w where
  extract :: w a -> a
  duplicate :: w a -> w (w a)

-- Store forms a comonad
instance Comonad (Store b) where
  extract (Store piece hole) = hole piece
  duplicate (Store piece hole) = Store piece (\b -> Store b hole)

-- F-algebras, and their dual, F-coalgebras
type Alg f a = f a -> a
type Coalg f a = a -> f a
