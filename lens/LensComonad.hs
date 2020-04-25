{-# LANGUAGE RankNTypes #-}
module LensComonad where
import StoreComonad

type Lens a b = forall f. Functor f => Coalg f b -> Coalg f a

(>-) :: Lens a b -> Lens b c -> Lens a c
la >- lb = la . lb

_1 :: Lens (a, b) a
_1 inj (a,b) = (\a -> (a,b)) <$> inj a

experiment :: Functor f => Store b a -> (b -> f b) -> f a
experiment (Store part hole) inj = hole <$> inj part

guess :: (forall f. Functor f => (b -> f b) -> f a) -> Store b a
guess m = m $ \piece -> Store piece id

