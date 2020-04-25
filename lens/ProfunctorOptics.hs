{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes, TypeOperators #-}
-- Saturday, April 25, 2020 at 13:41
-- Profunctor Optics: The Categorical Approach - Bartosz Milewski

-- A profunctor is contravariant in the first argument but covariant
-- in the second.
class Profunctor p where
  dimap :: (a -> b) -> (c -> d) -> (p b c -> p a d)

instance Profunctor ((->)) where
  dimap f g h = g . h . f

-- Natural transformation between functors f and g
type f ~> g = forall x. f x -> g x

safeHead :: [] ~> Maybe
safeHead [] = Nothing
safeHead (x:xs) = Just x

-- Reader functor, Reader a x = a -> x

newtype Reader a x = Reader (a -> x)

-- Reader forms a functor.
instance Functor (Reader w) where
  fmap f (Reader g) = Reader (f . g)

type Yo f a = Functor f => Reader a ~> f

-- Yoneda lemma proof, Yo f a ~= f a
-- { expanding }
-- forall x. (a -> x) -> f x ~= f a

toYo :: Functor f => f a -> Yo f a
toYo fa (Reader atox) = atox <$> fa

fromYo :: Functor f => Yo f a -> f a
fromYo alpha = alpha (Reader id)

{-
Yoneda Embedding
forall x. (a -> x) -> f x ~= f a
What if we specialize f to Reader?
f x = (b -> x)
forall x. (a -> x) -> (b -> x) ~= (b -> a)


Ok, what about Yoneda on Functors?
Take the old embedding
forall x. (a -> x) -> (b -> x) ~= (b -> a)
Then replace arrows with natural transformations

forall x. (a ~> x) -> (b ~> x) ~= (b ~> a)
{ renaming }
forall f. Functor f =>
          (g ~> f) -> (h ~> f) ~= (h ~> g)
-}

-- Toy Optic
{-
We start with the Yoneda lemma in the functor category
forall f. Functor f =>
          (g ~> f) -> (h ~> f) ~= (h ~> g)
{ definition of ~> }
forall f. Functor f =>
          (forall x. g x -> f x)
        -> (forall x. h x -> f x) ~= (forall x. h x -> g x)
Let's specialize g and h with reader, so
g x = a -> x
h x = s -> x

forall f. (forall x. (a -> x) -> f x)
       -> (forall x. (s -> x) -> f x)
       ~= (forall x. (s -> x) -> (a -> x))

{ Yoneda, backwards }

forall f. f a -> f s ~= (a -> s)
-}

type Toy s a = forall f. Functor f => f a -> f s
-- We have the isomorphism Toy s a ~= (a -> s)

-- Let's do Yoneda for profunctors
-- Essentially pairing readers
newtype ProReader a b x y = ProReader (x -> a, b -> y)
instance Profunctor (ProReader a b) where
  dimap from to (ProReader (f, g)) = ProReader (f . from, to . g)

type ProYo p a b = Profunctor p => forall x y. (x -> a, b -> y) -> p x y

-- We have,
-- ProYo p a b ~ p a b
-- Using the Yoneda lemma,
-- forall x y. (x -> a) -> (b -> y) -> p x y ~= p a b

-- Yoneda on profunctors (profunctors form a category and have natural
-- transformations)

{-
   forall p. Profunctor p => (forall x y. q x y -> p x y)
                          -> (forall x y. r x y -> p x y)
~= (forall x y. r x y -> q x y)

{ specialize q and r }
q x y = (a -> x, y -> b)
r x y = (s -> x, y -> t)

  forall p. (forall x y. (a -> x, y -> b) -> p x y)
         -> (forall x y. (s -> x, y -> t) -> p x y)
~= (forall x y. (s -> x, y -> t) -> q x y)


Then, using Yoneda

   forall p. Profunctor p => p a b -> p s t (equivalent to Iso)
~= q s t
~= (a -> s, t -> b)
~= Iso s t a b

-}

-- Adjoint functors
{- F is left adjoint to U
F a -> b ~= a -> U b

For instance,
F a = (a, x)
U b = (x -> b)

We have (curry/uncurry)
(a, x) -> b ~= a -> (x -> b)

Also, Co-Yoneda

exists x. (f x, x -> a) ~= f a
How do we go to f a? Well,
g (fx, xToA) = fmap xToA fx

Yoneda + Adjunction

Here's Yoneda, again
forall x. (a -> x) -> (b -> x) ~= (b -> a)

Replace a with F a, replace b with F b.

forall x. (F a -> x) -> (F b -> x)
       ~= (F b -> F a)

forall x. (a -> U x) -> (b -> U x)
       ~= (b -> (U ∘ F) a)
(composition of two adjoint functors is a monad)

Let's do adjunctions with profunctors.

Recall Yoneda in profunctor category
forall p. Profunctor p => (forall x y. q x y -> p x y)
                       -> (forall x y. r x y -> p x y)
~= (forall x y. r x y -> q x y)

Replace p with U p

(Tambara profunctors have additional structure)
forall p. Tambara p => (forall x y. q x y -> (U p) x y)
                    -> (forall x y. r x y -> (U p) x y)
~= (forall x y. r x y -> ((U ∘ F) q) x y)

{ Specialize q and r }

q x y = (a -> x, y -> b)
r x y = (s -> x, y -> t)

   forall p . Tambara p => (U p) a b -> (U p) s t
~= ((U ∘ F) q) s t

{ Applying Yoneda, let U be a forgetful functor }

forall p. Tambara p => p a b -> p s t ~= (ϕ q) s t
\___________________________________/
 |
 +- Exactly what needed to combine lenses and prisms.

What is ϕ?  Well, since U and F are adjoint, this means the
composition (U ∘ F) is a monad ϕ.  What is this monad ϕ?  There is a
paper https://arxiv.org/pdf/0711.1859.pdf on this.

As Bartosz describes it,

(ϕ q) s t = ∫ c x y A(s, c ⊗ x) ⊗ A(c ⊗ y, t) ⊗ q x y

{ translating math to Haskell }

(Phi q) s t = exists c x y. ((s -> c ⊗ x, c ⊗ y -> t), q x y)

{ instantiate q, Yoneda }
q x y = (a -> x, y -> b)

(Phi q) s t = exists c. (s -> c ⊗ a, c ⊗ b -> t)

-}

type Lens s t a b = forall p. Strong p => p a b -> p s t
-- Lens s t a b = exists c. (s -> (c ,a) , (c, b) -> t)

type Prism s t a b = forall p. Choice p => p a b -> p s t
-- Prism s t a b = exists c. (s -> Either c a, Either c b -> t)

type Iso s t a b = forall p. Profunctor p => p a b -> p s t

class Profunctor p => Strong p where
  first' :: p a b -> p (a, c) (b, c)

class Profunctor p => Choice p where
  left' :: p a b -> p (Either a c) (Either b c)

-- class Profunctor p => Tambara p where
--   left'' :: p a b -> p (a ⊗ c) (b ⊗ c)

