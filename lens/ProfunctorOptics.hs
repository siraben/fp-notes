{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes, TypeOperators, NoMonomorphismRestriction #-}
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

-- Now we generalize to a useful lens library thanks to phadej's post
-- http://oleg.fi/gists/posts/2017-04-18-glassery.html

-- An Optic for a profunctor p.
type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a -- Simple (Optic p) s a

-- Lens s t a b = exists c. (s -> (c, a), (c, b) -> t)
-- newtype Lens s t a b = Lens (forall p. Strong p => p a b -> p s t)
type Lens s t a b = forall p. Strong p => Optic p s t a b

-- Prism s t a b = exists c. (s -> Either c a, Either c b -> t)
type Prism s t a b = forall p. Choice p => Optic p s t a b

type Iso s t a b = forall p. Profunctor p => Optic p s t a b

class Profunctor p => Strong p where
  first' :: p a b -> p (a, c) (b, c)

class Profunctor p => Choice p where
  left' :: p a b -> p (Either a c) (Either b c)

type Lens' s a = Lens s s a a

instance Strong ((->)) where
  first' f (a, c) = (f a, c)

instance Choice ((->)) where
  left' f (Left a) = Left (f a)
  left' g (Right a) = Right a

_1 :: Lens (a, c) (b, c) a b
_1 = first'

unLens l = l

newtype Const b a = Const { getConst :: b }
instance Functor (Const b) where
  fmap f (Const b) = Const b

modify :: Strong p => Lens s t a b -> p a b -> p s t
modify l f = l f

over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id

set :: Optic (->) s t a b -> s -> b -> t
set o s b = over o (const b) s

-- Composition of lenses
(>-) :: Lens s t a1 b1 -> Lens a1 b1 a2 b2 -> Lens s t a2 b2
ll >- rr = ll . rr

{-
λ> view (_1 . _1) ((1,2),3)
1
λ> set (_1 . _1) ((1,2),3) 5
((5,2),3)

-}
newtype Re p s t a b = Re { runRe :: p b a -> p t s }

-- Covariant bifunctor
class Bifunctor p where
    bimap :: (a -> b) -> (c -> d) -> p a c -> p b d
    bimap f g = first f . second g

    first :: (a -> b) -> p a c -> p b c
    first f = bimap f id

    second :: (b -> c) -> p a b -> p a c
    second = bimap id

    {-# MINIMAL bimap | (first, second) #-}

-- Contravariant bifunctor
class Bicontravariant p where
    cimap :: (b -> a) -> (d -> c) -> p a c -> p b d
    cimap f g = cofirst f . cosecond g

    cofirst :: (b -> a) -> p a c -> p b c
    cofirst f = cimap f id

    cosecond :: (c -> b) -> p a b -> p a c
    cosecond = cimap id

    {-# MINIMAL cimap | (cofirst, cosecond) #-}

instance Profunctor p => Profunctor (Re p s t) where
    dimap f g (Re p) = Re (p . dimap g f)

instance Bifunctor p => Bicontravariant (Re p s t) where
    cimap f g (Re p) = Re (p . bimap g f)

instance Bicontravariant p => Bifunctor (Re p s t) where
    bimap f g (Re p) = Re (p . cimap g f)


type Getter s a = forall p. (Bicontravariant p, Strong p) => Optic' p s a

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens gt st pab = dimap (\s -> (gt s, s))
                       (\(b, s) -> st s b)
                       (first' pab)

newtype Forget r a b = Forget { runForget :: a -> r }

instance Profunctor (Forget r) where
    dimap f _ (Forget p) = Forget (p . f)

instance Strong (Forget r) where
    first' (Forget p) = Forget (p . fst)

instance Bicontravariant (Forget r) where
    cimap f _ (Forget p) = Forget (p . f)

view :: Optic' (Forget a) s a -> s -> a
view o = runForget (o (Forget id))
