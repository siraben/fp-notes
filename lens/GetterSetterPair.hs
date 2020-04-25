-- A lens is a just a pair of getters and setters
data Lens a b = Lens { get :: a -> b
                     , set :: b -> a -> a }

_1 :: Lens (a, b) a
_1 = Lens fst (\a (_, b) -> (a,b))

-- Composition of lens
(>-) :: Lens a b -> Lens b c -> Lens a c
la >- lb = Lens (get lb . get la) setter
  where
    setter part whole  = set la (set lb part (get la whole)) whole

-- We can compose lenses
_ = _1 >- _1 :: Lens ((c, b1), b2) c

-- But this is clumsy, we can find a better encoding that will result
-- in lens composition as (.)
