# Equational Reasoning
One of the greatest strengths of FP is being able to reason
about programs in an equational manner, a common proof technique in
mathematics.  This is amplified by having a pure functional language,
allowing us to perform rewrites without the side condition that
functions must not be effectful.

## Booleans and double negation
```haskell
data Bool = True | False

not :: Bool -> Bool
not True = False
not False = True
```

We can treat the equality sign literally, replacing the left hand side
of the equality for the right hand side in any context, and vice versa.

Let's prove that `not (not b) = b`.

```
   not (not b)
Case 1: b = True
   not (not True)
= { equation 1 of not }
   not False
= { equation 2 of not }
   True
Case 2: b = False
   not (not False)
= { equation 2 of not }
   not True
= { equation 1 of not }
   False

Therefore, forall b : Bool, not (not b) = b.
```

This is an example of proof by cases, where we exhaustively enumerate
all the constructors for a given type and show that the proposition
holds, therefore it holds for all values of the constructor.

### Exercises
Define the binary functions `and, or :: Bool -> Bool -> Bool` and
prove de Morgan's laws;

```
1. forall a b : Bool, not (and a b) = or (not a) (not b)
2. forall a b : Bool, not (or a b)  = and (not a) (not b)
```

## Reasoning about recursive types
TODO: structural induction

### List Append
```haskell
data [a] = [] | a : [a]

infixr 5 ++
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : xs ++ ys
```

TODO: append associative, reverse, reverse correct
