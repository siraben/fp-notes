# Impredicative polymorphism
Consider the following program, where `listF` is a list of polymorphic functions.

```haskell
{-# LANGUAGE RankNTypes, TypeApplications #-}

listF :: [forall a. a -> a -> a]
listF = [f, g]
  where
    f x y = x
    g y x = y

foo :: forall a. a -> a
foo x = case listF of
          (f:fs) -> f @a x x
          _ -> x
```

Such a program should typecheck, right?  GHC complains however:

```
impred.hs:4:10-32: error: …
    • Illegal polymorphic type: forall a. a -> a -> a
      GHC doesn't yet support impredicative polymorphism
    • In the type signature: listF :: [forall a. a -> a -> a]
```

This is because we instantiate the polymorphic type `a` in `[a]` with a qualified type, `forall a. a -> a -> a` in `listF`.  This is not allowed by GHC, see [this page](https://gitlab.haskell.org/ghc/ghc/-/wikis/impredicative-polymorphism).

However, the same example above will typecheck just fine in Coq:

```coq
Require Import List.
Import ListNotations.

Definition listF : list (forall (A : Type), A -> A -> A) :=
  let f (A : Type) (x y : A) := x in
  let g (A : Type) (x y : A) := y in
  [f;g].

Definition foo : forall (A : Type), A -> A :=
  fun (A : Type) (x : A) =>
    match listF with
    | f :: fs => f A x x
    | _ => x
    end.
```
