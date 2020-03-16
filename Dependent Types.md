# Dependent Types

## Dependent functions
Consider the predecessor function on natural numbers.  What value
should it have for 0?  Suppose, for the sake of argument, we want to
return `false`.  Here's a first attempt.

```coq
Fail Definition dec (n : nat) :=
  match n with
  | 0 => false
  | S n' => n'
  end.

(*
The command has indeed failed with message:
In environment
n : nat
n' : nat
The term "n'" has type "nat" while it is expected to have type "bool".
*)
```

As every functional programmer knows, you can't have a function that
returns a `bool` in one case and returns `nat` in another, this isn't
Python!

We can compromise with a sum type.

```coq
Definition dec' (n : nat) :=
  match n with
  | 0 => inl false
  | S n' => inr n'
  end.

Check dec.
(* dec : nat -> bool + nat *)
```

But somehow this is unsatisfying.  We can't treat a dec'd number as a
number directly, leading to problems about theorems, for instance,
that a decrement undoes a successor.

```coq
Fail Theorem dec'Sn : forall n, dec' (S n) = n.
(*
The command has indeed failed with message:
In environment
n : nat
The term "n" has type "nat" while it is expected to have type
 "(bool + nat)%type".
*)
```

However, `forall n : nat, dec' (S n) = inr n` is easily solved by
reflexivity.

We can do better than this.  Coq provides a mechanism known as
_dependent pattern matching_.  This is nicely explained in Adam
Chlipala's _Certified Programming with Dependent Types_, [available
online](http://adam.chlipala.net/cpdt/html/MoreDep.html).

Whether a dependently typed language uses dependent pattern matching
or some other procedure to check when a function satisfies its
dependent type, is up to implementation.  Dependent pattern matching
is easier to implement and leads to better error messages.

In the following example, it looks like the ill-typed version except
for the `return match n with ... end` clause, which forms the
"dependent" part of the dependent pattern match.  We simply write a
Gallina expression stating that when `n` is `0`, return a value of
type `bool`, and when n is a successor of `n'`, return a value of type
`nat`.

```coq
Definition dec (n : nat) :=
  match n return match n with 0 => bool | S n' => nat end with
  | 0 => false
  | S n' => n'
  end.

Check dec.

(*
dec : forall n : nat, match n with
                      | 0 => bool
                      | S _ => nat
                      end
*)
```
And indeed, Coq shows us that `dec'` is indeed a dependent function,
one whose return type depends on the value of the argument.

Finally, we can prove that it indeed undoes succession of a natural
number.

```coq
Theorem decSn : forall n, dec (S n) = n.
Proof. reflexivity. Qed.
```

## Propositions as types
Proofs and programs.

### Equality as a type
Editors note: _would this be clearer in Agda?_

With dependent types, we are able to formulate equality as a type.
This is given below as the inductive type `equal`, which has a single
constructor, `equal_refl`.  It takes a type as its argument, then a
value of that type, producing a proposition, `equal A x x`, which
should be read as "`x` is equal to `x` under the type A".

```coq
Inductive equal (A : Type) (x : A) : A -> Prop := equal_refl : equal A x x.

Check equal_refl.

(*
equal_refl : forall (A : Type) (x : A), equal A x x
*)
```

To show it's really an equality, let's prove some properties about it,
namely that it's symmetric and transitive.
```coq
Theorem equal_sym : forall A (x y : A), equal A x y -> equal A y x.
Proof.
  intros A x y H.
  destruct H.
  exact (equal_refl A x).
Qed.

Theorem equal_trans : forall A (x y z : A), equal A x y -> equal A y z -> equal A x z.
Proof.
  intros A x y z H H0.
  destruct H, H0.
  exact (equal_refl A x).
Qed.
```

`equal_refl`, `equal_sym`, `equal_trans` together show that `equal` is
an [equivalence
relation](https://en.wikipedia.org/wiki/Equivalence_relation).

Finally, we show that we can use a proof that `x` equals `y` to
substitute `x` for `y` in any predicate `P`.

```coq
Theorem equal_cong : forall A (x y : A) (P : A -> Prop), P x -> equal A x y -> P y.
Proof.
  intros A x y P Px eqxy.
  destruct eqxy.
  exact Px.
Qed.
```

#### Equational reasoning, again

