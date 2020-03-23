# Papers

## Landmark Papers

John McCarthy, “Recursive Expressions and Their Computation By Machine,
Part 1”.  Communications of the ACM, vol. 3, no. 4 (1960).
[PDF](http://www-formal.stanford.edu/jmc/recursive.pdf)

The paper in which McCarthy describes LISP, and introduces several
ideas that became fundamental to the implementation of functional
languages, including garbage collection.

---

Guy L. Steele, Jr., “Debunking the ‘Expensive Procedure Call’ Myth, or,
Procedure Call Implementations Considered Harmful, or, Lambda: The
Ultimate GOTO”.  MIT AI Memo 443, 1977.
[PDF](https://dspace.mit.edu/bitstream/handle/1721.1/5753/AIM-443.pdf?sequence=2&isAllowed=y)

Steele shows that the notion that functional programming languages are
impractically slow is pure myth.

---

John Backus, “Can Programming Be Liberated from the von Neumann Style?”
Communications of the ACM, vol. 21, no. 8 (1978).

Backus’s 1977 Turing Award lecture presents the “FP” language and
makes a detailed, insightful argument for functional programming.
Includes discussion on “the Algebra of Programs”, in which programs
are manipulated via algebraic laws.  Calling this algebra “a game
amateurs can profitably play and enjoy”, Backus proves a handful of
theorems and shows how they can be used to prove the correctness of
larger FP programs.  This paper is so rich that it’s hard to believe
it was presented as a lecture.

---

Philip Wadler, “How To Replace Failure By a List Of Successes”.
Proceedings of a conference on functional programming languages and
computer architecture, 1985.
[PDF](https://rkrishnan.org/files/wadler-1985.pdf)

Wadler introduces a classic functional pearl.  He shows how a
“stream-processing” technique can be used to solve problems that would
traditionally be handled with backtracking.  This is done by
representing multiple return values with a list, where the empty list
denotes failure.  Nondeterministic choice `OR` can be encoded as list
append, `(or p q) x = p x ++ q x`, and conjunction `AND` is encoded as
cartesian product.  A recursive descent parser is demonstrated.

It´s interesting to note the parallels between this work and later
work on monads.  A monad with a failure is encapsulated by the
`MonadZero` typeclass, a monad with choice is encapsulated by
`MonadPlus`.  Applying a function to a list of nondeterministic values
is `fmap` on lists.

---

John Hughes, “Why Functional Programming Matters”.  The Computer
Journal, 1989.
[PDF](https://www.cs.kent.ac.uk/people/staff/dat/miranda/whyfp90.pdf)

An accessible argument for functional programming, and also a nice
introduction to the subject.  For Hughes, the power of FP lies in
its *compositionality*--the property that allows us to build up
functional programs from tiny, reusable pieces.

---

Philip Wadler, “Monads For Functional Programming”
In Manfred Broy, *Program Design Calculi*.  Springer, 1993.
[PDF](https://homepages.inf.ed.ac.uk/wadler/papers/marktoberdorf/baastad.pdf)

The paper which introduced monads as a major unifying concept in
functional programming.  Wadler’s elegant presentation makes this idea
seem simple and natural.

---

Conor McBride and Ross Paterson, “Applicative Programming With
Effects”.  Journal Of Functional Programming, 2008.
[PDF](http://www.staff.city.ac.uk/~ross/papers/Applicative.pdf)

The paper that introduced applicative functors, AKA “idioms”, to
functional programming.  Applicative functors correspond to the
`Applicative` typeclass.  `Monad` is a subset of `Applicative`, and
`Applicative` is a subset of `Functor`, thus `Functor`, `Applicative`
and `Monad` form a hierarchy of abstractions.  `Functor` and `Monad`
correspond to concepts from category theory, and the paper elaborates
on the connection between `Applicative` and strong lax monoidial
functors.

## Functional Pearls
Graham Hutton and Erik Meijer, “Monadic Parsing in Haskell”.  Journal
of Functional Programming, 1998.

Combines three areas into a single 8-page work.  Namely, functional
parsers, using monads to structure functional programs, and
`do`-notation.  Provides a very elegant and compositional approach to
parsing that rivals imperative alternatives.  Treats parsers as
first-class citizens, including _parser combinators_, higher-order
functions that allow one to repeat a parser, or select between
alternative parsers for choice, sequencing, and more.

---

Wouter Swierstra, “Data types à la carte”.   Journal of functional
programming, 2008.
[PDF](http://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf)

The paper presents a solution to the expression problem, that is,
extending a data type without recompiling existing code while
retaining type safety. _Data types à la carte_ expresses effects as
algebras and interpretations as folds over that algebra.  A stateful
calculator and `Teletype` and `Filesystem` examples are presented,
along with how they can be freely combined.

Oleg [published a
comparsion](http://okmij.org/ftp/Haskell/extensible/extensible-a-la-carte.html)
of the paper and his own work on Extensible Effects.  Swierstra´s
construction is unable to handle the addition of new effects, as it
was not extensible.  Instead, Oleg redefines Swierstra's `Expr` as
`Term`, allowing for the interleaving of pure and impure computations,
regaining extensibility.

## Algorithms and Data Structures
Ralf Hinze and Ross Patterson, “Finger trees: a simple general-purpose
data structure”. Journal of Functional Programming, 2006.
[PDF](https://archive.alvb.in/msc/03_infoafp/papers/2012-12-18_WerkCollege_FingerTreesRalfHinze.pdf)

The paper presents a functional data structure, 2-3 finger trees,
allowing amortized constant time access to the ends, and concatenation
and splitting in time logarithmic to the smaller piece.  These bounds
have been achieved prior to the work, but 2-3 trees are much simpler.
By defining split operations generally, the data structure can be used
as a sequence, priority queue, search tree, priority search queue,
heap, interval tree, and more.  Changing how the split/merge works
corresponds to changing the underlying monoid (`Measured` typeclass),
unifying these data structures into a single monoidial framework.

## Compilation

Patrick Bahr and Graham Hutton, “Calculating Correct Compilers”.
Journal Of Functional Programming, 2015.
[PDF (preprint)](http://www.cs.nott.ac.uk/~pszgmh/ccc.pdf)

Bahr and Hutton show how to write a compiler for a small language
using program calculation exclusively.  Draws together much of
Hutton’s earlier work on the topic of compiler calculation and
verification.

## Haskell
The topic of these papers are concerned primarily with the purely
functional language Haskell.

### Type system
Oleg Kiselyov, Simon Peyton Jones, Chung-chieh Shan, “Fun with type
functions”.  Reflections on the Work of CAR Hoare, 2010.
[PDF](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/07/typefun.pdf)

This paper offers “a programmer´s tour of _type families_”, a Haskell
feature implemented in GHC.  It begins with a refresher on the role of
types, and more advanced types, such as associated types.  In Haskell,
we can _type constructors_, or _type functions_ as they are called in
this paper, such as `[] :: * -> *`.  A type function can be fully
applied to a type, yielding another type, or partially applied,
yielding another type constructor, (`[] Int` becomes `[Int]`).

The paper demonstrates arithmetic with implicit type “coercion”, data
structures with the same interface but possibly different
implementations, and optimized container representations (reminiscent
of using C++ meta-programming to optimize certain structures into more
memory efficient versions).  It then builds up to talk about building
memoization tables (with references to generics), then session types.
This allows for a client/server view of programming.  A type-safe solution to
the formatted `printf` and `scanf` functions is presented.

The last section elaborates phantom types--applying them to the
problem of statically guaranteeing pointers are aligned, and
parametrized monads.  As an example, we can have computations that use
a certain number of resources (in the concurrent sense) and is
statically guaranteed to not leave resources acquired, or acquire the
same resource twice.  Finally, the data kinds feature is demonstrated
to make type-level programming itself typed.


