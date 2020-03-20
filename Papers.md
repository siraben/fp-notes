# Papers

## Landmark Papers

John McCarthy, “Recursive Expressions and Their Computation By Machine,
Part 1”.  Communications of the ACM, vol. 3, no. 4 (1960).
[PDF available](http://www-formal.stanford.edu/jmc/recursive.pdf)

The paper in which McCarthy describes LISP, and introduces several
ideas that became fundamental to the implementation of functional
languages, including garbage collection.

Guy L. Steele, Jr., “Debunking the ‘Expensive Procedure Call’ Myth, or,
Procedure Call Implementations Considered Harmful, or, Lambda: The
Ultimate GOTO”.  MIT AI Memo 443, 1977.
[PDF available](https://dspace.mit.edu/bitstream/handle/1721.1/5753/AIM-443.pdf?sequence=2&isAllowed=y)

Steele shows that the notion that functional programming languages are
impractically slow is pure myth.

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

Philip Wadler, “How To Replace Failure By a List Of Successes”.
Proceedings of a conference on functional programming languages and
computer architecture, 1985.
[PDF available.](https://rkrishnan.org/files/wadler-1985.pdf)

Wadler introduces a classic functional pearl.  He shows how a
“stream-processing” technique can be used to solve problems that would
traditionally be handled with backtracking.
 
John Hughes, “Why Functional Programming Matters”.  The Computer
Journal, 1989.
[PDF available.](https://www.cs.kent.ac.uk/people/staff/dat/miranda/whyfp90.pdf)

An accessible argument for functional programming, and also a nice
introduction to the subject.  For Hughes, the power of FP lies in
its *compositionality*--the property that allows us to build up
functional programs from tiny, reusable pieces.

Philip Wadler, “Monads For Functional Programming”
In Manfred Broy, *Program Design Calculi*.  Springer, 1993.
[PDF available](https://homepages.inf.ed.ac.uk/wadler/papers/marktoberdorf/baastad.pdf)

The paper which introduced monads as a major unifying concept in
functional programming.  Wadler’s elegant presentation makes this idea
seem simple and natural.

Conor McBride and Ross Paterson, “Applicative Programming With
Effects”.  Journal Of Functional Programming, 2008.
[PDF available.](http://www.staff.city.ac.uk/~ross/papers/Applicative.pdf)

The paper that introduced applicative functors, AKA “idioms”, to
functional programming.


## Compilation

Patrick Bahr and Graham Hutton, “Calculating Correct Compilers”.
Journal Of Functional Programming, 2015.
[PDF (preprint) available.](http://www.cs.nott.ac.uk/~pszgmh/ccc.pdf)

Bahr and Hutton show how to write a compiler for a small language
using program calculation exclusively.  Draws together much of
Hutton’s earlier work on the topic of compiler calculation and
verification.
