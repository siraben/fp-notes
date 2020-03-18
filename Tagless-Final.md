# Tagless-Final
Some of my posts have used the
[tagless-final](http://okmij.org/ftp/tagless-final/course/lecture.pdf)
style, which isn't too well-known in the wider functional programming
community.  Indeed, as far as I know, you will not find it in
functional programming books.  It is a beautiful approach to solving a
difficult problem with extensibility of data types, and it works in
any language with "modular functors or constructor classes" (Kiselyov
et al., Finally tagless), but we will use Haskell here.  Familiarity
with Haskell's typeclasses is assumed.  We will present a series of
problems, each ending with how it's done in tagless-final.

## A simple arithmetic language
Let's write the language of arithmetic expressions and its
interpreter. We've all done this at some point, maybe it was an
exercise in a textbook, or a contrived example in a blog post.  We
continue the tradition of the latter here.

```haskell
data Exp = Lit Int
         | Neg Exp
         | Add Exp Exp

ti1 = Add (Lit 8) (Neg (Add (Lit 1) (Lit 2)))

eval :: Exp -> Int
eval (Lit n)     = n
eval (Neg e)     = negate (eval e)
eval (Add e1 e2) = eval e1 + eval e2
```

Let's write a pretty printer too.

```haskell
view :: Exp -> String
view (Lit n) = show n
view (Neg e) = "(-" <> view e <> ")"
view (Add e1 e2) = "(" <> view e1 <> " + " <> view e2 <> ")"
```

Let's see if it works.

```
λ> eval ti1
5
λ> view ti1
"(8 + (-(1 + 2)))"
```

So far so good, although we have `eval` and `view`, we're restricted
to only those functions to interpret `Exp` values into `Int` or
`String`.  Speaking from a semantics point of view, all `eval` and
`view` ever do is give us the mapping from `Exp` to a given semantic
domain (`Int` or `String`), by doing something different for each of
the constructors (`Lit`, `Neg`, `Add`).  So, why not skip the middle
man and parameterize `Exp`'s constructors in the semantic domain?
Haskell has exactly that mechanism, a _typeclass_.

## The final encoding
```haskell
-- Compare with GADT syntax
class ExpSYM repr where
  lit :: Int -> repr
  neg :: repr -> repr
  add :: repr -> repr -> repr

tf1 :: ExpSYM repr => repr
tf1 = add (lit 8) (neg (add (lit 1) (lit 2)))
```

`tf1` is an example term in this encoding.  It has the type `ExpSYM
repr => repr`, in other words, it's polymorphic in the semantic
domain!  Now that we have an encoding, a natural question to ask is
how to interpret this encoding---by writing instances.

```haskell
instance ExpSYM Int where
  lit = id
  neg = negate
  add = (+)
```

Let's try it out.

```
λ> tf1
tf1 :: ExpSYM repr => repr
λ> tf1 :: Int
5
```

Why didn't the first line do anything?  Well, `tf1` is a polymorphic
type, so we don't know _which_ type it is until we have some more
information!  All we know is that whatever type it _finally_ has is an
instance of `ExpSYM`.

So, by just saying we expected an `Int` in lieu of `ExpSYM repr =>
repr`, Haskell looks to see if `Int` is an instance of `ExpSYM`, finds
out it is and replaces `lit` with `id`, `neg` with `negate` and add
with `(+)`.  In effect, `tf1` is no different than the following
calculation.

```haskell
   tf1 :: ExpSYM repr => repr
-- { definition of tf1 }
 = add (lit 8) (neg (add (lit 1) (lit 2))) :: ExpSYM repr => repr
-- { Int is an instance of ExpSYM }
 = (+) (id 8) (negate ((+) (id 1) (id 2)))
-- { evaluation }
 = 5
```

We're imbuing `lit` `neg` and `add` with new meanings, depending on
the domain we are working in.  Let's try a different domain,
`String`.  As an example, we are now trying to figure out what
function to use for `lit :: Int -> String`.  We know such a function
exists, `show`.  In that sense, we are writing a pretty printer, so it
stands to reason that `add` and `neg` should behave similarly.

```haskell
instance ExpSYM String where
  lit = show
  neg e = "(-" <> e <> ")"
  add e1 e2 = "(" <> e1 <> " + " <> e2 <> ")"
```

So what happens when we try to interpret `tf1` as a string?  We get
its pretty printed output.

```haskell
   tf1 :: ExpSYM repr => repr
-- { definition of tf1 }
 = add (lit 8) (neg (add (lit 1) (lit 2))) :: ExpSYM repr => repr
-- { String is an instance of ExpSYM }
 = "(" <> show 8 <> " + " <> ("(-" <> ("(" <> show 1 <> " + " <> show 2
   <> ")")) <> ")"
-- { show, (<>) associative }
 = "(" <> "8" <> " + " <> "(-" <> "(" <> "1" <> " + " <> "2" <> ")" <> ")"
-- { evaluation }
 = "(8 + (-(1 + 2))"
```

Both examples are the embodiment of the phrase "seek and ye shall
find" --- as long as someone has written a typeclass instance for it.

So far, it doesn't seem like this encoding as a typeclass is
beneficial, if anything, it leaves us with questions such as comparing
terms for equality, or pattern matching, and performing nested pattern
matches.  Before we get to that, let's visit a problem of generic
programming, the expression problem.

## The expression problem
What happens if we want to add multiplication to our `Exp` data type?
In the initial encoding, all we need to do is add a new constructor;

```haskell
data Exp = ...
         | Mul Exp Exp
```

But now we have to traverse the entire codebase, to every place we
pattern matched on `Exp` and handle the new clause.  This also means
we have to recompile everything that touches `Exp` directly or
indirectly.  Somehow, a small change produces a global impact.  What
about in the final case?  Let's consider how types work in Haskell.
It's very common to see Haskell types that have one or more typeclass
constraints, for instance;

```
λ> \x -> show x <> show (x + 3)
it :: (Show a, Num a) => a -> String
```

In this example, `it` is a polymorphic function from `a` to `String`,
but the choice of `a` is restricted to numeric types (`Num`), and
showable types (`Show`).  So, why don't we add a new form by making a
new typeclass altogether?  Think of it as the "diff" for the
extensions we want to make.


```haskell
class MulSYM repr where
  mul :: repr -> repr -> repr

tfm1 = add (lit 7) (neg (mul (lit 1) (lit 2)))
tfm2 = mul (lit 7) tf1
```

Hold on, we are combining `MulSYM` and `ExpSYM` methods freely?  This
is no different than using `x` in `\x -> show x <> show (x + 1)` as
something that can be shown and something can be incremented.  So the
types of `tfm1` and `tfm2` similarly have multiple constraints;

```haskell
tfm1, tfm2 :: (ExpSYM repr, MulSYM repr) => repr
```

And now we interpret `MulSYM` in the domain of `Int` and `String`.

```haskell
instance MulSYM Int where
  mul = (*)
instance MulSYM String where
  mul e1 e2 = "(" <> e1 <> " * " <> e2 <> ")"
```

The beauty is that these extensions are separate from the old code.
Additionally, suppose we had forgotten to write the `MulSYM String`
instance, then attempting to interpreter `tfm1` in the domain of
`String` will raise a type error.

Let's see it in action.

```haskell
   tfm1 :: (ExpSYM repr, MulSYM repr) => repr 
-- { definition of tfm1 }
 = add (lit 7) (neg (mul (lit 1) (lit 2))) :: (ExpSYM repr, MulSYM repr) => repr 
-- { Int is an instance of ExpSYM, MulSYM }
 = (+) (id 7) (negate ((*) (id 1) (id 2)))
-- { evaluation }
 = 5
```

## Pattern matching in the final approach
`eval` and `view` were straightforward to translate, but what if we
have a transformation of `Exp` values that cannot be expressed a fold?
For instance, here is a transformation to bubble negation down to the
leaves, and perform double negation elimination.

### Pushing negation down: initial approach
Nested pattern matching makes pushing negation down a piece of
cake.  When we encounter an addition happening inside a negation,
distribute the negation to both sides of the addition, and recur.
When a double negation is found, eliminate it.

```haskell
pushNeg :: Exp -> Exp
pushNeg e@(Lit _)       = e
pushNeg e@(Neg (Lit _)) = e
pushNeg (Neg (Neg e))   = e
pushNeg (Neg (Add e1 e2)) = Add (pushNeg (Neg e1)) (pushNeg (Neg e2))
pushNeg (Add e1 e2) = Add (pushNeg e1) (pushNeg e2)
```

```
λ> view (pushNeg (Neg ti1))
"((-8) + (1 + 2))"
```

### Pushing negation down: final approach
We achieve the seemingly impossible, pushing negation down in the
final approach.  We can realize this because when we encounter a
negation, we are changing the _context_, which can be positive or
negative.  In either case, we flip the context.  When we encounter an
add, just push negation down to both branches, preserving the context.

```haskell
data Ctx = Pos | Neg

instance ExpSYM repr => ExpSYM (Reader Ctx repr) where
  lit n = do ctx <- ask
             pure $ case ctx of
                      Pos -> lit n
                      Neg -> neg (lit n)
  neg e = local flipCtx e
    where flipCtx Pos = Neg
          flipCtx Neg = Pos
  add e1 e2 = add <$> e1 <*> e2
```

And we get the result we desire.

```
λ> runReader tf1 Neg :: String
"((-8) + (1 + 2))"
```

Notice that, in the final equation, we are defining `add` for `Reader
Ctx repr` given that `repr` is an instance of `ExpSYM`, so the `add`
you see on the right hand side is the `add` acting on `repr` values.

```haskell
instance ExpSYM repr => ExpSYM (Reader Ctx repr) where
  ...
  add e1 e2 = add <$> e1 <*> e2
```


## The problem of tags
What about more complicated domains, such as writing a typed object
language and its interpreter?  Let's make a simple language with
variables (represented by its unary Debruijn index), booleans, lambda
abstractions and application.

```haskell
data Var = VZ | VS Var
data Expr = V Var | B Bool | L Expr | A Expr Expr

resolve :: [a] -> Var -> a
resolve (x:env) i = case i of
                     VZ -> x
                     VS v -> resolve env v

eval (V v) env = resolve env v
eval (B b) env = b
eval (L e) env = \x -> eval e (x:env)
eval (A e1 e2) env = (eval e1 env) (eval e2 env)
```

Uh oh, but this fails.  Why does it fail?  The return type of `eval`
is different from one equation to the next!  When we try to evaluate a
boolean, we return something of type `Bool`, but when we evaluate a
lambda, we return a function!

OK, but we know how to handle this in Haskell, just wrap the different
return types into a single type, `Val`, representing the type of
values in our language.

```haskell
data Val = VB Bool | VA (Val -> Val)

eval :: [Val] -> Expr -> Val
eval env (V v) = resolve env v
eval env (B b) = VB b
eval env (L e) = VA (\x -> eval (x:env) e)
eval env (A e1 e2) = case eval env e1 of
                       VA f -> f (eval env e2)
```

Yay, it typechecks.  However, `eval` is actually a partial function
now, consider the expression `(A (VB True) (VB False))`, and let's try
to evaluate it. (we use `seq` to force evaluation.)

```
λ> eval [] (A (B True) (B False)) `seq` 1
*** Exception: Non-exhaustive patterns in case
```

Where did the match fail?  In the last pattern match for `eval`, there
was a `case` statement that only handled the happy case that in an
application, the first expression evaluates to a function, in this
case `VA`.  But obviously `(B True)` will not evaluate to `VA ...`, so
the match fails.

We could try to resolve this by making `eval` return some sort of
`Either` type, but that doesn't help the fact that the type tag
checking is still being performed.  In fact, we want to be able to
make ill-typed terms in our object language _unrepresentable_ in the
metalanguage.

Let's turn to GADTs for solace.

```haskell
data Var env t where
  VZ :: Var (t, env) t
  VS :: Var env t -> Var (a, env) t

data Exp env t where
  B :: Bool -> Exp env Bool
  V :: Var env t -> Exp env t
  L :: Exp (a, env) b -> Exp env (a -> b)
  A :: Exp env (a -> b) -> Exp env a -> Exp env b

ti1 :: Exp env Bool
ti1 = A (L (V VZ)) (B True) -- represents ((\x -> x) True)
```

Now, we can write the interpreter that we would have liked to have
written earlier on.

```haskell
eval :: env -> Exp env t -> t
eval env (V v) = lookp v env
eval env (B b) = b
eval env (L e) = \x -> eval (x, env) e
eval env (A e1 e2) = (eval env e1) (eval env e2)
```

Finally, we need to define how to look something up in the
environment. `lookp` traverses a nested tuple with a de Bruijn
variable until `VZ` is reached.  Note that it becomes impossible to
reference something with a de Bruijn index larger than the
environment, because of the types of `VZ` and `VS`.

```haskell
lookp :: Var env t -> env -> t
lookp VZ (x,_) = x
lookp (VS v) (_, env) = lookp v env
```

We try evaluating both closed and open terms.  In the last example, we
try to apply `False` to `True`, which fails the typecheck.  Notice
that evaluating an open term in the empty environment leads to a type
error, but add something to the environment and it works.  This is a
very strong _static_ guarantee, only well-typed terms can be
represented!

```
λ> eval () (A (L (V VZ)) (B True))
True
λ> eval () (A (L (V (VS VZ))) (B True)) -- an open term w/ empty env
<type error>
λ> eval (False, ()) (A (L (V (VS VZ))) (B True)) -- open term w/ env
False
λ> eval () (A (B False) (B True)) -- applying False to True
<type error>
```

## References
This post was heavily inspired by Oleg Kiselyov's papers on
tagless-final.

[Tagless-final style](http://okmij.org/ftp/tagless-final/index.html)
[Typed tagless final interpreters](http://okmij.org/ftp/tagless-final/course/lecture.pdf)
