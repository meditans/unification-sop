# unification-sop

This is a haskell package that implements typed terms with logical variables in
a prolog-style.

Consider the datatype:

``` haskell
data Foo = FooI Int | FooS String Foo

exFoo1, exFoo2 :: Foo
exFoo1 = FooI 3
exFoo2 = FooS "hey" (FooI 4)
```

With this library you can express terms like:

``` haskell
exTermFoo1, exTermFoo2, exTermFoo3 :: Term Foo
exTermFoo1 = fooI (Var 1)                    -- prolog: fooI(X)
exTermFoo2 = fooR (Var 1) (fooI (Var 1))     -- prolog: fooR(X, fooI(Y))
exTermFoo3 = fooR (Con "hey") (fooI (Var 1)) -- prolog: fooR ("hey", fooI(X))
```

`exTermFoo1` would be written in prolog as `fooI(X)`, and `exTermFoo2` as
`fooR(X, fooI(Y))`, because, since the variables are typed, `Var 1` has type
`String` in the first case and `Int` in the second.

You can find more information in the (WIP) tutorial, or see the haddock
documentation.

### A quick survey of the organization of the code:

- Generic.Unification.Tutorial

    Here I wrote a more complete version of the ideas expressed in the prologue
    of this package.

- Generic.Unification.Term

    Here I define the Term datatype, which is the structure that lets us express
    the `term with holes` idea.
    
- Generic.Unification.Substitution

    Here we define a concept of substitution, which is essentially a map from
    variables to terms, except that in our case the variables are all typed, so
    that a substitution is denotationally a map from `(a :: Type, var :: a) ->
    Term a` (using a notation borrowed from dependent types).
    
- Generic.Unification.Unification

    Here we implement the quite fast unification algorithm described in
    Efficient functional Unification and Substitution` by A.Dijkstra (and used
    for example in his EHC haskell compiler).

- Generic.Unification.Hinze

    Here we write a complete prolog (with cut) using the machinery defined in
    the other modules, and following the paper "Prolog control constructs in a
    functional setting" by Hinze, augmented with explicit logical variables.
    This is an experimental module meant to demonstrate a possible use of the
    package, and will probably be removed in the future.

### FAQ
- Why do you want to use logical variables when you can instead use a purely
monadic representation indicating logic computation, like the one in Hinze's
paper?

    My tentative answer is that I sometime use logical variables to structure
    data (think graphs) so that I can use unification to quickly prototype
    algorithms.

### Contributing

I wrote this package as a proof of concept for another package I needed (and
it's closed source for now) which uses the same mechanism but instead of
manually implementing unification delegates that part to the z3 solver. As I'm
using the new one I don't plan on improving this one much further, but if you
have suggestions, want me to develop some feature, or want to send me a patch,
please open an issue here on github: all issues are very welcome :)
