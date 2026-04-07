## Changes made to Idris

This section is to justify the hours working on something that is not strictly
my thesis work: Updates to the Idris compiler.

Working on a library for category theory puts some strain on the Idris compiler,
and made obvious some shortcomings in the languages that, if addressed, could
drastically improve the experience of using the language. Here are the features
I've designed and implemented.

### Customisable Parameter Arguments

Idris does not have first-class modules like OCaml or Agda, instead, it has a
number of features that provide approximatively the same features as a language
with first-class modules. _Parameter blocks_ are one of those, they allow to
define a block of code as being _parameterised_ by some arguments, and those
parameters are then automatically prefixing all the definitions in the block.

The old parameter block syntax allowed to give a list of arguments, and their
types but those arguments had to be explicit and could not have their quantity
changed. Declaring a parameter block with an erased implicit argument was
impossible.

```idris
parameters (arg1 : type1, arg2 : type2)
  -- definitions
```

This limitation was necessary to remove to write mathematical statements such as
"given two categories $\cat{C}$ and $\cat{D}$, and the fact that $cat{C}$is monoidal we have..."
because now the header of this definition can be held as parameter arguments and
the lemmas making use of them live in the body of the parameter block.

This statement can be written using the new parameter block syntax:

```idris
parameters {0 o1, o2 : Type}
           (c : Category o1) (d : Category o2)
           {auto mon : Monoidal cat1}
```

And every definition in the body of the parameter block now assumes the presence
of two types for objects `o1`, `o2`, two categories `c`, `d` and an
implicit proof that `c` is monoidal.

### Binding Operators & Binding Application

Working with dependent types reveal some unique challenges, because types also
contain programs, one of those challenges is to write types containing
lambda-expressions. Those types are surprisingly common in dependent types
theories, not least of which $\Pi : (t : \Type) \to (t \to \Type) → \Type$ and $Σ : (t :
\Type) \to (t \to \Type) \to Type$ both contain a function as their second argument.

$\Pi$-types enjoy special syntactic treatment in Idris, the term, written in
mathematical syntax, $\Pi\ \textit{Nat}\ (\lambda \textit{x} . \textit{Vect x String})$ is written
`(x : Nat) -> Vect n String`, where the binding of `x` is done using this
special bracketing syntax, rather than with a lambda. Without special syntax,
$\Pi$-types would have to be written something like this
`Pi Nat (\x => Vect x Nat)` which is much less pleasant.

$Σ$-Types also enjoy special syntax in Idris, instead of writing `Sigma Nat (\x
=> Vect x String` one can write `(x : Nat ** Vect x String)` where again, the
binding is handled by the special `(_ : _ ** _)` syntax.

$\Pi$ and $Σ$ types are far from being the only types requiring a function
binding an argument, the main definiton of this thesis, the `Container` type
also binds their second argument to the first:

```idris
record Container where
  constructor MkCont
  base : Type
  fibre : base -> Type
```

But the above program can only instanciate containers with the generic lambda
syntax `MkCont Nat (\x => Vect x String)`. Wouldn't it be nice if one could
write `MkCont (x : Nat) | Vect x String`, or as an infix operator
`(x : Nat) ▷ Vect x String` ? That's what binding application and binding
operators are for.

With this feature, any function or operator can be defined as `binding`, for
example the above `Container` can be written.

```idris
record Container where
  typebind
  constructor MkCont
  base : Type
  fiber : base -> Type
```

And this allows the constructor `MkCont` to be used with binding syntax :

```idris
example : Container
example = MkCont (x : Nat) | Vect x String
```

This syntax is particularly well suited to alternative sigma-types such as
`Exists` and `Subset` since writing `Exists (x : Nat) | Vect x String` reads
naturally as "there exists `x` with type `Nat` _such that_ we have a vector of
length `x` storing strings".

Additionally, operators can be defined as binding for infix use, for example we
can define another `(*)` operator that is binding for our own $Σ$ type:

```idris
typebind infixr 0 *

record (*) (t : Type) (s : t -> Type) where
  constructor (&&)
  p1 : t
  p2 : s p1

sigmaExample : Type
sigmaExample = (x : Nat) * Vect x String
```

There is another form of binding allowing more flexible use of the syntax,
`typebind` makes sure that the type of the function is always `(t : Type) -> (t
-> Type) -> s` but there are binding structures where the syntax would be useful
that do not follow this pattern. For example writing a programming language with
dependent types one could define a type constructor for $\Pi$:

```idris
VPi : Value -> (Value -> Value) -> Value
```

But using it to write terms in this language can be challenging:

```idris
sig : Value
sig = VPi VStar                 (\fstTy => VPi
      (VPi fstTy (const VStar)) (\sndTy => VPi
      fstTy                     (\val1 => VPi
      (sndTy `vapp` val1)       (\val2 =>
      VSigma fstTy sndTy)))))
```

Using `autobind` the above can be written much more naturally:

```idris
sig : Value
sig =
    (fstTy <- VStar) =>>
    (sndTy <- (_ <- fstTy) =>> VStar) =>>
    (val1 <- fstTy) =>>
    (val2 <- sndTy `vapp` val1) =>>
    VSigma fstTy sndTy
```

The syntax `(_ <- _)` indicates a binder which does not constraint the type of
the right side of the operator. It is meant to ressemble `let` binding because
it can be used as such:

```idris
linearProg : LIO ()
linearProg
  = Bind1 (x <- getline1)
  | Let1 (args <- words x)
  | Let1 (counts <- map length args)
  | putStrLn (unwords $ map show counts)
```

As a replacement for `do-notation` in the presence of linear
arguments[^linearDo] .

Additionally, `autobind` can also be used for replicating imperative-looking
code, for example we can define `for` as `autobind` and obtain a syntax that
very much looks like an imperative for-loop.

```idris
autobind
for : Applicative m => List a -> (a -> m n) -> m ()
for = flip traverse_

main : IO ()
main = for (x <- [0 .. 10]) | do
       input <- readLine
       printLn ("\{show x} : \{input}"
```

### Namespaced Fixity Declarations

Because this project made extensive use of custom operators, it revealed some weakness in the
design of operator fixity and precedence declaration.

To declare operators, it is not enough to use operator symbols for a function's
name. One also needs to define a matching _fixity_ declaration[^fixity]. They allow to define an
operator's associativity and precedence. For example a non-associative operator with precedence
9 is defined as `infix + 9`.

Those declaration
were originally entirely global and would shadow each other without warning. This
lead to interesting bugs where the same code would parse differently depending
on what modules were imported. While this is a desirable feature when implementing
a DSL, the fact that there was not mechanism to control that behaviour was problematic.

The sitiation was as follow. First we define a module `A` and `B` with  fixity declaration
in each

```
module A

infixl - 5
```

```
module B

infixr - 5
```

Then we import both in a third module and define a function that matches the given fixity

```
module C

import A
import B


main : IO ()
main = printLn (10 - 5 - 3)
```

Depending on the order the modules were imported, the expression `a + b + c` would
either parse as `(a + b) + c` or as `a + (b + c)` without any indication of what fixity
declaration the compiler would pick.

To address this issue, _Namespaced Fixities_ combine multiple features:
- Control if fixity declarations are allowed to escape the modules in which they are defined.
- Provide helpful error messages when conflicting fixities are present in the same module.
- Allow to selectively hide fixity declarations by selecting them through their namespaces.

To control if a fixity is allowed to escape the scope of its namespace, one can use the keywords
`export` or `private`. Where previously one could only write `infix + 9` without the ability
to keep this definition local, one can now write `private infix + 9` to ensure this declaration
remains in the current namespace.

To see the new messages we reproduce the above scenario, and get the following warning:

```
Warning: operator fixity is ambiguous, we are picking Prelude.Ops.infixl.(-) out of :
 - Prelude.Ops.infixl.(-), precedence level 8
 - A.infixl.(-), precedence level 5
 - B.infixr.(-), precedence level 5

To remove this warning, use `%hide` with the fixity to remove
For example: %hide Prelude.Ops.infixl.(-)

C:7:20--7:21
 3 | import A
 4 | import B
 5 |
 6 | main : IO ()
 7 | main = printLn (10 - 5 - 3)
                        ^
```

This message also teaches us about the last aspect of this feature: the ability to hide extranious
fixity declarations with the `%hide` directive followed by the namespace of the fixity to hide.

[^linearDo]: The current state of do notation with linear arguments is quite
    unsatisfactory and so relying on the user to carefully control the type of
    binding (linear, erased, unrestricted) results in much more reliable code.
[^fixity]:The term _fixity_ is borrowed by Haskell, where it denotes a similar feature.
