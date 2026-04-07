# About Idris

To fully grasp the content of this document, it is important to knowledge of the formalisation tool used: Idris. Although, a lot of this text is written with references to Haskell or Agda, due to the intended audience being thesis reviewers rather than students or programmers.

## Language features

Idris is good at matching expectations with regards to the runtime performance of programs. Both the javacript[^fastJS] and the Chez backend
are fast, the implementation of QTT makes erasure reliable and easy to use, the strict
semantics of the code makes performance predictable in a way that matches the intuition of most commercial programming
languages. Most importantly, Idris has a fully featured package manager and a number of binding to important libraries to write
software, like networking, user interfaces, web servers, databases and more.

Idris is _not_ well known for its theorem proving capabilities. It is, in the mind of the community members I've talked to, something
it _can_ do but is not _designed_ to do.

- [ ] find quote about this

I don't think I can pretend that I'm able to change the mind of people who came to this
conclusion, but I think I can shed light into what makes Idris a _different_ experience than Agda when proving theorems.

### Data Declarations

Before we write any program we need to define types and their inhabitants. We make use of two ways of defining them: `data` declarations and `record` declarations.

`data` declarations take a type signature for the type constructor and is followed by a list of constructor with their own type signature. Here is an example of a `data` declaration for the predicate transformer `All` ensuring a predicate holds for all elements of a list.

```idris
data All : (a -> Type) -> List a -> Type where
    Nil : All p []
    (::) : p x -> All p xs -> All p (x :: xs)
```

Unlike Agda, there is no difference between an _index_ or a _parameter_, therefore, we are not going to concern ourselves with the difference between them when programming.

`record` declarations are like `data` declarations with a single constructor. They provide a familiar and ergonomic way to bundle multiple types in a product under a familiar name. For example one can define a type `User` with various fields that the records hold to fully characterise a user.

```idris
record User where
  constructor MkUser
  name : String
  birthdate : Date
  friends : List User
```

In this work, we are going to predominantly use them to define types that collect functions and properties about those functions. In the following example we define the type `Monad` as a type parameterised by a functor `f`, a constructor `MkMonad`, two fields for the functions `unit` and `mult` and two fields for proofs about them.

```
record Monad (f : Type -> Type) {auto _ : Functor f} where
  constructor MkMonad
  unit : a -> f a
  mult : f (f a) -> f a
  multOk : (x : f (f (f a))) -> (mult (mult x)) === mult (map mult x)
  unitOk : (x : f a) -> mult (unit x) === mult (map unit x)
```



### Case Statements

Much like Haskell, Idris has `case` statements that allow to pattern match on a value as part of an expression.
This has multiple benefits as it allows to match directly on argument on a lambda without having to lift an expression
to the top-level like would be required in Agda

- [ ] example of case

This can be further simplified with the used of lambda-case

- [ ] example of lambda-case

One issue with `case` is that expresions get stuck when they appear in a type, and require either to replicate the case-expression at use-site, or lift the `case` statement in its own helper function like in Agda.

### Type-In-Type

Idris has type-in-type, which means it is suseptible to Girard's paradox. While there is no technical reason
preventing Idris from having universe levels or cumulativity, there is a social reason. Idris does not have
any fulltime maintainer and the cost of labour of implementing cumulativity is disproportionally greater than
its payoff when compared to other more pressing issues in the language. Type-in-Type has therefore been a long standing to-do item. Being aimed primarily at software engineering, this particular aspect of Idris has not been the source of a lot of demand.

### Let-binding

Let bindings come in two forms in Idris: Lifted binding and inlined binding.

And inlined binding is what you would expect from most programming languages, it binds a value to a name and
the name can be reused multiple times without recomputing the value:

```
let x = 3 * 7*
in x + x
```

This however causes issues when writing proofs, because inlined binder are not evaluated in expressions, to
be consistent with the runtime semantics of the program

*place example of proof that fails because of a let binder*

This is where lifted binding come up. To tell Idris that it's ok to evaluate a bound expression multiple times
one can write it in the same way they would write top-level definitions:

```
main = let x : Nat
           x = 3 * 7
       in printLn (x + x)
```

The `x` binder will now be lifted into a top-level definition and behave like a function being called multiple times.

```
x : Nat
x = 3 * 7

main = printLn (x + x)
```

This might not be what you want for runtime performance reasons but when you are writing proofs, then each
occurrence of `x` will be substituted by its implementation, enabling some proofs to evaluate down to simpler
statements. The fact that `x` is evaluated multiple times has no impact on runtime performance since most
proofs are erased from the runtime.

### Unicode and Operators

Agda is notorious for its mixfix and unicode syntax. "Write-only" software is a meme often repeated to criticise the
fact that Agda code is often illegible to newcomers. Idris aims to provide a much more familiar experience by
implementing a syntax that looks like Haskell, albeit with single colons for types rather than double colon.  Of course
this is not to say that Idris code is immediately legible to a newcomer either. Quantity annotations, rules around
case, implicit resolution and arbitrary overloading easily confuse users, even when they are accustomed to Haskell. Like all discussions about syntax, there is no winner here, only opinions. And in my efforts to keep code as
enjoyable to read as possible, I've taken the best of both languages to write the code that you will see here, and
used my own fork of Idris with the following changes:

- Support for binding syntax, it enables the use of syntax like `(x : a) * b x` rather than `a * (\x => b x)`
- Support for a limited subset of unicode operators, in particular we use `⊗`, `▶`, `▷`, `⨾`, `×`, `≅`,  and `≡`.
- Change rules about capital letters to handle lower and upper-case greek letters.

Change involving unicode are directly inspired from Agda, and are going to remain private.
While bringing together the syntax of Idris and Agda has been helpful to me, I do not believe they are helping
 Idris become a more compelling programming language.

Binding operators are a public contribution to the language and are going to get their own section \ref{}

Regular operator come in four flavours `infix`, `infixl`, `infixr` and `prefix`. An `infix` operator is infix but does not associate to the left or right. Writing for example:

```idris
infix + 7

sum : Nat
sum = 3 + 4 + 5
```

Results in a parse error because the operator is marked as `infix` and does not associate to the right or the left, the user needs to write a valid parenthesisation of the expression to have it parse. `infixl` and `infixr` are infix operators that associate to the left such that the above expression parses as `(3 + 4) + 5` for `infixl` and `3 + (4 + 5)` for `infixr`. `prefix` operators behave similarly to function application where the symbol is placed ahead of its arguments, but it will often require parenthesis whenever it is inserted in a larger expression. One of the benefits of prefix operators is that they can be chained with themselves. For example:

```
prefix ¬ 6

(¬) : Type -> Type
(¬) a = a -> Void

NotNot : Type -> Type
NotNot a = ¬ ¬ a
```

Parses as `¬ (¬ a)` which is exactly what was intended.

### Replace/Subst

The biggest difference in formalising containers and category theory, was that `replace` in idris is treated differently than `subst` in Agda. Here are their respective definitions.

```agda
-- agda
subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px
```

```idris
-- idris
replace : forall x, y, p . (0 rule : x = y) -> (1 _ : p x) -> p y
replace Refl prf = prf
```

`replace` states that
given a proof `x = y` and a predicate `p`, any value `p x` can be converted into a value `p y`.  The same function is called
`subst` in Agda and performs the same functionality. The difference lies in how the compiler evaluates those two expressions. While Agda is stuck for as long as the
proof is not `refl`, Idris will assume all proofs are `Refl` and evaluates `replace` away.

Idris makes some proofs much easier to write, since the layers of `replace` are hidden. On the flipside, once proofs become  more complex, evaluating `replace` away breaks subject-reduction, and we end up in situations where types given by idris do not typecheck themselves.

For example imagine the following scenario:

- We have types `a : Type` and `p : a -> Type`
- We have a function `g : p y -> Nat`, two values `x, y : a`, a term `v : p x`, and a proof `prf : x = y`.
- Finally we have the following program:
    ```
    g (replace {p} prf v)
    ```

If the above expression appears in the type of a program it will have this shape:
```
g v
```

But this program is malformed because `g` takes an argument of type `p y` but `v` has type `p x`.

This problem does not exist in Agda since expressions using `subst` are not evaluated unless the proof it uses is matched upon. This make
proving simple statements sightly less approchable, but enable the ceiling of proof complexity to be much higher since
the user can _see_ what `substs` are required to be matched in order to make progress in the proof. We're going to see in a subsequent section how to address the issue of therms that do not typecheck due to the evaluation of `replace`.

### Implicit arguments

Both languages feature implicit arguments but Idris only has named arguments, wheras Agda has both named and positional arguments.
What's more, Agda allows to bind implicit arguments in Lambda, something Idris can only do in top-level definitions.

This makes a number of things in Idris akward, like the fact that implicit arguments are automatically given to function in unapplied position when they shouldn't

*example of automatically applied argument*

But because there is no syntax for writing a lambda with an implicit argument, this cannot be resolved without writing a top-level definition, or by replacing implicit arguments by explicit ones.

### Totality Checking

Idris has three notions of termination: `total`, `covering`, `partial` . Programs marked `total` benefit from the totality checker
that tries to identify when programs are non-terminating with a series of heuristics. In a nutshell, the main rule of thumb is that
a program is total if every recursive call is made on a structurally smaller part of the program. Of course this is able to detect
that every terminating program is total, and for this, idris provides the `assert_total` primitive that will assert locally that a
program is total. Here is an example:

- [ ] TODO: example of total program that the compioler cannot detect

While having to use `assert_total` is not ideal, one of the benefits of this design, compared to marking the entire function as
partial, is that one can immediately see what parts of the program are suseptible to non-termination, which is useful for debugging
programs that were mistakently believed total.

The Idris compiler does not check for totallity by default, by default the compiler will check that every definition is `covering`,
that is, every pattern-match is exhaustive. This does not ensure termination, but it eliminate a sizable source of bugs that often
arise when changing the definition of a type. Without coverage checking, adding a constructor to a type can result in a crash, but
with coverage checking, the missing constructor is detected ahead of time.

- [ ] TODO: example of coverage checking

Finally, for programs which are neither covering or total, idris has the `partial` keyword. Those programs are often the product
of FFI interaction, or known-unsafe primitives like there are for concurrency. Ideally, every Idris keyword should be at least
`covering` and create suitable abstractions to hide, or avoid `partial` programs.

### Quantitative Type Theory

Idris implements quantitative type theory, meaning that each binder has an associated _quantity_ that represents the number
of uses the bound variable has. This feature has two main uses:
- Resource tracking via linearity.
- Erasure of compile-time only terms.

Because this work does not actually deal with linear resources, mostly the second aspect was used. One of the interesting
effects of this feature is that it highlights areas where one would suspect a type argument to be erased but due to how
the program is structured, it is impossible to erase this value at runtime (TODO: Reference natural transformation case).

A quantity is always attached to a _binder_, binders occur when a variable is given a type, example of binders include:

- Delcaring a new function `add : Nat -> Nat -> Nat` the variable `add` is bound
- Declaring a local variable with let `let x := f y` here the variable `x` is bound
- Giving a name to a function argument in a dependent function `(n : Nat) -> Fin n`, here  `n` is bound

In all those cases, we could have attached a quantity to each name to identify how many uses this variable will see in its
scope. When there are no quantities attached, the number of use is unrestricted. But we could have written:

- `(0 n : Nat) -> Fin n` to indicate that `n` is never used at runtime
- `let 1 x := f y` to indicate that `x` is used exactly once in the body of the let

By far the most powerful use is to annotate parameters of algebraic datatypes as erased so that they do not leak into
the runtime, avoiding having to rely on heuristics to optimise them away. (Cite edwin's old work here)

```
data List : (0 a : Type) -> Type where
  Nil : List a
  (::) : a -> List a -> List a
```

Here because the parameter `a` is marked as `0`, it will always be erased from the runtime, ensuring the list never
carries with it an extra needles argument at runtime.

### Automatic universal quantification via character case

To leverage existing knowledge from existing programmers, Idris' syntax borrowed a lot from Haskell, and one of the
features is developed to be closed in appearance to Haskell is the ability to automatically quantify variables
that are lowercase if they do not appear in the immediate scope. For example

```
reverse : List a -> List a
```
the parameter `a` never appears in scope and therefore it is automatically converted to an erased implicit argument:

```
reverse : {0 a : Type} -> List a -> List a
```

Note that in the final program, the variable `a` is annotated with `0`, indicating that it is inaccessible to the runtime,
again this is done to mimic the semantics of the equivalent Haskell program that would never leak the type `a` into the runtime.

Sometimes this behaviour is undesirable, and for those cases the feature can be disabled locally with the directive:

```
%unbound_implicits off
```

It can be re-enabled with a corresponding directive:

```
%unbound_implicits on
```

when deemed appropriate.

Idris also has a `forall` keyword, but despite what the keyword suggests,
idris does not have universal quantification, instead this keyword will desugar into an erased implicit parameter
just like when the argument's declaration is left out.

```
reverse : forall a. List a -> List a
~
reverse : {0 a : Type -> List a -> List a
```

[^fastJS]: https://unsafeperform.io/blog/2022-07-02-a_small_benchmark_for_functional_languages_targeting_web_browsers/
