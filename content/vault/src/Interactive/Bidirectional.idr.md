<!-- idris
module Interactive.Bidirectional

import Data.Container
import Data.Container.Closed
import Data.Container.Closed.Coproduct
import Data.Container.Closed.Sequence
import Data.Container.Closed.Maybe.Functor
import Data.Container.Closed.Kleene
import Data.Container.Apply.Definition
import Data.Container.Maybe.Definition
import Data.Container.Kleene
import Data.Container.Tensor.Definition

import Data.Coproduct
import Data.Product
import Data.Sigma
import Data.List
import Data.Either

%language ElabReflection

-->

## Bidirectional Typechecking Using Dependent Lenses

This section was first written as a blog post for the [cybercat institute](https://cybercat.institute/blog/), the version you see here goes into more details about why it works, rather than only showing that it does.

The core idea is an implementation of lenses-as-tactics to build a typechecker. Each inference rule is a tactic and in turn each tactic is represented as a lens. First we review the bidirectional rules for typech>

### Bidirectional: Up and Down

The simply typed lambda calculus can be checked using a _bidirectional typechecking algorithm_, that is to say, each jugdement is one of two forms:
- $t ∈ A$ : A synthesizing rule, saying that from term $t$ we can produce, or deduce type $A$
- $A \ni t$: A checking rule, asserting that term $t$ should have type $A$

Now it remains to fit a rule for each term, first, we properly define our lambda calculus, first we need types:
```
ty := name | ty "->" ty | 1
```

That is, each type is either a variable name, or a function, or the unit type. We represent this with a simple data type.

```idris
data Ty = Var String | Function Ty Ty | One

Eq Ty where
  Var s == Var t = s == t
  (Function f x == Function g y) = f == g && x == y
  One == One = True
  _ == _ = False

showTy : Bool -> Ty -> String
showTy parens (Var str) = str
showTy parens (Function f@(Function _ _) y) = showParens parens "\{showTy True f} -> \{showTy False y}"
showTy parens (Function x y) = showParens parens "\{showTy False x} -> \{showTy False y}"
showTy parens One = "1"

export
Show Ty where
  show = showTy False

Context : Type
Context = List (String, Ty)
```

<!-- idris
-- %runElab derive "Ty" [Eq]
-->

Now for the terms, we have either variable references, lambda expressions or function application:

```
stlc := stlc stc | λ name . stlc | name
```

However, we're missing types, which means we need to pick which one of the two judgement forms each term is. Thankfully we can fairly easily reason them out.

### App rule
In an application of the form `fn arg`, the term `fn` _must_ be a function type `->`, it would be a type error if it wasn't, therefore the term `fn` is synthesizable into `a -> b`. If we assume it's a function `a`

\begin{prooftree}
\AxiomC{f $\in A \to B$}
\AxiomC{$A \ni$ x}
\BinaryInfC{f x $\in B$} APP
\end{prooftree}

This rule however does not read top-to-bottom. Unlike other inference rules, reading from the premises down to the conclusion does not tell the story in the correct order. Instead one starts at the bottom-left wi>
- What does it take to synthesize the type of $\text{f x}$?
- Move top-left and read $\text{f} ∈ A \to B$, this means that we first need to obtain the type $A \to B$ for $\text{f}$
- Move top-right and read $A \ni \text{x}$, this means that we then need to check that $A$ accepts term $\text{x}$
- Then move _back down_ and read $B$, we've successfully synthesized $B$ from $\text{f x}$.

This dance clockwise around the inference line is where _bidirectionality_ comes from, we don't just read top to bottom, we read in both directions.

### Lambda rule


\begin{prooftree}
\AxiomC{$\text{n} : A \vdash B \ni \text{t} $}
\UnaryInfC{$ A \to B \ni \lambda \text{n}. \text{t}$} LAM
\end{prooftree}

- Start at the bottom-left, given $A \to B$.
- Move up, if by extending the context with $\text{n} : A$ if we can ensure $\text{t}$ has type $B$
- Move back down, then we can ensure that $\lambda\text{n}. \text{t}$ has type $A\to B$

### Var Rule

The `Var` rue does not delegate any work because it only does a context lookup.

\begin{prooftree}
\AxiomC{}
\UnaryInfC{$t : A \vdash t \in A$} VAR
\end{prooftree}


### Annotate

One can annotate a term with the type it is meant to have, we then check that it matches the type we are given and if so we can synthesize the type for it.

\begin{prooftree}
\AxiomC{$A \ni x$}
\UnaryInfC{$t : A \in A$} \text{Annotate}
\end{prooftree}

### Assume

Any type can accept a term of that type, the `Assume` rule makes sure what we expect is what we have.

\begin{prooftree}
\AxiomC{$t \in B$}
\AxiomC{$A = B$}
\BinaryInfC{$A \ni t$} \text{Assume}
\end{prooftree}

- Given a type $A$
- If we can synthesize type $B$ from term $\text{t}$
- and $A$ is equal to $B$
- Then $A$ accepts $\text{t}$

### Bidirectional Simply Typed Lambda Calculus

From this we defined the bidirectional simply typed lambda calculus
as a data type

```idris

data Mode = Synthesizable | Checkable

data Term : Mode -> Type where
  Variable : String -> Term Synthesizable
  App : (fn : Term Synthesizable) -> (arg : Term Checkable) -> Term Synthesizable
  Annotate : Ty -> Term Checkable -> Term Synthesizable
  Lam : (name : String) -> Term Checkable -> Term Checkable
  Assume : Term Synthesizable -> Term Checkable

Show (Term n) where
  showPrec prec (Variable str) = str
  showPrec prec (App fn arg) = showParens (prec == App) (showPrec (User 0) fn ++ " " ++ showPrec App arg)
  showPrec prec (Annotate ty tm) = showParens (prec > Open) (show tm ++ " : " ++ show ty)
  showPrec prec (Lam name x) = showParens (prec > Open) "λ\{name}. \{show x}"
  showPrec prec (Assume x) = showPrec prec x
```

The data type is indexed by the mode, either `Synthesizable` or `Checkable`.

### Bidirectional: Sideways

This summary of bidirectional typechecking offers the necessary background to understand how to implement them as lenses.
In that scenario, lenses's bidirectional works _sideways_ converting questions to further questions, and specific answers to more general ones.

We can sumarise this idea by illustrating the following derivation as a lens.

((λ x : a -> a. λ y : b. x)(λ x : . x))(v : b)

For bidirectional typechecking we have to categories of statements:
- Given this _trusted_ type, and looking at a piece of syntax. Can we ensure that it is a term of the given type?
- Looking at a piece of syntax, can we generate a trusted type for it?

In the first case, we are given an input type, in the context of a term, and we generate a witness of its truth, the question/answer pair looks like `Context × Term !> ()`. In the second case, we only know about a term but we need to produce a trusted type, therefore the question/answer pair looks like `Term !> Ty`

### A Data Type for Questions and Answers

With this knowledge, we formulate questions and answers as their own data types. First we write the data necessary to ask both `check` and `synth` questions.

```idris
record SynQuestion where
  constructor MkSynQ
  ctx : Context
  term : Term Synthesizable

record CheckQuestion where
  constructor MkChkQ
  ctx : Context
  type : Ty
  term : Term Checkable
```

Each question will have a corresponding answer, answers to checking question are only
a confirmation that everything went well, answers to synthesizing questions contain
the type that was synthesized.

```idris
SynAnswer : Type
SynAnswer = Ty

CheckAnswer : Type
CheckAnswer = Unit

SynGoal : Container
SynGoal = SynQuestion :- SynAnswer

ChkGoal : Container
ChkGoal = CheckQuestion :- CheckAnswer
```

Using those two types we build the typechecking container with `Question` as queries
and `Answer` as responses.

```idris
Typecheck : Container
Typecheck = ChkGoal + SynGoal
```

### A Coproduct of questions and answers

There is another way to describe the `Typecheck` container, instead of building two bespoke data types for the questions and answers, we can describe `Syn` and `Check` questions separately, and then use a coproduct to describe typechecking.

We need to use a tensor product on `SynAPI + CheckAPI` to carry around the necessary data to answer questions. We can prove that this container and the previous on `Typecheck` are isomorphic. The representation of this second one is closer to what you would expect from writing a term in $Poly$ as a coproduct of monomials, wheras the first one is closer to what one would already write in a dependently typed programming language and then retrofitted into a Container form.

For completeness, this is the $Poly$ term we just built:

$$
\text{TypecheckAPI} = Context\ y × (Syn\ y^{Ty} + Chk\ y)
$$

### Delegating Problems

A lens for an inference rule will take a question-answer pair and produce
0 or more delegate question-answer pairs. For example the `Var` rule does not delegate
any work, beyond checking the variable is in scope. So its type should be
`Typecheck =&> CUnit`. The `App` rule however does delegate two tasks,
synthesize the type of the function, and check the type of the argument. So its
type is `Typecheck =&> Typecheck ○ Typecheck`.

Because of this variable arity in the codomain, the typechecker will have type
`Typechecker =&> Star Typechecker` to capture both the fact that some rules delegate
nothing, and some delegate multiple tasks.

Additionally, we lift the output of the backward part with `Either String` to
handle errors. The type of the typechecking lens becomes:

```idris
data Error = ExpectedFunction (Term Synthesizable) Ty
           | IncompatibleAnn Ty Ty
           | VarNotFound String
           | LamNotFn (Term Checkable) Ty

E : Type -> Type
E = Either Error

TCErr : Container -> Container
TCErr = (E •)
```

Implementing it means to analyse the input and find out what question
is asked, and from that question, what further questions to ask.

```idris
varRule : TCErr SynGoal =&> Any.Maybe I
varRule = !! \case (MkSynQ ctx (Variable var)) => Just () ## \_ =>
                     maybeToEither (VarNotFound var) (lookup var ctx)
                   others => Nothing ## absurd

appRule : TCErr SynGoal =&> Any.Maybe (SynGoal ▷ Any.Maybe ChkGoal)
appRule = !! \case (MkSynQ ctx (App f x)) =>
                     Just (MkEx (MkSynQ ctx f)
                              (\case (Function a b) => Just (MkChkQ ctx a x)
                                     _ => Nothing
                              )
                          )
                     ## (\case (Aye (Function a b ## Aye vy)) => Right b
                               (Aye (t ## _)) => Left (ExpectedFunction f t)
                        )
                   _ => Nothing ## absurd

annRule : SynGoal =&> Any.Maybe ChkGoal
annRule = !! \case (MkSynQ ctx (Annotate ty term)) =>
                       Just (MkChkQ ctx ty term) ## \_ => ty
                   _ => Nothing ## absurd

assume : TCErr ChkGoal =&> Any.Maybe SynGoal
assume = !! \case (MkChkQ ctx ty (Assume term)) =>
                     Just (MkSynQ ctx term) ## (\(Aye sy) =>
                        if sy == ty
                           then Right ()
                           else Left (IncompatibleAnn sy ty)
                           )
                  _ => Nothing ## absurd

lamRule : ChkGoal =&> Any.Maybe ChkGoal
lamRule = !! \case (MkChkQ ctx (Function a b) (Lam var body)) =>
                       Just (MkChkQ ((var, a) :: ctx) b body) ## \_ => ()
                   _ => Nothing ## absurd

IsFn : Container
IsFn = Ty :- Maybe (Ty * Ty)

lamRule' : TCErr ChkGoal =&> Any.Maybe (IsFn ▷ All.Maybe ChkGoal)
lamRule' = !! \case (MkChkQ ctx ty (Lam var body)) =>
                       Just (MkEx ty (map (\fnTy => MkChkQ ((var, fnTy.π1) :: ctx) fnTy.π2 body))) ##
                            \case (Aye (Nothing ## p2)) => Left (LamNotFn (Lam var body) ty) -- the lambda wasn't a function
                                  (Aye (Just x ## (Yay y))) => Right () -- everything went well
                    _ => Nothing ## absurd
```

Because there is a finite number of constructors and each has a rule it can be applied to
we can also write a lens that will destructure the input into its various constructors and
each lens is now a non-failing process because we only feed it the correct input

```idris {hidden=""}
%hide Prelude.Ops.infixr.(&&)
private infixl 6 &&
```

We define a container for each possible constructor of our language, each reprents the data
we can extract from the constructor to pass onto a subsequent lens for solving the problem.

```idris
VarGoal : Container
VarGoal = Context * String :- Ty
AppGoal : Container
AppGoal = Context * Term Synthesizable * Term Checkable :- Ty
LamGoal : Container
LamGoal = Context * Ty * String * Term Checkable :- Unit
AnnotateGoal : Container
AnnotateGoal = Context * Ty * Term Checkable :- Ty
AssumeGoal : Container
AssumeGoal = Context * Ty * Term Synthesizable :- Unit
```

The `match` lens then takes as input an term of our language and returns the appropriate question/answer pair.
Because there are 5 constructors, this is a coproduct of 5 containers.

```idris
match : ChkGoal + SynGoal =&> VarGoal + AppGoal + LamGoal + AnnotateGoal + AssumeGoal
match = !! \case
                 (<+ (MkChkQ ctx type (Assume t))) => +> (ctx &&  type && t) ## id
                 (+> (MkSynQ ctx (Annotate ty term))) => <+ +> (ctx && ty && term) ## id
                 (<+ (MkChkQ ctx type (Lam name term))) => <+ <+ +> (ctx && type && name && term) ## id
                 (+> (MkSynQ ctx (App fn arg))) => <+ <+ <+ +> (ctx && fn && arg) ## id
                 (+> (MkSynQ ctx (Variable str))) => <+ <+ <+ <+ (ctx && str) ## id
```

Each one can now be implemented as a lens without `Maybe` surrounding it.

```idris
namespace Direct
  export
  varRule : TCErr VarGoal =&> I
  varRule = !! \(ctx && name) => () ## \_ =>
            maybeToEither (VarNotFound name) (lookup name ctx)

  export
  annRule : AnnotateGoal =&> ChkGoal
  annRule = !! \(ctx && ty && term) => MkChkQ ctx ty term ## const ty

  export
  assRule : TCErr AssumeGoal =&> SynGoal
  assRule = !! \(ctx && ty && term) => MkSynQ ctx term ## \ty' =>
            if ty == ty' then Right ()
                         else Left (IncompatibleAnn ty' ty)

  export
  lamRule : TCErr LamGoal =&> IsFn ▷ All.Maybe ChkGoal
  lamRule = !! \(ctx && ty && var && body) =>
            MkEx ty (map (\fnTy => MkChkQ ((var, fnTy.π1) :: ctx) fnTy.π2 body)) ##
            (\case (Nothing ## yy) => Left (LamNotFn (Lam var body) ty)
                   ((Just x) ## yy) => Right ())

  export
  appRule : TCErr AppGoal =&> SynGoal ▷ All.Maybe ChkGoal
  appRule = !! \(ctx && fn && arg) =>
                MkEx (MkSynQ ctx fn) (\case (Function a b) => Just (MkChkQ ctx a arg)
                                            _ => Nothing) ##
                (\case (Function a b ## (Yay x)) => pure b
                       (xs ## ys) => Left (ExpectedFunction fn xs))
```

We can then handle each constructor with the appropriate lens applying the rule to
the bespoke problem

With some ingenuity we can turn the above into an actual typechecker. It requires
making use of unbounded recursion in the host language by calling the checker recursivley
for each sub-problem. The first


```idris {hidden=""}
distribFPlus5 : f • (a + b + c + d + e) =&> f • a + f • b + f • c + f • d + f • e
distribFPlus5 = !! \x => ?adad ## ?distribFPlus5_rhs

dia5 : a + a + a + a + a =&> I
dia5 = !! \case x => ?dia5_rhs

pushRightSeq : Monad f => f • (a ▷ b) =&> f • (a ▷ f • b)
pushRightSeq = !! \x => x ##
                   (\yy => do y1 ## y2 <- yy
                              map (y1 ##) y2
                   )

distFMaybe : Functor f => f • Any.Maybe a =&> Any.Maybe (f • a)
distFMaybe = !! \case Nothing => Nothing ## absurd
                      (Just x) => Just x ## (\(Aye vx) => map (\y => Aye y) vx )

distFMaybe' : Applicative f => f • All.Maybe a =&> All.Maybe (f • a)
distFMaybe' = !! \case Nothing => Nothing ## (\xs => pure Nay)
                       (Just x) => Just x ## (\(Yay vx) => map (\y => Yay y) vx )
```

```idris
runAll : TCErr VarGoal +
         TCErr AppGoal +
         TCErr LamGoal +
         TCErr AnnotateGoal +
         TCErr AssumeGoal =&>
         I +
         TCErr (SynGoal ▷ All.Maybe ChkGoal) +
         TCErr (IsFn ▷ All.Maybe ChkGoal) +
         TCErr ChkGoal +
         TCErr SynGoal
runAll = varRule
    ~+~ pureRight appRule {a = AppGoal}
    ~+~ pureRight lamRule {a = LamGoal}
    ~+~ fapplyMap annRule
    ~+~ pureRight assRule {a = AssumeGoal}
```

Now comes the hard part. The codomain of this lens is a coproduct of different kinds
of sub-goals. To turn this into a fully working program we need to handle each
subgoal with a working typechecker. But we have not defined it yet! Indeed, all this
setup is necessary to even start working on the typechecker.

Idris allows to forward define type signatures for mutual definitions, and so we
write down the type for the typechecking lens as a Costate `TCerr Typecheck`.

```idris
covering
typecheckRec : Costate (TCErr Typecheck)
```

The definition is `covering` because idris cannot prove that each recursive call
to `typecheckRec` is on a smaller sub-goal. It is perfectly possible that
our lenses generates bigger subgoal for which recursive application of them would
not terminate. Thankfully, we know this is not the case, but the cost is that
the compiler cannot recognise the terminating nature of this definition.

For each branch of the match we have a different subgoal to translate back into a
container `TCErr Typecheck`. We write one lense for each and then apply it to
the coproduct using bifunctoriality of `+`.

```idris
covering
adapt1 : TCErr (SynGoal ▷ All.Maybe ChkGoal) =&> TCErr Typecheck
adapt1 = pushRightSeq {f = E, b = All.Maybe ChkGoal}
    |&> fapplyMap {a = SynGoal ▷ TCErr (All.Maybe ChkGoal), b = Typecheck }
        ((identity SynGoal ~▷~ fromChk)
            {a = SynGoal, a' = SynGoal, b = TCErr (All.Maybe ChkGoal), b' = I}
        |&> fromSeqIdRight
        |&> inr {a = ChkGoal, b = SynGoal})
    where
      covering
      fromChk : TCErr (All.Maybe ChkGoal) =&> I
      fromChk = distFMaybe' {a = ChkGoal}
         |&> All.mapMaybe
             (fapplyMap {a = ChkGoal} (inl {b = SynGoal}) |&> typecheckRec)
         |&> All.unitI

isFn : Closed.Costate IsFn
isFn = costate (\case (Function a b) => Just (a && b) ; _ => Nothing)

covering
adaptMaybe : TCErr (All.Maybe ChkGoal) =&> I
adaptMaybe = distFMaybe' {a = ChkGoal}
    |&> All.mapMaybe {a = TCErr ChkGoal, b = I}
        (fapplyMap {a = ChkGoal, b = Typecheck}
            (inl {b = SynGoal}) |&> typecheckRec)
    |&> All.unitI

covering
adapt2 : TCErr (IsFn ▷ All.Maybe ChkGoal) =&> I
adapt2 = fapplyMap {f = E}
    ((isFn ~▷~ identity (All.Maybe ChkGoal))
    |&> fromSeqIdLeft {a = All.Maybe ChkGoal})
    |&> adaptMaybe

adapt3 : TCErr ChkGoal =&> TCErr Typecheck
adapt3 = fapplyMap (inl {a = ChkGoal, b = SynGoal})

adapt4 : TCErr SynGoal =&> TCErr Typecheck
adapt4 = fapplyMap (inr {b = SynGoal, a = ChkGoal})

covering
recAll : I +
         TCErr (SynGoal ▷ All.Maybe ChkGoal) +
         TCErr (IsFn ▷ All.Maybe ChkGoal) +
         TCErr ChkGoal +
         TCErr SynGoal
         =&>
         I + I + I + I + I
recAll = identity I
    ~+~ (adapt1 |&> typecheckRec)
    ~+~ adapt2
    ~+~ (adapt3 |&> typecheckRec)
    ~+~ (adapt4 |&> typecheckRec)
```

A couple noteworthy things about the above program:

- For the variable case, we don't have an adaptation lens because in this case there
  are no subgoals to solve, and therefore we are done. This gives a distrinctive type
  to the base case of our induction.
- To implement the `App` rule we need to defer to another lens `isFn` that will match
  on the type and return the domain and codomain types of a function and fail otherwise.
- In both the implementation of `lam` and `app` we have a sequence of containers where
  a `maybe` is involved. We use the `All` variant to properly represent the fact that a
  handler for those containers need to also produce a value for the case where the lens
  fails
- In all cases, there is a lot of juggling around `TCErr` due to it being a comonad
  rather than a monad, a fact we can see if we illustrate our program with functor boxes


- [ ] add functor box drawings

We combine our matching functions with our lenses that call the typechecker recursively.
This requries some helper functions `distribFPlus5` and `dia5` that will distribute
the functorial application across our coproduct of 5 containers, and `dia5` is the diagonal
map for 5 coproducts.


```idris
typecheckRec = fapplyMap {f = E} match
    |&> distribFPlus5 {a = VarGoal, b = AppGoal, c = LamGoal, d = AnnotateGoal, e = AssumeGoal, f = E}
    |&> runAll
    |&> recAll
    |&> dia5 {a = I}
```

With this lens we can run the typechecker as a costate and obtain the compiler output as an `E (Ty + Unit)`

```idris
covering
runTypechecker : (x : Typecheck .request) -> E (Typecheck .response x)
runTypechecker = runCostate typecheckRec
```

We can run some example, for example the following is well-typed:

```idris
-- well typesd examples
```


And those programs fail for various reasons
```idris
-- ill-typed examples
```

- [ ] add typechecking examples
