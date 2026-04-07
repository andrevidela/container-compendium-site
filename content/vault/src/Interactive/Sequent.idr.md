<!-- idris
module Interactive.Sequent

import Data.Container
import Data.Container.Closed
import Data.Container.Closed.Eq
import Data.Container.Closed.Sequence
import Data.Container.Tensor.Definition
import Data.Container.Closed.Tensor.Bifunctor
import Data.Container.Closed.List.Functor
import Data.Container.Closed.List.Monoid
import Data.Container.Displayed
import Data.Container.Closed.Maybe.Functor
import Data.Container.List.Functor
import Data.Container.List.Desc
import Data.Container.Coproduct
import Data.Container.Descriptions.List
import Data.Container.Descriptions.Maybe
import Data.Container.Kleene
import Data.Container.Maybe.Definition

import Data.Fin
import Data.DPair
import Data.List
import Data.List.Any
import Data.List.Elem
import Data.List.Quantifiers
import Data.Sigma
import Data.Product
import Data.List1
import Data.Maybe.Any
import Data.Nat.Views
import Data.SnocList
import Data.Vect
import Decidable.Equality

import Syntax.PreorderReasoning.Generic

%hide Prelude.Ops.infixr.(&&)
%hide Prelude.Ops.infixl.(*)
private infixl 8 @@
private infixr 9 ~~>
private infix 5 |-
private infixl 8 *
private infixl 8 &&

private prefix 10 ¬
private infixl 8 ∧
private infixl 7 ∨

data Cover : (x, y, xy : List a) -> Type where
  Empty : Cover [] [] []
  PickL : Cover a b ab -> Cover (x :: a) b (x :: ab)
  PickR : Cover a b ab -> Cover a (x :: b) (x :: ab)

CoverRight : {xs : List a} -> Cover [] xs xs
CoverRight {xs = []} = Empty
CoverRight {xs = (x :: xs)} = PickR (CoverRight {xs})

CoverLeft : {xs : List a} -> Cover xs [] xs
CoverLeft {xs = []} = Empty
CoverLeft {xs = (x :: xs)} = PickL CoverLeft
-->

## Tactics for The Sequent Calculus

The sequent calclulus is the best environement to write a theorem prover. It's
a well known and interesting system, it has a extensive history and literature
surrounding it. And crucially for us, writing a theorem prover for us is
rendered easy by studying rules that are "invertible", that is, some statements
have only one rule apply, which makes it very amenable to automating.

First we define the types for our language, we define negation, implication,
conjunction and disjunction, along with primitive atoms.

$Ty := a \mathbin{|} Ty → Ty \mathbin{|} \lnot Ty \mathbin{|} Ty \land Ty \mathbin{|}Ty \lor Ty$

```idris
data Ty = Atom Nat -- atoms are distinguished by a natural number
        | (¬)  Ty
        | (~~>) Ty Ty
        | (∧) Ty Ty
        | (∨) Ty Ty

```

We define a sequent as a pair $Ty^* \vdash Ty^*$  where the first list of types is known as the "antecedent" and the second as the "consequent". Those lists form traditional "contexts", as lists of types. We can interpret sequents in human language as "if all the antecedents are true, then one of the consequents is true".

```idris
record Sequent where
  constructor (|-)
  antecedent : List Ty
  consequent : List Ty
```

In idris we use a `SnocList` in the antecedents to replicate the fact that we pop elements from the right for the antecedents and from the left for consequents $Δ, a \vdash b, \Pi$ means that $a$ and $b$ are types and $\Delta$ and $\Pi$ are lists of types occurring in the rest of the context.

Proof are indexed by a sequent, if a proof is inhabited, then the sequent is verified.

```idris
data LK : Sequent -> Type where
```

The first rule is the axiom rule. A sequent of the form $a \vdash a$ is always true. It states that a sequent with one antecedent and the same statement as consequent is always true and does not require further proofs to be verified.

- [ ] add inference rule

```idris
  --
  -- ----------
  --  a |- a
  Axiom  : LK ([a] |- [a])
```

We introduce negation-left and negation-right rules both of which
require a premisse without negation but where the positions of the
term is moved across the turnstile.

- [ ] add inference rule

```idris
  --   Γ |- a, Δ
  -- -------------
  --  Γ , ¬a |- Δ
  NegL   : LK (g |- a::d) -> LK (¬ a :: g |- d)

  --  Γ , a |- Δ
  -- -------------
  --  Γ |- ¬a , Δ
  NegR   : LK (a :: g |- d) -> LK (g |- ¬ a :: d)
```

In traditional presentations of sequent calculus, there
are two rules for "and-introduction-left". One for "a"
and one for "b". We slightly depart from this convention
to say that to build a proof of "and-left" we
require a _choice_ of "a" or "b". This comes with the
benefit that now every connective has the same number of
rules, additionally it perfectly represents the proof tree
derived by our tactics.

- [ ] add inference rule

```idris
  -- We write "+" to indicate that either
  -- of those premisses must hold
  --    Γ , a |- Δ "+" Δ Γ , b |- Δ
  -- -----------------------------
  --         Γ, a ∧ b |- Δ
  AndL  : LK (b :: g |- d) + LK (a :: g |- d) ->
          LK ((a ∧ b) :: g |- d)

  -- Γ |- a , Δ    Γ |- b , Δ
  -- ------------------------
  --      Γ |- a ∧ b , Δ
  AndR   : LK (g |- a :: d) -> LK (g |- b :: d) -> LK (g |- (a ∧ b) :: d)
```

We use a similar convention for "or-right" stating that to introduce
an "or" on the right side of the turnstile we need a choice of premisses
an "a" or "b" on the right side.

```idris
  -- Γ , a |- Δ    Γ , b |- Δ
  -- ------------------------
  --      Γ , a ∨ b |- Δ
  OrL    : LK (a :: g |- d) -> LK (b :: g |- d) ->
           LK ((a ∨ b) :: g |- d)

  --  Γ |- a , Δ  "+"  Γ |- b , Δ
  -- ----------------------------
  --      Γ  |- a ∨ b , Δ
  OrR    : LK (g |- b :: d) + LK (g |- a :: d) ->
           LK (g |- (a ∨ b) :: d)
```

Finally, we define rules for implication. "implication-left" is particularly
tricky because, to prove implication on the left, we need additional side
conditions that are not clearly stated in the inferrence rule: The fact that
the contexts in the premises form a _cover_ of the contexts in the conclusion.

```idris
  --  Γ |- a , Δ      Σ , b |- Π
  -- --------------------------
  --  Σ , Γ , a -> b |- Δ , Π
  ImpL   : {Γ, Π, Δ, Σ, ΓΣ, ΔΠ : _} ->
           Cover Γ Σ  ΓΣ  -> Cover Δ Π ΔΠ ->
           LK (Γ |- a :: Δ) -> LK (b :: Σ |- Π) ->
           LK (((a ~~> b) :: ΓΣ) |- ΔΠ)

  --  Γ , a |- b , Δ
  -- ----------------
  --  Γ |- a -> b , Δ
  ImpR   : LK (a :: g |- b::d) -> LK (g |- (a~~>b)::d)
```

```idris {hidden=""}
covering
Show (LK t) where
  show _ = "proven"
  -- show (NegL x) = "NegL " ++ show x
  -- show (NegR x) = "NegR " ++ show x
  -- show (AndL x) = "AndL " ++ show x
  -- show (AndR x y) = "AndR(" ++ show x ++ ", " ++ show y ++ ")"
  -- show (OrL x y) = "OrL(" ++ show x ++ ", " ++ show y ++ ")"
  -- show (OrR x) = "OrR " ++ show x
  -- show (ImpL x y z w) = "ImpL(" ++ show z ++ ", " ++ show w ++ ")"
  -- show (ImpR x) = "ImpR " ++ show x
```

Using the rules above we can give an example of the `LK` system at play. Here we
prove that the sequent $\vdash \lnot\lnot a → a$ is true

```idris
checkProof : LK ([] |- [¬ (¬ a) ~~> a])
checkProof = ImpR (NegL (NegR Axiom))
```

We reach the core definition of this section, the `Seq` container that
represents sequents and their proofs. Our theorem prover will be primarily manipulating
containers of this sort.

```idris
Seq : Container
Seq = (s : Sequent) !> LK s
```

```idris {hidden=""}
interface HemiDecidable (0 a : Type) where
  hdec : (x, y : a) -> Maybe (x === y)

hemEq : (a, b : Ty) -> Maybe (a === b)
hemEq (Atom a) (Atom b) with (decEq a b)
  hemEq (Atom a) (Atom a) | Yes Refl = Just Refl
  hemEq (Atom a) (Atom b) | No c = Nothing
hemEq (¬ x) (¬ y) = Prelude.map (\x => cong (¬) x) (hemEq x y)
hemEq (x ~~> y) (z ~~> w) = do
  Refl <- hemEq x z
  Refl <- hemEq y w
  pure Refl
hemEq _ _ = Nothing

HemiDecidable Ty where
  hdec = hemEq
```

Implementing the theorem prover entails writing a lens for each tactic of our
system. Because our tactics will mirror our proof system, we write one tactic
per constructor of `LK`. We start with axioms.

Generally, axioms are rules without premises, in our system we have one axiom
the `Axiom` rule that says that if we have only one term in our context, then
we can prove it.
To implement the rule in Idris we use hemi-decidable equality here to obtain a
proof of their equalty and construct the proof using the `Axiom` constructor
in the backward part of the lens.

- [ ] add ref to hem-dec

```idris
applyAxiom : Seq =&> Any.Maybe I
applyAxiom = !! \case
  ([a] |- [c]) => case hemEq a c of
                      Just Refl => Just () ## (const Axiom)
                      Nothing => Nothing ## absurd
  _ => Nothing ## absurd
```

The negation-left and right tactics will do the same as `Axiom` and match on the
incoming problem to ensure is has the right shape. Unlike `Axiom` they then
produce a sub-problem to solve, removing the negation, and assuming that the
subproof will be solved. If the proof does not have the right shape, the lens fails immediately.

```idris
applyNegL : Seq =&> Any.Maybe Seq
applyNegL = !! \case
    (¬ a :: g |- d) => Just (g |- a :: d) ## (NegL . .unwrap)
    _ => Nothing ## absurd

applyNegR : Seq =&> Any.Maybe Seq
applyNegR = !! \case
    (g |- ¬ a :: d) => Just (a :: g |- d) ## (NegR . .unwrap)
    _ => Nothing ## absurd
```

The expressivity of containers shows the difference between
"and-left" and "and-right" rules. One of them is a product, and the other
one is a tensor! This is the payoff for representing "and-left" proofs
as a choice of two premisses, it allows to write this code seamlessly.
This type in turn shows that "and-left" is a non-deterministic proof, giving
the theorem prover (or human) a choice to make when proving statements
involving "and".

```idris
applyAndL : Seq =&> Any.Maybe (Seq * Seq)
applyAndL = !! \case
    ((a ∧ b) :: g |- d) => Just ((b :: g |- d) && (a :: g |- d)) ## (AndL . .unwrap)
    _ => Nothing ## absurd

applyAndR : Seq =&> Any.Maybe (Seq ⊗ Seq)
applyAndR = !! \case
  (g |- (a ∧ b) :: d) => Just ((g |- a :: d) && (g |- b :: d)) ## (uncurry AndR . .unwrap)
  _ => Nothing ## absurd
```

We see the same distinction between tactics that produce subproblems that all
need to be solved with "or-left" and tactics that produce subproblem only
one of which need to be solved "or-right", as indicated by the use of tensor
and cartesian product respectively.

```idris
applyOrL : Seq =&> Any.Maybe (Seq ⊗ Seq)
applyOrL = !! \case
  ((a ∨ b) :: g |- d) => Just ((a :: g |- d) && (b :: g |- d)) ## (uncurry OrL . .unwrap)
  _ => Nothing ## absurd

applyOrR : Seq =&> Any.Maybe (Seq * Seq)
applyOrR = !! \case
  (g |- (a ∨ b) :: d) => Just ((g |- b :: d) && (g |- a :: d)) ## (OrR . .unwrap)
  _ => Nothing ## absurd
```

It remains to define tactics for implication left and right. While implication right
does not pose any particular challenge, implication left is uniquely hard to implement.

```idris
applyImpR : Seq =&> Any.Maybe Seq
applyImpR = !! \case
    (g |- a ~~> b :: d) => Just (a :: g |- b :: d) ## (ImpR . .unwrap)
    _ => Nothing ## absurd
```

The conclusion of "implication-left" has the form $Γ, a \to b ⊢ Δ$ and its premisses
have types $Γ₁, b ⊢ Δ₁$ and $Γ₂ ⊢ a, Δ₂$. Note that this is slightly different from
the premisses written by hand whch only state that _concatenation_ of contexts
from the premisses forms the context of the conclusion. The closest notion we can
define in constructive type theory is a _Cover_.

```
data Cover : (x, y, xy : List a) -> Type where
  Empty : Cover [] [] []
  PickL : Cover a b ab -> Cover (x :: a) b (x :: ab)
  PickR : Cover a b ab -> Cover a (x :: b) (x :: ab)
```

A Cover is constructive evidence that two lists merge into a third one, in our case, the
lists are the contexts of the premises, and the third list is the context in the conclusion.

The `Cover'` container captures the information transmitted when computing a cover. Indeed,
a system generating covers takes a cover `xy` as a query and responds with two sublists
`x` and `y` such that they form a cover of `xy`.

```idris
Cover' : Container
Cover' = (xy : List Ty) !> Σ (x : List Ty) | Σ (y : List Ty) | Cover x y xy
```

Once idenified, implication-left problems are translated into two `Cover'` sub-problems,
and two `Seq` sub-problems. That is, we need to generate two covers, and using those, we
need to solve two sub-problems.

```idris
matchImpL : Seq =&> Any.Maybe ((Cover' ⊗ Cover') ▷ (Seq ⊗ Seq))
matchImpL = !! \case
    (a ~~> b :: g |- d) =>
      Just (MkEx (g && d)
          (\((gamma ## sigma ## gs) && (delta ## pi ## dp)) =>
                (gamma |- a :: delta) &&
                (b :: sigma |- pi)))
      ## (\xy =>
            let (((gamma ## sigma ## gs) && (delta ## pi ## dp)) ## xy) = xy.unwrap
            in ImpL gs dp xy.π1 xy.π2)
    _ => Nothing ## absurd
```

Dealing with covers requires some additional insight and infrastructure. Our task
is to write a "solver" for covers, that is, a lens that looks like `Cover' =&> I`.
This type is not quite because `Cover'` generates lists of candidate covers, therefore
to solve a `Cover'` we need to express the idea that _one of the covers_ works. We
achieve that by applying the `Any.List` monad to `I` indicating "there exists
one cover that works", our cover solver therefore has type `Cover' =&> Any.List I`.
From this, a follow up insight is that `Any.List I` is isomorphic to the list container!
Indeed, the requests of `Any.List I` are `List Unit` which is isomorphic to `Nat` and
the responses of `Any.List I` are `Any (\_ => Unit) xs` where `xs` is the `List Unit` from
the request. This second type is isomorphic to `Fin` since it's only in habited by a unit
value for exactly one of the elements of `xs`. Consequently, the lens we are going to implement is
`Cover' =&> ListCont`.

To build the cover solver we need a notion of a cover `Selector`, a piece of data that
uniquely idenfies a cover given a candidate list. Because our covers are lists of
boolean choices, this type is isomorphic to `Vect n Bool` where `n` is the length
of the list that is subject to the cover.

```idris
data Selector : List a -> Type where
  Nil : Selector []
  (::) : Bool -> Selector xs -> Selector (x :: xs)
```

Another way to see `Selector` is as the bit-string that uniquely identifies
a cover once they are enumerated. The number of covers is $2^n$ where `n` is
the number of elements in the list we are covering, therefore any number in the
range $[0, 2^n]$ identifies a unique cover for a list of length $n$.

The following function generates a cover given a `Selector` by picking
the left or right choice depending on the boolean values in it.

```idris
createSingleCover : {0 a : Type} -> (xy : List a) -> Selector xy ->
    Σ (x : List a) | Σ (y : List a) | Cover x y (toList xy)
createSingleCover [] [] = [] ## [] ## Empty
createSingleCover (x :: xy) (False :: xs)  =
  let ls ## ks ## rs = createSingleCover xy xs
  in (x :: ls) ## ks ## PickL rs
createSingleCover (x :: xy) (True :: xs)  =
  let ls ## ks ## rs = createSingleCover xy xs
  in ls ## (x :: ks) ## PickR rs
```

We continue with `createSelector`, a way to generate a selector given a unique
idenfier for a cover. `coverBound` tracks how many covers exist for a given list
to cover.

```idris
coverBound : List a -> Nat
coverBound [] = 1
coverBound (x :: xs) = 2 * coverBound xs

createSelector :
   (cov : List Ty) ->
   (ix : Fin (coverBound cov)) ->
   Selector cov
createSelector [] ix = []
createSelector (x :: xs) ix =
  case splitFinPlus ((coverBound xs)) ((coverBound xs) + 0) ix of
       +> fn => True  :: createSelector xs (replace {p = Fin} (plusZeroRightNeutral ?) fn)
       <+ fn => False :: createSelector xs fn
```

Composing `createSelector` and `createSingleCover` we can generate a cover given
an index for it, which we use to implement our cover solver.

```idris
SolveCover : Cover' =&> ListCont
SolveCover = !! \cov =>
    (coverBound cov)
    ## (\ix => createSingleCover cov (createSelector cov ix) )
```

Unfortunately, the cover solver by itself is not enough to manipulate subgoals, we need
another insight. Fortunately for us, we already have to tools to deploy it, it's the fact
that `Any.List a` is isomorphic to `ListCont ▷ a` _and_ that `ListCont` forms a monoid
via the tensor product of containers. This last information perfectly captures the need
for a way to combine covers by saying that the search space is not just a list of possible
covers, but a matrix for each possible combination of covers. We implement the following
lens using those two insights and represent the lens `toSeq` diagramatically.

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{(Cover \otimes Cover) \rhd (Seq \otimes Seq)} && {Any (Seq \otimes Seq)} \\
\\
{(List \otimes List) \rhd (Seq \otimes Seq)} && {List \rhd (Seq \otimes Seq)}
\arrow["toSeq", from=1-1, to=1-3]
\arrow["{Solve \otimes Solve \rhd id}", from=1-1, to=3-1]
\arrow["{List_\otimes \rhd id}", from=3-1, to=3-3]
\arrow["toList", from=3-3, to=1-3]
\end{tikzcd}
\end{document}
```

```idris
covering
toSeq : ((Cover' ⊗ Cover') ▷ (Seq ⊗ Seq))
    =&> Any.List (Seq ⊗ Seq)
toSeq =  CalcWith {leq = (=&>)} $
  |~ (Cover' ⊗ Cover') ▷ (Seq ⊗ Seq)
  <~ (ListCont ⊗ ListCont) ▷ (Seq ⊗ Seq)
      ...((SolveCover ~⊗~ SolveCover) ~▷~ identity (Seq ⊗ Seq))
  <~ ListCont ▷ (Seq ⊗ Seq)
      ...(mult ~▷~ identity (Seq ⊗ Seq))
  <~ Any.List (Seq ⊗ Seq)
      ...(fromAny {a = Seq ⊗ Seq})
```

Using `toSeq` we can convert implication-left problems into a more approachable format, as
an existential list of two sub-problems.

```idris
covering
applyImpL : Seq =&> Any.Maybe (Any.List (Seq ⊗ Seq))
applyImpL = matchImpL |&> Any.Maybe.map toSeq
```

We finally have all our tactics in the form of a lens, to combine them all
we define a "sub-problem" with `SubSeq`, a container that indicate that either we
are done, or we have more sub-problems to solve.

```idris
SubSeq : Container
SubSeq = Any.List (All.List Seq)
```

Each of our previous definitions can be mapped to this container via
some judiciously defined injections.

```idris
seqToSub : Seq =&> SubSeq
seqToSub = !! \x => (pure (pure x)) ## All.head . .extract

endToSub : I =&> SubSeq
endToSub = !! \x => (pure []) ## const ()

pairToSub : Seq * Seq =&> SubSeq
pairToSub = !! \x =>  [[x.π1], [x.π2]] ## bimap All.head All.head . .extract2

tensorToAll : Seq ⊗ Seq =&> All.List Seq
tensorToAll = !! \x => ([x.π1, x.π2]) ## (\xx => All.head xx && head (tail xx))

tensorToSub : Seq ⊗ Seq =&> SubSeq
tensorToSub = tensorToAll |&> anyPure

anyToTactic : Any.List (Seq ⊗ Seq) =&> SubSeq
anyToTactic = Any.List.map tensorToAll
```

Using those maps, we adapt each tactic into a lens with codomain `Maybe SubSeq`.

```idris
covering
seqTactics : List (Seq =&> Any.Maybe SubSeq)
seqTactics = [applyAxiom |&> Any.Maybe.map endToSub,
              applyNegL  |&> Any.Maybe.map seqToSub,
              applyNegR  |&> Any.Maybe.map seqToSub,
              applyAndL  |&> Any.Maybe.map pairToSub,
              applyAndR  |&> Any.Maybe.map tensorToSub,
              applyOrL   |&> Any.Maybe.map tensorToSub,
              applyOrR   |&> Any.Maybe.map pairToSub,
              applyImpL  |&> Any.Maybe.map anyToTactic,
              applyImpR  |&> Any.Maybe.map seqToSub]
```

Since morphisms $a → b$ form a monoid when $b$ is a monoid, we can use the fact
that `Any.Maybe a` is a monoid to run each lens sequentially until one of them
suceeds. Note that the order of this list defines the order in which each tactic
is tested, the consequence being that a different order could result in drastically
different performance characteristics.

```idris
covering
runAll : Seq =&> Any.Maybe SubSeq
runAll = tryAll {a = Seq, b = SubSeq} seqTactics
```

Using unbounded recursion in Idris, we define the loop solver that turns our
lens $\cbar{A} \Rightarrow Maybe\ \cbar{A}$ into a costate
$Costate(Maybe\bullet \cbar{A})$

```idris
-- map all values through an applicative functor
allMap' : {0 a : Type} -> {0 b : a -> Type} -> Applicative m =>
         (f : (x : a) -> m (b x)) -> (xs : List a) -> m (All b xs)
allMap' f [] = pure []
allMap' f (x :: xs) = [| f x :: allMap' f xs |]

-- apply all values and join them using an alternative functor
anyMap' : {0 a : Type} -> {0 b : a -> Type} -> Alternative m =>
         (f : (x : a) -> m (b x)) -> (xs : List a) -> m (Any b xs)
anyMap' f [] = empty
anyMap' f (x :: xs) = map (Here {p = b, xs}) (f x)
                  <|> map (There {p = b, x}) (anyMap' f xs)

-- given a lens `a => Maybe (Any (List a))` generate a costate
-- `Maybe • a => I` by recursively applying the lens to all
-- sub-problems generated until none are left.
covering
loopTactics : (tactics : a =&> Any.Maybe (Any.List (All.List a))) ->
             (x : a.message) -> Maybe (a.response x)
loopTactics m x = case m.fn x of
  (Just py ## p2) =>
    map (p2 . Aye) $ anyMap' (allMap' (loopTactics m)) py
  (Nothing ## p2) => Nothing -- could not generate a sub-problem
```

Our theorem prover is an instance of the above costate specialised to `runAll`.

```idris
covering
runProver : (x : Seq .message) ->  Maybe (Seq .response x)
runProver = loopTactics {a = Seq} runAll
```

We can now run our prover on any sequent calculus term and see if it's solvable with the given tactics.

```idris
doubleNeg : Sequent
doubleNeg = [] |- [(¬ (¬ (Atom 0))) ~~> Atom 0]

excluded : Sequent
excluded = [] |- [Atom 0 ~~> Atom 0 ∨ ¬ Atom 0]
```

Those two examples give the expected results when run in the REPL:

```
> runProver doubleNeg
< Just (ImpR (NegL (NegR Axiom)))
```

```
> runProver excluded
< Just (OrR ((+>) (ImpR Axiom)))
```
