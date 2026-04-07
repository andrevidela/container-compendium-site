<!-- idris
module Interactive.Tactics

import Data.Container
import Data.Container.Category
import Data.Category.Functor
import Data.Container.Descriptions.Maybe
import Data.Container.Maybe.Functor
import Data.Container.Maybe.Definition
import Data.Container.Closed
import Data.Container.Closed.Definition
import Data.Container.Closed.Maybe.Functor
import Data.Container.Closed.Maybe.Monad
import Data.Container.Closed.Tensor
import Data.Container.Closed.Tensor.Bifunctor
import Data.Container.Closed.Tensor.Monoidal
import Data.Container.Tensor.Definition
import Data.Product
import Data.Sigma
import Data.Maybe
import Data.Maybe.Any
import Proofs.Sigma

import Decidable.Equality

%hide Prelude.(&&)

%default total
-->


## A Tactical System for Equations

We demonstrate the effectiveness containers as a framework for tactics by implementing tactics for a simple equational system with natural numbers as terms.

Numbers in this system can be built in three ways:

- We can directly build the number for `zero`.
- We can build the successor of a number given any other number.
- We can add two numbers together.

We represent those three cases via the constructors `Zero`, `Succ` and `(+)` for `Term`.

```idris
data Term : Type where
  Zero : Term
  Succ : Term -> Term
  (+) : Term -> Term -> Term
```

An equality of terms is given by the following data with values for every way to prove that two numbers are equal:

```idris
data Eq : Term -> Term -> Type where
```

- Every number is equal to itself.

```idris
  Refl : Eq t t
```
- Proofs of equalities are transitive, that is given $a = b$ and $b = c$ we get $a = c$.
```idris
  Trans : Eq r s -> Eq s t -> Eq r t
```
- Proofs are congruent with regard to the `Succ` constructor.
```idris
  Cong : Eq t s -> Eq (Succ t) (Succ s)
```
- Given two proofs of equality, their sum is also an equality.
```idris
  CPlus : Eq t s -> Eq x y -> Eq (t + x) (s + y)
```
- Proofs of equality are symmetric.
```idris
  Sym : Eq t s -> Eq s t
```
- Given three proofs of equality, their sum is associative.
```idris
  Assoc : Eq t1 t2 -> Eq r1 r2 -> Eq s1 s2 ->
          Eq ( t1 + (r1  + s1))
             ((t2 +  r2) + s2)
```

### Primitive Tactics

With the above definition we can write the container that represents an equational problem. An equational problem has pairs of terms as _questions_ and proofs of equality as _responses_.

```idris
EqProblem : Container
EqProblem = (t : Term * Term) !> uncurry Eq t
```

Using this container, we can build tactics that will attempt to resolve the problem, or break it down into subproblems. Starting easy, the `sym` tactic says that to solve a problem, it is enough to solve its symmetric.

```idris
sym : EqProblem =&> EqProblem
sym = !! \x => swap x ## Sym
```

The above is an example of a tactic that always succeeds, it can always be applied to any problem. But most commonly, tactics can fail if the problem does not have the right shape. For this we use the _Maybe_ monad on containers.

This is done for the `refl` tactic, this tactic attempts to apply the `Refl` proof to the problem, attempting to solve it immediately. Of course, this tactic only succeeds if both sides of the equations are the definitionally equal. We give the type for this tactic as a morphism into `Maybe I`
```
refl : EqProblem =&> Any.Maybe I
```

To implement this tactic we need a couple of helper functions, first we need a semi-decidable property for `Term`.

```idris
eq : (t, s : Term) -> Maybe (t === s)
eq Zero Zero = Just Refl
eq (Succ x) (Succ y) = map (\w => cong Succ w) (eq x y)
eq (x + y) (a + b) = do Refl <- eq x a
                        Refl <- eq y b
                        Just Refl
eq _ _ = Nothing
```

Once the busywork is done we can write the tactic by running a test of equality on the
forward part, and then rebuild the proof in the backward part. Note that, thanks to the nature of the `Maybe` monad on containers, we only ever worry about the case where the two terms have a proof that they are equal.

```idris
refl : EqProblem =&> Any.Maybe I
refl = !! \x => case eq x.π1 x.π2 of
                     Nothing => Nothing ## absurd
                     Just p => Just () ## (\_ => rewrite p in Refl)
```

The transitive property of equations can be used to build a tactic that will attempt to break down an equation $a = c$ into two equations $a = b$ and $b = c$ as long as
$b$ is provided in advance. If the two subproblems $a = b$ and $b = c$ can be resolved, then we can build the larger proof $a = c$ via transitivity. This is a prime example of a tactic that breaks down a problem into two subproblems.

```idris
trans : (term : Term) -> EqProblem =&> (EqProblem ⊗ EqProblem)
trans term = !! \x => ((x.π1 && term) && (term && x.π2)) ## uncurry Trans
```

The `assoc` tactic also breaks down an existing problem into subproblems but it can itself fail. This is because the associativity tactic can only work in a problem with the shape $a + (b + c) = (d + e) + f$. If that is the case, then the problem can be resolved if we obtains proofs $a = d$, $b = e$ and $c = f$.

The type of this tactic is then:

```idris
assoc : EqProblem =&> Any.Maybe (EqProblem ⊗ (EqProblem ⊗ EqProblem))
assoc = !! \case ((a + (b + c)) && ((a' + b') + c')) =>
                     Just ((a && a') && (b && b') && (c && c')) ##
                       \(Aye (x1 && x2 && x3)) => Assoc x1 x2 x3
                 _ => Nothing ## absurd
```

The tactic matches on its argument to ensure it handle problems of the appropriate shape. Because associativity can only be applied to problem `a + (b + c)` we match
on the incoming problem and extract the values for `a`, `b`, and `c`. If the problem does not have the right shape, we return `Nothing` and the tactic fails.


```idris {hidden=""}
combineUnits : Any.Maybe I ⊗ Any.Maybe I =&> Any.Maybe I
combineUnits = Any.strengthL {a = I, b = Any.Maybe I}
    |&> Any.mapMaybe {a = I ⊗ Any.Maybe I, b = Any.Maybe I} unitL
    |&> Any.join {a = I}

tripleRight : a ⊗ a =&> a -> a ⊗ (a ⊗ a) =&> a
tripleRight m = Data.Container.Closed.Tensor.Bifunctor.(~⊗~) (Data.Container.Closed.Definition.identity a) m |&> m
```

### User Defined Tactics

The rich monoidal structure on containers and their morphisms forms combinators that can be used to build larger tactics from smaller ones. For example, we can build
a tactic that will attempt to solve the following equation, and only this one: $(x + y) + z = x + (y + z)$, for all $x, y, z$.

This is done by applying the symmetry tactic, then following it up by the associativity tactic. The associativity tactic generates three sub-problems, so we need to solve each one of them we do this by attempting to apply the reflexivity tactic, assuming that we are dealing with three variables in the same order but with a different bracketing.

The following program implements the above procedure:

```idris
assocCompose : EqProblem =&> (Any.Maybe I)
assocCompose
    = sym
    |&> assoc
    |&> Closed.Maybe.Functor.Any.mapMaybe
            ((refl ~⊗~ (refl ~⊗~ refl))
                |&> tripleRight combineUnits)
    |&> Any.join {a = I}
```

It might help to visualise the diagram that represents this computation

*Draw the diagram here*

The type of this lens indicates that it's a _leaf tactic_ and the `Maybe` monad shows that it
might fail to apply.

