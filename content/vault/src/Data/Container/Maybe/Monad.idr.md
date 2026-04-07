<!-- idris
module Data.Container.Maybe.Monad

import Data.Category.Action
import Data.Category.Bifunctor
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Monad
import Data.Category.Monoid
import Data.Category.MonadAction

import Data.Container
import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Sequence.Monoidal as Cart
import Data.Container.ForallSeq.Action
import Data.Container.Morphism
import Data.Container.Maybe.Functor
import Data.Container.Maybe.Monoid
import Data.Container.Product
import Data.Container.Sequence.Bifunctor
import Data.Container.Sequence.Monoidal

import Data.Sigma
import Data.Product
import Data.Maybe.Any
import Data.Maybe.Monad

import Proofs.Void
import Proofs.Extensionality
import Proofs.Congruence
import Proofs.Sigma
import Proofs.Unit

%hide Data.Category.(|>)
%hide Prelude.Ops.infixl.(*>)
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
-->

### Maybe Monads

The main contribution of this work is in this module: Monads on containers.

While monads on containers aren't a surprising fact in itself, it is noteworthy
to see that they provide us with similar capabilities than monads on types and
functions, but in the realm of bidirectional programming.

The first step in defining our maybe monad is to chose the maybe functor for which
we are going to carry out the proof. For pedagical purposes, we start with proving
that the functor written using data types in idris \defref{prop:maybe-functor-idris}
is a monad. Then we will prove that $Maybe \compose \_$ is a monad via the $\compose$
monoid.

Monads are identified by their `unit : 1 -> m a` and `mult : m (m a) -> m a`
operation. Here `m` is `Maybe ▷` and `1` is the identity functor on containers
defined as `Unit :- Void`.
With this knowledge, we build the unit mapping:

```idris
unit : (a : Container) -> a =%> Any.Maybe a
unit _ = Just <! (\x, y => y.unwrap)
```

We now need to prove that `just` is _natural_, that is, given any other morphism
`m : a =%> b`, composing `unit` after `m` is the same as functorially mapping
`m` after `unit`: $m ; \text{unit}_b = \text{unit}_a ; Maybe_{Any}(m)$. Or
graphically, the following diagram commutes:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
x && {x} && {Maybe(x)} \\
\\ y && {y} && {Maybe(y)}
\arrow["{unit_x}", from=1-3, to=1-5]
\arrow["{m}"', from=1-3, to=3-3]
\arrow["{unit_y}"', from=3-3, to=3-5]
\arrow["{Maybe(m)}", from=1-5, to=3-5]
\arrow["m", from=1-1, to=3-1]
\end{tikzcd}
\end{document}
```

Programatically it means we need to implement the function:

```idris
%unbound_implicits off
MaybeAnyIsNatural : {0 a, b : Container} ->
                    (m : a =%> b) ->
                    m |%> unit b <%≡%> unit a |%> mapHom Any.MaybeF a b m
MaybeAnyIsNatural (fwd <! bwd) = MkDepLensEq
    (\arg => Refl)
    (\arg, wrg => Refl)
```

Thankfully the proofs are quite simple.

Those two functions are enough to define the first part of our monad: the unit natural transformation:

```idris
unitNT : Functor.idF Cont =>> Any.MaybeF
unitNT = MkNT
    unit
    (\_, _, arg => depLensEqToEq (MaybeAnyIsNatural arg))
```

The second part is the multiplication natural transformation, which states that for any monad $m$ we have $m (m\ a) \to m\ a$, in our case, this takes the form of a morphism
```idris
public export
mult : (x : Container) -> Any.Maybe (Any.Maybe x) =%> Any.Maybe x
mult container = joinMaybe <! anyJoin
```

It is left to prove that `join` is natural, we do the same as we did for unit:

```idris
JoinIsNatural : {0 a, b : Container} ->
    (m : a =%> b) ->
    mapHom Any.MaybeF (Any.Maybe a) (Any.Maybe b) (mapHom Any.MaybeF a b m) |%> mult b
    <%≡%> mult a |%> mapHom Any.MaybeF a b m
```

Which is the expected naturality square $\text{MaybeAny} (\text{MaybeAny}(m)) ; mult = mult ; (\text{MaybeAny}(m))$.

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
x && {Maybe(Maybe (x))} && {Maybe(x)} \\
\\ y && {Maybe(Maybe(y))} && {Maybe(y)}
\arrow["{mult_x}", from=1-3, to=1-5]
\arrow["{Maybe(Maybe(m))}"', from=1-3, to=3-3]
\arrow["{mult_y}"', from=3-3, to=3-5]
\arrow["{Maybe(m)}", from=1-5, to=3-5]
\arrow["m", from=1-1, to=3-1]
\end{tikzcd}
\end{document}
```

The proof of this square is a bit more involved and is left in appendix.

```idris {hidden=""}
JoinIsNatural m = MkDepLensEq
    (\case Nothing => Refl ; (Just _) => Refl)
    (\case Nothing => \x => absurd x
           (Just x) => \_ => Refl)

joinCommutes : (0 x, y : Container) -> (m : x =%> y) ->
  let 0 top : Any.Maybe (Any.Maybe x) =%> Any.Maybe x
      top = mult x

      0 bot : Any.Maybe (Any.Maybe y) =%> Any.Maybe y
      bot = mult y

      0 left : Any.Maybe (Any.Maybe x) =%> Any.Maybe (Any.Maybe y)
      left = mapHom (Any.MaybeF ⨾⨾ Any.MaybeF) x y m

      0 right : Any.Maybe x =%> Any.Maybe y
      right = mapHom Any.MaybeF x y m

  in top |%> right <%≡%> left |%> bot
joinCommutes x y m = MkDepLensEq
    (\case Nothing => Refl
           (Just z) => Refl)
    (\case Nothing => \y => absurd y
           (Just z) => \_ => Refl)
```
```idris
joinNT : (Any.MaybeF ⨾⨾ Any.MaybeF) =>> Any.MaybeF
joinNT = MkNT
  mult
  (\a, b, m => depLensEqToEq (joinCommutes a b m))
```

Equipped with those two natural transformation, and the `MaybeAny` functor, we have proven that our functor is also a monad. We can make sure of that fact by building a value of type `Monad` \defref{def:monad}

```idris
MaybeAnyMonad : Monad Cont Any.MaybeF
MaybeAnyMonad = MkMonad
  { unit = unitNT
  , mult = joinNT
  , square = \c => depLensEqToEq (monadSquare c)
  , identityLeft = \c => depLensEqToEq $ MkDepLensEq (\_ => Refl) (\_, _ => Refl)
  , identityRight = \c => depLensEqToEq $ MkDepLensEq
      (\case Nothing => Refl
             (Just x) => Refl)
      (\case Nothing => \x => absurd x
             (Just x) => \(Aye y) => Refl)
  }
  where
    monadSquare : (x : Container) ->
                  (Any.mapMaybe (mult x) |%> mult x)
                  <%≡%>
                  (mult (Any.Maybe x) |%> mult x)
    monadSquare x = MkDepLensEq
        (\case Nothing => Refl
               (Just y) => Refl)
        (\case Nothing => \y => absurd y
               (Just y) => \_ => Refl)
```

#### Maybe Monad arising from the `Maybe` Monoid

All this effort can be saved by deriving the monad instance from
the monoidal structor of $MaybeCont$ in $\Cont$.

First we build a self-action in $\Cont$ from the monoidal
structure of $\compose$.

```idris
MaybeMonoidAction : Action Cont Cont SequenceMonoidal
MaybeMonoidAction = monoidalSelfAction SequenceMonoidal
```

Then we turn the action into a lax-action and use that
to produce the monad. The monoid object is given by the
fact that $MaybeCont$ is a monoid with regards to the
$\compose$ monoidal structure in $\Cont$

```idris
namespace Any
  public export
  MaybeMonad : Monad Cont MaybeSeq
  MaybeMonad =
    MonadFromLaxAction ? ? Cont Cont SequenceMonoidal
      (relax MaybeMonoidAction) Cont.MaybeMonoidCompose
```

We do the same for the `All.Maybe` monad as the partially
applied functor $MaybeCont \forallSeq \_$.

```idris
namespace All
  MaybeMonad : Monad Cont MaybeAllSeq
  MaybeMonad =
    MonadFromLaxAction Container Container ContCart Cont
      Cart.SequenceMonoidal
      ForallLaxAction
      Cart.MaybeMonoidCompose
```
