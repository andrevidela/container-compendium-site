## Monads

A monad is a complex property that requires everything we previously defined, we need to know about categories \defref{def:category}, functors \defref{def:functor}, and natural transformations \defref{def:natural-transformation}. Being a monad is a property of _functors_, in particular, endofunctors \defref{def:endofunctor}. Before we jump into the definition, let us study a small programming example.

<!-- idris
module Data.Category.Monad

import Data.Category
import Data.Category.NaturalTransformation
import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Category.Monoid
import Control.Relation

import Syntax.PreorderReasoning

%hide Prelude.Ops.infixl.(*>)
%hide Prelude.Monad
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
-->


The type `List : Type -> Type` is a functor
in the category of types and functions, because it has a function `map : (a -> b) -> List a -> List b` which transports any function `a -> b` into a function that operates on lists. What makes it a functor is that the `map` function respects the functor laws.

What is more, the `List` type also has functions `flatten : List (List a) -> List a` and `singleton : a -> List a`. The first one collapses nested lists into one, preserving the order of elements, and the second one create a list with a single element in it. If those two functions obey the monad properties, then we say that `List` is a monad. The key properties are that flattening a doubly-nested list can be done in two ways without affecting the result, either by flattening twice in a row, or by flattening the inner nested list first, and then flattening what is left. In other words `(xs : List a) -> flatten (flatten xs) = flatten (map flatten xs)`.  We also require that calling `singleton` on a list, and then flattening is the same as calling `singleton` on each element of a list, and then flattening, both of those operations should be equivalent to doing nothing. In summary:
`(xs : List a) -> flatten (singleton xs) = xs = flatten (map singleton xs)`


We can generalise this notion for any functor $m : \mathcal{C} \to \mathcal{C}$ , the functions `flatten` and `singleton` become natural transformations that we call `mult` and `unit` respectively.

````definition {label="def:monad"}
Given a category $\cat{C}$ and an endofunctor $F : \cat{C}\to\cat{C}$, $F$ is a monad if we have the following two natural transformations:

- $unit : Id_{\cat{C}} \Rightarrow F$ where $Id : \cat{C} \to\cat{C}$ is the identity functor on $\mathcal{C}$
- $mult : F\comp F \Rightarrow F$ where $(\comp)$ is the composition of functors

As well as the following conditions:

- $mult \vcomp mult = (Id_F \hcomp mult) \vcomp mult$
- $mult \vcomp unit = mult \vcomp (Id_F \hcomp unit)$

Where $Id_F$ is the identity natural transformation $F \Rightarrow F$.
````

We put all those pieces together to define monads:

<!-- idris
public export
-->
```idris {label="def:idris-monad"}
record Monad (c : Category o) (endo : Endo c) where
  constructor MkMonad
  unit : idF c =>> endo
  mult : (endo ⨾⨾ endo) =>> endo
```


Not only we need to define $unit$ and $mult$ but we also need to ensure they respect some properties, the first one is that
$mult$ can be applied in any order given a term $f(f(f(x)))$. Either it can be applied twice in succession, or it can be applied
first as the map on morphism from the functor $F$ such that $F(mult) : f(f(f(x))) \to f(f(x))$, and then applied directly on
the result. This property is similar to the associativity property of monoids.

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{f(f(f(x)))} && {f(f(x))}
\\
\\ {f(f(x))} && {f(x)}
\arrow["{F(mult_x)}", from=1-1, to=1-3]
\arrow["{mult_{f(x)}}"', from=1-1, to=3-1]
\arrow["{mult_x}", from=1-3, to=3-3]
\arrow["{mult_x}"', from=3-1, to=3-3]
\end{tikzcd}
\end{document}
```

```idris
  0 square : (x : o) -> let
      0 top : endo.mapObj (endo.mapObj (endo.mapObj x)) ~> endo.mapObj (endo.mapObj x)
      top = endo.mapHom _ _ (mult.component x)
      0 bot, right : endo.mapObj (endo.mapObj x) ~> endo.mapObj x
      right = mult.component x
      bot = mult.component x
      0 left : endo.mapObj (endo.mapObj (endo.mapObj x)) ~> endo.mapObj (endo.mapObj x)
      left = mult.component (endo.mapObj x)
      0 arm2, arm1 : endo.mapObj (endo.mapObj (endo.mapObj x)) ~> endo.mapObj x
      arm1 = (top |> right) {cat = c}
      arm2 = left |> bot
      in arm1 === arm2
```

Next, we ensure that $unit$ and $mult$ interact appropriately with each other,
so that from $f(x)$ we can apply $unit$ on either the whole expression $f(x)$
and obtain $f(f(x))$, or apply it to the inner $x$ using the map on morphism
from the functor $F$ to obtain $f(f(x))$. Either way, applying $mult$ should
result in the same $f(x)$ in the end. We visualise this property with the
following commutative diagram.

  ```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{f(x)} && {f(f(x))} \\
\\
{f(f(x))} && {f(x)}
\arrow["unit_{f(x)}", from=1-1, to=1-3]
\arrow["{F(unit_x)}"', from=1-1, to=3-1]
\arrow[from=1-1, to=3-3, equals]
\arrow["mult", from=1-3, to=3-3]
\arrow["mult"', from=3-1, to=3-3]
\end{tikzcd}
\end{document}
```
```idris
  0 identityLeft : (x : o) -> let
      0 compose : endo.mapObj x ~> endo.mapObj x
      compose = (unit.component (endo.mapObj x) |> mult.component x) {cat = c}
      0 straight : endo.mapObj x ~> endo.mapObj x
      straight = c.id (endo.mapObj x)
      in compose === straight

  0 identityRight : (x : o) -> let
      0 compose : endo.mapObj x ~> endo.mapObj x
      compose = (endo.mapHom _ _ (unit.component x) |> mult.component x) {cat = c}
      0 straight : endo.mapObj x ~> endo.mapObj x
      straight = c.id (endo.mapObj x)
      in compose === straight
```

This definition of monad is complete, but there is a dual to monad called *comonads* which we define next.

## Comonad

Being the dual of a monad, the comonad contains all the same information as a monad, but flipped. We still have an endofunctor $F : \cat{C}\to\cat{C}$ but instead of $unit : a → F (a)$ and $mult : F (F (a)) → F(a)$ we have $extract : F(a) → a$ and $duplicate : F(a) → F (F (a))$

````definition {label="def:comonad"}
A Comonad is the dual of a monad.
```idris
public export
record Comonad (c : Category o) (endo : Endo c) where
  constructor MkCoMonad
  extract : endo =>> idF c
  duplicate : endo =>> endo ⨾⨾ endo

  idL : let
         0 ηT : (endo ⨾⨾ endo) =>> endo
         ηT = (extract -⨾ endo) ⨾⨾⨾ funcIdRNT
         in (duplicate ⨾⨾⨾ ηT) `NTEq` identity {f = endo}
  idR : let
         0 Tη : endo ⨾⨾ endo =>> endo
         Tη = (endo ⨾- extract) ⨾⨾⨾ funcIdLNT
         in (duplicate ⨾⨾⨾ Tη) `NTEq` identity {f = endo}
  comp : let
         0 whiskL : endo ⨾⨾ endo =>> endo ⨾⨾ (endo ⨾⨾ endo)
         whiskL = (endo ⨾- duplicate) {a = c, b = c, c = c, g = endo , h = endo ⨾⨾ endo}
         0 whiskR : endo ⨾⨾ endo =>> endo ⨾⨾ (endo ⨾⨾ endo)
         whiskR = (duplicate -⨾ endo) ⨾⨾⨾ funcCompAssocNTL _ _ _
         in whiskL `NTEq` whiskR
```
````

- [ ] add the comonad laws
