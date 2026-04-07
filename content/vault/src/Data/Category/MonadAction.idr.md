## Monads From Actions

After studying both monads and actions, we can build the next result: how to
produce monadsa given a categorical action.

````theorem {label="thm:monad-action"}
Given a monoidal category $\cat{C}$ $(\otimes, I, α, l, r)$, a monoid $m \in\cat{C}$, and an action $(\oslash : \cat{C}\times\cat{D}\to\cat{D}, act, i)$ of this monoidal category on $\cat{D}$, then the partially applied functor $m \oslash \_:\cat{D}\to\cat{D}$ is a monad.
````

To produce a monad we need to give its functor and its two natural
transformations. For this, we first make precise what we have available before
we define the functor. We will need:

- A category $\cat{D}$
- A monoidal category $\cat{C}$ with $( ⊗ : C × C → C, I ∈ C)$
- A monoid $m ∈ \cat{C}$
- A monoidal action $(\oslash : \cat{C} \times \cat{D} \to \cat{D}, act : x ⊘ (y ⊘ z) -> (x ⊗ y) ⊘ z , e : x -> I ⊘ x)$

Using the above, we can define a functor $T : \cat{D} →\cat{D}$ by
partially applying our action to our monoid $m$, in other words, $T (x) = m \oslash
x$.

This allows us to write explicitly what the natural tranformations of a suitable
monad should be. The monadic unit $\eta : Id(x) ⇒ T(x)$ can be written as $Id(x)
⇒ m \oslash x$ is given by the lax unitor $e$. Similarly, the monadic multiplication
$μ : T (T(x)) ⇒ T(x)$ can be written as $(m \oslash (m \oslash x)) ⇒ (m \oslash x)$
and is given by composing the actor of the action with the monoidal multiplication
$act ; (⊗ × id)$.

```tikz {caption="The definition of monad multiplication for a monad emerging from an action" label="fig:monad-action-mult"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\providecommand{\unitordiagram}[6]{
  \begin{tikzcd}[ampersand replacement=\&]
    {#1}
    \\ \\
    {#2} \&\& {#3}
    \arrow["{#4}"', from=1-1, to=3-1]
    \arrow["{#5}", from=1-1, to=3-3]
    \arrow["{#6}"', from=3-1, to=3-3]
  \end{tikzcd}
}
\begin{document}
\unitordiagram
{m \oslash (m\oslash x)} % top node
{(m \otimes m)\oslash x} % bottom left corner node
{m \oslash x} % right node
{act} % left arrow
{\mu} % diagonal arrow
{\otimes \times id_x} % bottom arrow
\end{document}
```

<!-- idris
module Data.Category.MonadAction

import Data.Category
import Data.Category.Action
import Data.Category.Monad
import Data.Category.Monoid
import Data.Category.Functor
import Data.Category.Endofunctor
import Data.Category.Bifunctor
import Data.Category.Bifunctor.Apply
import Data.Category.NaturalTransformation

import Syntax.PreorderReasoning
import Pipeline.Equality

%hide Prelude.Ops.infixl.(*>)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Functor
%hide Prelude.(|>)

%unbound_implicits off
-->

- [!] finish the diagrams programmatically

We implement monads from action in Idris by first parameterising all the
data we need.

```idris
parameters
  (0 o1, o2: Type)
  (cat1 : Category o1)
  (cat2 : Category o2)
  (mon : Monoidal cat1)
  (act : LaxAction cat1 cat2 mon)
  (m : MonoidObject {o=o1} {cat=cat1} {mon})
```

Then we define the functor that we claim is a monad, that is
$T(x) = m ⊘ x$.

<!-- idris
  public export
-->

```idris
  T : Endo cat2
  T = applyL m.obj act.laction
```
we define the unit of the monad a $Id \Rightarrow F$ by
composing vertically the unitor from the action
$x ⇒ I ⊘ x$ with the map $I ⊘ x ⇒ m ⊘ x$ emerging
from the neutral map of the monoid $e : I → m$

```idris
  unit : idF cat2 =>> T
  unit = act.lunitor ⨾⨾⨾ applyNT m.η act.laction
```

The multiplication is a map $T ; T ⇒ T$ which expands to
$m ⊘ (m ⊘ x) ⇒ m ⊘ x$. Its codomain almost matches
the actor map $x ⊘ (y ⊘ z) ⇒ (x ⊗ y) ⊘ z$
and the monoid operation on $m$ $(*) : m ⊗ m → m$ compose

We define an alias for the functor $F'(x) = (m ⊗ m) ⊘ x$

```idris
  -- the functor F'(x) = (m ⊗ m) ⊘ x
  F' : Endo cat2
  F' = applyL {a = cat1} ((m.obj ⊗ m.obj)) act.laction
```

And we use it to define the natural transformation
$(m ⊗ m) ⊘ x ⇒ m ⊘ x$ via the multiplication of the monoid object.

```idris
  multAction : F' =>> T
  multAction = applyNT m.mult act.laction
```

We need to partially apply the actor map to be a natural transformation
$m ⊘ (m ⊘ x) ⇒ (m ⊗ m) ⊘ x)$, we can do it by applying $M$ using whiskering
but in this case it was faster to write down the map manually.

```idris
  (⊘) : o1 -> o2 -> o2
  (⊘) x y = act.laction.mapObj (x && y)
  private infixr 3 ⊘

  (~⊘~) : {x, y : o1} -> {z, w : o2} -> (x ~> y) {cat=cat1} -> z ~> w -> x ⊘ z ~> y ⊘ w
  (~⊘~) m1 m2 = act.laction.mapHom (x && z) (y && w) (m1 && m2)
  private infixr 3 ~⊘~

  actor : (x, y : o1) -> (z : o2) -> x ⊘ (y ⊘ z) ~> (x ⊗ y) ⊘ z
  actor x y z = act.lactor.component (x && (y && z))

  unitor : (x : o2) -> x ~> mon.i ⊘ x
  unitor x = act.lunitor.component x

  private infixr 3 ⊘>

  -- This could be done with careful composition of act.lactor and some lemmas about apply
  -- but writing out the definition is actually easier
  appActor : T ⨾⨾ T =>> F'
  appActor = MkNT
    (\v => actor m.obj m.obj v)
    (\x, y, h => let
      0 steps : CongPipeline ? ?
      steps =
         Cong (\vx =>
            (actor m.obj m.obj x) |>
            (vx ~⊘~ h))
              [ cat1.id (m.obj ⊗ m.obj)
              , cat1.id m.obj -⊗- cat1.id m.obj]
         >| ((cat1.id m.obj ~⊘~ (cat1.id m.obj ~⊘~ h)) |>
            (actor m.obj m.obj y))
         :: Nil
      in runProof steps
        [ sym (mon.mult.presId (m.obj && m.obj))
        , act.lactor.commutes
            (m.obj && (m.obj && x))
            (m.obj && (m.obj && y))
            (cat1.id m.obj && (cat1.id m.obj && h))
        ]
    )
```

Using the applied actor map and the action we obtain the multiplication morphism of our monad

```idris
  mult : T ⨾⨾ T =>> T
  mult = appActor ⨾⨾⨾ multAction
```

Those definitions bring us to the definition of $m ⊘ \_$ as a monad in $\cat{D}$, the
coherence diagrams are left in appendix.

- [ ] complete squares

```idris {hidden=""}
  0 square : (x : o2) -> let
      0 top : T .mapObj (T .mapObj (T .mapObj x)) ~> T .mapObj (T .mapObj x)
      top = T .mapHom _ _ (mult.component x)
      0 bot, right : T .mapObj (T .mapObj x) ~> T .mapObj x
      right = mult.component x
      bot = mult.component x
      0 left : T .mapObj (T .mapObj (T .mapObj x)) ~> T .mapObj (T .mapObj x)
      left = mult.component (T .mapObj x)
      0 arm2, arm1 : T .mapObj (T .mapObj (T .mapObj x)) ~> T .mapObj x
      arm1 = (top |> right) {cat = cat2}
      arm2 = left |> bot
      in arm1 === arm2
  square x = Calc $
    |~
       (
         (cat1.id m.obj
           ~⊘~
         (actor m.obj m.obj x
           |>
         (m.mult ~⊘~ cat2.id x))))
       |>
         ((actor m.obj m.obj x)
           |>
           (m.mult ~⊘~ cat2.id x))
    ~~ ((actor m.obj m.obj (m.obj ⊘ x))
         |>
         (m.mult ~⊘~ cat2.id (m.obj ⊘ x)))
       |>
       ((actor m.obj m.obj x)
         |>
         (m.mult ~⊘~ cat2 .id x))
    ...(?squarePrf)



  0 identityLeft : (x : o2) -> let
      0 compose : T .mapObj x ~> T .mapObj x
      compose = (unit.component (T .mapObj x) |> mult.component x) {cat = cat2}
      0 straight : T .mapObj x ~> T .mapObj x
      straight = cat2.id (T .mapObj x)
      in compose === straight
  identityLeft x = Calc $
    |~ ((unitor (m.obj ⊘ x))
         |>
        (m.η ~⊘~ cat2.id (m.obj ⊘ x)))
      |>
       ((actor m.obj m.obj x)
         |>
        (m.mult ~⊘~ cat2.id x))
    ~~ cat2.id (m.obj ⊘ x)
    ...(?bee)

  0 identityRight : (x : o2) -> let
      0 compose : T .mapObj x ~> T .mapObj x
      compose = (T .mapHom _ _ (unit.component x) |> mult.component x) {cat = cat2}
      0 straight : T .mapObj x ~> T .mapObj x
      straight = cat2.id (T .mapObj x)
      in compose === straight
  identityRight x = Calc $
    |~
       (cat1.id m.obj ~⊘~ ((unitor x) |> (m.η ~⊘~ cat2.id x)))
       |>
       (
         (actor m.obj m.obj x)
         |>
         ((m.mult ~⊘~ cat2.id x))
       )
    ~~ cat2 .id (m.obj ⊘ x)
    ...(?idRPrf)


```

- [ ] finish the coherence diagrams in idris

<!-- idris
  public export
-->
```idris
  MonadFromLaxAction : Monad cat2 T
  MonadFromLaxAction = MkMonad unit mult square identityLeft identityRight
```
