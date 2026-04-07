<!-- idris
module Data.Category.Functor.Category

import Data.Category
import Data.Category.Functor
import Data.Category.Bifunctor
import Data.Category.NaturalTransformation

import Syntax.PreorderReasoning

%hide Prelude.Ops.infixl.(|>)
-->

### The category of functors and natural transformations

Because vertical composition has the shape `f =>> g -> g =>> h -> f =>> h`, we
can use it to define the category of functors as objects and natural transformations as morphisms
using vertical composition to stitch natural transformations together.
The objects of this category are functors, it is parameterised by two categories `c` and `d` that will
remain fixed such that every object is an instance of a functor from `c` to `d`. The identity morphism
is given by the identity natural transformation. It remains to prove this statement, which we do
programmatically. First, we pin down the parameters that are not going to change, that is, the categories
$\cat{C}$ and $\cat{D}$, and the functors $f, g : \cat{C} → \cat{D}$


```idris
parameters
  {0 o1, o2 : Type}
  {0 c : Category o1} {0 d : Category o2}
  {f, g : c ->> d}
```

To help with type inference, we define an alias for function composition that is specialied to the
category $\cat{D}$.

```idris
  0
  (|>>) : {x, y, z : o2} -> x ~> y -> y ~> z -> x ~> z
  (|>>) = (|:>) d
  private infixr 2 |>>
```
Then we prove the three lemmas that need to hold for this to form a category

````lemma
The identity natural transformation is neutral on the right side of vertical composition.
```idris
  public export
  ntIdentityRight :
    (n : f =>> g) -> NTEq (n ⨾⨾⨾ identity {f = g}) n
  ntIdentityRight nt = MkNTEq $ \vx => Calc $
      |~ nt.component vx |>> g.mapHom vx vx (c.id vx)
      ~~ nt.component vx |>> d.id (g.mapObj vx)
         ...(cong (nt.component vx |>>) (g.presId vx))
      ~~ nt.component vx
         ...((d.idRight _ _ _))
```
````

````lemma
The identity natural transformation is neutral on the left side of vertical composition.
```idris
  public export
  0 ntIdentityLeft :
    (n : f =>> g) -> NTEq (NaturalTransformation.identity ⨾⨾⨾ n) n
  ntIdentityLeft nt = MkNTEq $ \v =>
      Calc $ |~ f.mapHom v v (c.id v) |>> nt.component v
             ~~ d.id (f.mapObj v)     |>> nt.component v
                ...(cong (|>> nt.component v) (f.presId v))
             ~~ nt.component v
                ...(d.idLeft _ _ (nt.component v))
```
````
````lemma
Vertical composition of natural transformations is associative.
```idris
  public export
  0 ntAssoc :
      {h, i : c ->> d} ->
      (n1 : f =>> g) -> (n2 : g =>> h) -> (n3 : h =>> i) ->
      NTEq (n1 ⨾⨾⨾ (n2 ⨾⨾⨾ n3)) ((n1 ⨾⨾⨾ n2) ⨾⨾⨾ n3)
  ntAssoc (MkNT n1 p1) (MkNT n2 p2) (MkNT n3 p3) = MkNTEq $ \v =>
      (d.compAssoc _ _ _ _ (n1 v) (n2 v) (n3 v))
```
````

Using those lemma we can build the functor category parameterised over two
categories $\cat{C}$ and $\cat{D}$. The objects are functors $\cat{C} \to\cat{D}$
and morphisms are natural transformation.

<!-- idris
public export
-->

````proposition {label="prop:functorCat"}
Given categories $\cat{C}$ and $\cat{D}$, we define the category of functors as objets
and natural transformations as morphisms, composed via vertical composition.
```idris
FunctorCat : (c1 : Category a) -> (c2 : Category b) -> Category (c1 ->> c2)
FunctorCat c1 c2 = MkCategory
    (=>>)
    (\f => identity {f})
    (⨾⨾⨾)
    (\f, g, n => ntEqToEq $ ntIdentityRight n)
    (\f, g, n => ntEqToEq $ ntIdentityLeft n)
    (\f, g, h, i, nt1, nt2, nt3 =>
        ntEqToEq $ ntAssoc nt1 nt2 nt3
    )
```
````

