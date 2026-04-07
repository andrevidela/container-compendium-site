<!-- idris
module Data.Category.Bifunctor.Apply

import Data.Category.Bifunctor
import Data.Category.NaturalTransformation

-->
#### Bifunctor Application

Given a bifunctor $F : A * B → C$ and a morphism in $A$ $m : A(x, y)$ we can build the natural
transformation $F(x) ⇒ F(y)$, where $F(x), F(y) : B \to C$ by using $F(m, id)$ as the component of the natural transformation.

````proposition
Given a bifunctor $F : \cat{C} * \cat{D} → \cat{E}$ and a morphism $\mor{C}{x}{y}$, then we can deduce the natural transformation
$F (x, \_) ⇒ F(y,\_)$
````

```idris
public export
applyNT : {0 o1, o2, o3 : Type} ->
          {c1 : Category o1} -> {c2 : Category o2} -> {0 c3 : Category o3} ->
          {x, y : o1} ->
          (x ~> y) -> (f : Bifunctor c1 c2 c3) ->
          applyL {a = c1} x f =>> applyL {a = c1, b = c2} y f
applyNT mor bi = MkNT
    (\vx => bi.mapHom (x && vx) (y && vx) (mor && c2.id vx) )
    (\a, b, g => bimapIdSwap ? ? ? mor g bi )

public export
applyId : {0 o1, o2, o3 : Type} ->
          {a : Category o1} -> {b : Category o2} -> {c : Category o3} ->
          (f1, f2 : a × b ->> c) -> (x : o1) -> f1 =>> f2 ->
          applyL {a, b, c} x f1 =>> applyL {a, b, c} x f2
applyId f1 f2 x y = MkNT
    (\vx => y.component (x && vx))
    (\dom, cod, m => y.commutes (x && dom) (x && cod) (a.id x && m) )
```
