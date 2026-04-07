<!-- idris
module Data.Category.Endofunctor

import Data.Category
import Data.Category.Bifunctor
import Data.Category.Functor
import Data.Category.Functor.Category
import Data.Category.NaturalTransformation as NT
import Data.Category.Monoid

import Data.Product

import Syntax.PreorderReasoning

import Pipeline.Equality

%hide Prelude.Ops.infixl.(|>)

-->


We can use the idea that a natural transformation is a mapping between functors
to reproduce facts that we know ought to work. For example, since functor composition
is associative, we should be able to define a natural isomorphism between
$(f \circ g) \circ h$ and $f \circ (g \circ h)$.

```idris
parameters
  {o1, o2, o3, o4 : Type}
  {c1 : Category o1} {c2 : Category o2} {c3 : Category o3} {c4 : Category o4}
  (f : c1 ->> c2) (g : c2 ->> c3) (h : c3 ->> c4)
  public export
  funcCompAssocNTR : (f ⨾⨾ (g ⨾⨾ h)) =>> ((f ⨾⨾ g) ⨾⨾ h)
  funcCompAssocNTR = MkNT
      (\vx => c4.id _)
      (\x, y, m => c4.idLeft _ _ _ `trans` sym (c4.idRight _ _ _) )

  public export
  funcCompAssocNTL : (f ⨾⨾ g) ⨾⨾ h =>> f ⨾⨾ (g ⨾⨾ h)
  funcCompAssocNTL = MkNT
      (\vx => c4.id _)
      (\x, y, m => c4.idLeft _ _ _ `trans` sym (c4.idRight _ _ _) )

  public export
  funcCompAssocNI : (f ⨾⨾ g) ⨾⨾ h =~= f ⨾⨾ (g ⨾⨾ h)
  funcCompAssocNI = MkNaturalIsomorphism
      funcCompAssocNTL
      funcCompAssocNTR
      (\vx => c4.idLeft _ _ _)
      (\vx => c4.idLeft _ _ _)
```

There is still more we can do, for example, we can provide mappings from
any functor that is composed with the identity, to itself, essentially
proving that the identity functor is a neutral element with regards to
functor composition when the maps are natural transformations.

```idris
parameters
  {o1, o2 : Type}
  {c : Category o1} {d : Category o2}
  {f : c ->> d}
  public export
  funcIdRNT : idF c ⨾⨾ f =>> f
  funcIdRNT = MkNT (\vx => d.id _)
    (\x, y, m => d.idLeft _ _ _ `trans` sym (d.idRight _ _ _))

  public export
  funcIdLNT : f ⨾⨾ idF d =>> f
  funcIdLNT = MkNT (\vx => d.id _)
    (\x, y, m => d.idLeft _ _ _ `trans` sym (d.idRight _ _ _))

  public export
  funcIdLNT' : f =>> f ⨾⨾ idF d
  funcIdLNT' = MkNT (\vx => d.id _)
    (\x, y, m => d.idLeft _ _ _ `trans` sym (d.idRight _ _ _))

  public export
  funcIdRNT' : f =>> idF c ⨾⨾ f
  funcIdRNT' = MkNT (\vx => d.id _)
    (\x, y, m => d.idLeft _ _ _ `trans` sym (d.idRight _ _ _) )
```

- [ ] shouldn't this be about the bicategory of sets, functors and natural transformations?

Actually the above help us define the monoidal category of endofunctors,
unlike `FunctorCat`, we fix one category $\mathcal{C}$ instead of two, and objects
are endofunctors $\mathcal{C}\to\mathcal{C}$

## Endofunctors

We define _endofunctors_ as functors with the same
source and target. Here we make this a bit more precise by giving a function `Endo` that
will only build endofunctors. With this we can build the category `EndoCat` of endofunctors
as objects and natural transformations as morphisms

````definition {label="def:endofunctor"}
Endofunctors are functors with the same source and target.
```idris
public export
Endo : Category o -> Type
Endo c = c ->> c
```
````

````proposition
There is a category of endofunctors where the objects are endofunctors and the morphisms
                                          are natural transformations between endofunctors.

```idris
public export
EndoCat : (c : Category o) -> Category (Endo c)
EndoCat c = FunctorCat c c
```
````
