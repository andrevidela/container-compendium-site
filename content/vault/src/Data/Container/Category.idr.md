
<!-- idris
module Data.Container.Category

import public Data.Category
import Data.Category.Product
import Data.Category.Monoid
import Data.Category.Bifunctor
import Data.Category.NaturalTransformation
import public Data.Container.Definition
import public Data.Container.Morphism.Definition
import public Data.Container.Morphism.Eq
import Data.Sigma

import Proofs

import Syntax.PreorderReasoning

%hide Prelude.(&&)
%hide Prelude.Ops.infixl.(*>)
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
-->

````lemma
The identity lens is neutral when composed to the right.
```idris
composeIdRight : (f : a =%> b) -> f |%> identity b ≡ f
composeIdRight (fwd <! bwd) = Refl
```
````
````lemma
The identity lens is neutral when composed to the left.
```idris
composeIdLeft : (f : a =%> b) -> identity a |%> f ≡ f
composeIdLeft (fwd <! bwd) = Refl
```
````
````lemma
Composition of dependent lenses is associative.
```idris
proveAssoc : (f : a =%> b) -> (g : b =%> c) -> (h : c =%> d) ->
             f |%> (g |%> h) ≡ (f |%> g) |%> h
proveAssoc (fwd0 <! bwd0) (fwd1 <! bwd1) (fwd2 <! bwd2) = Refl
```
````

```idris {hidden=""}
public export
```

````proposition
Containers and dependent lenses form a category $\Cont$
```idris
Cont : Category Container
Cont = NewCat
  { objects = Container
  , morphisms = (=%>)
  , identity = (\x => identity x)
  , composition = (|%>)
  , identity_right = composeIdRight
  , identity_left = composeIdLeft
  , compose_assoc = proveAssoc
  }
```
````



