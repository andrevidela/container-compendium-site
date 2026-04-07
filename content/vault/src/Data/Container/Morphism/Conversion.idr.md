<!-- idris
module Data.Container.Morphism.Conversion

import Data.Container.Definition
import Data.Container.Morphism.Definition
import Data.Container.Morphism.Eq
import Data.Container.Closed.Definition
import Data.Container.Closed.Eq

import Data.Iso
import Proofs
-->

Very importantly, they are in isomorphism with our previous definition of dependent lenses:

````lemma
Closed lenses are isomorphic to dependent lenses
````

We prove the isomorphism by providing map to and from dependent lenses.

```idris
public export
toClosed : a =%> b -> a =&> b
toClosed mor = !!
  \x => mor.fwd x  ## (\y => mor.bwd x y)

public export
fromClosed : a =&> b -> a =%> b
fromClosed (!! g) =
  (\x => (g x).π1) <!
  (\x, y => (g x).π2 y)

public export
closedIso : a =&> b ≅ (a =%> b)
closedIso = MkIso
  fromClosed
  toClosed
  (\(x <! y) => Refl)
  (\(!! fn) => cong (!!) (funExtDep $ \nx => sigmaProjId _))
```

This means that everything that worked before, works on closed lenses as well.

```idris
export 0
clsEqToDLensEq : ClosedEq m n SigEq -> fromClosed m <%≡%> fromClosed n
clsEqToDLensEq eq = rewrite clsEqToEq SigEq sigEqToEq eq in reflexive

export 0
clsEqToDLensEq' : ClosedEq (toClosed m) (toClosed n) SigEq -> m <%≡%> n
-- clsEqToDLensEq' eq = rewrite clsEqToEq SigEq sigEqToEq eq in reflexive

export 0
clsEqToPropEq : ClosedEq (toClosed m) (toClosed n) SigEqS -> m === n
```
