<!-- idris
module Data.Container.List.Monad

import Data.Category
import Data.Category.Action
import Data.Category.Functor
import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Category.Monad
import Data.Category.Monoid
import Data.Category.NaturalTransformation
import Data.Category.MonadAction

import Data.Container
import Data.Container.Category
import Data.Container.Morphism
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.ForallSeq.Bifunctor
import Data.Container.Sequence.Monoidal
import Data.Container.ForallSeq.Action
import Data.Container.Cartesian.Sequence.Monoidal as Cart
import Data.Container.Descriptions.Maybe
import Data.Container.Descriptions.List
import Data.Container.List.Desc
import Data.Container.List.Functor
import Data.Container.List.Monoid

import Data.Fin
import Data.List
import Data.Sigma
import Data.List.Quantifiers
import Data.List.Monad
import Data.Iso

import Proofs

import Syntax.PreorderReasoning
import Pipeline.Equality

%hide Prelude.Ops.infixl.(*>)
%default total
-->

### `Forall` is a Monad

We're going to use our monad-action theorem \thmref{thm:monad-action} to generate
the witness that the `Forall` list is a monad in $\Cont$.
For this we need a couple of crucial defintion, first we need the fact that
$\forallSeq$ is a lax action, then we need a list monoid in $\ContCart$ with regards to
the monoidal structure induced by $\forallSeq$. Finally

````proposition
$Forall$ is a monad via the $\forallSeq$ action.
```idris
public export
ForallMonadCont : Monad Cont ForallFunctor
ForallMonadCont = MonadFromLaxAction ? ?
    ContCart Cont SequenceMonoidal Action.ForallLaxAction Cartesian.ListMonoid
```
````

### `Forany` is a Monad

Similarly, we're going to use the fact that for each monoidal structure in a category $\cat{C}$ and
a monoid $m ∈ \cat{C}$ the functor $m ⊗ \_$ is a monad. To apply this to the `Forany` functor we
need the monoidal structure induced by $\rhd$ on $\Cont$ as well as the monoid object $ListCont$.

We then instanciate both those facts by reusing the monad-action theorem but mapping our monoidal
category into a self-action

```idris
ListMonoidalAction : Action Cont Cont SequenceMonoidal
ListMonoidalAction = monoidalSelfAction SequenceMonoidal

ForanyMonadCont : Monad Cont ForanyFunctor
-- ForanyMonadCont = MonadFromLaxAction ? ?
--     Cont Cont SequenceMonoidal (relax ListMonoidalAction) Cont.ListMonoid
```

