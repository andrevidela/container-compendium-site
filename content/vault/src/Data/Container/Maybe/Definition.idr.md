<!-- idris
module Data.Container.Maybe.Definition

import Data.Container.Definition
import public Data.Maybe.Any
import public Data.Maybe.All
-->

### Maybe Functors

There are two `Maybe` functors in $\Cont$ and 3 ways to define them each. We start with the most straightforward definition.

````definition
The "Maybe any" functor $Maybe_{Any} (A, \bar{A}) \mapsto (m : Maybe\ A, Any\ \bar{A}\ m)$ maps queries into queries that can fail, and responses into responses that must be present.
```idris
namespace Any
  public export
  Maybe : Container -> Container
  Maybe c = (x : Maybe c.request) !> Any c.response x
```
````

````definition
The "Maybe all" functor $Maybe_{All} (A, \bar{A}) \mapsto (m : Maybe\ A, All\ \bar{A}\ m)$ maps queries into queries that can fail, and responses into optional responses.
```idris
namespace All
  public export
  Maybe : Container -> Container
  Maybe c = (x : Maybe c.request) !> All c.response x
```
````

Those definitions rely on the `All` \defref{def:maybe-all} and `Any` \defref{def:maybe-any} types that transform a predicate to run conditionally on a `Maybe` value.
