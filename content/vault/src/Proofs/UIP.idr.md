<!-- idris
module Proofs.UIP

public export
-->

Idris has no univalence axiom and assumes uniqueness of identity proofs, that is, for every proof `p1 : x = y` and `p2 : x = y` we have that `p1 = p2`. 

````definition {label="def:uip"}
Uniqueness of identity proofs.
```idris
UIP : (0 p, q : x === y) -> p === q
UIP Refl Refl = Refl
```
````

This is the same as using Agda with the option `--with-K` enabled.