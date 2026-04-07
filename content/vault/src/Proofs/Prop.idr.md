<!-- idris
module Proofs.Prop

import Data.Ops

%hide Builtin.Equal
-->

### Propositional Equality

Dependently-typed programming comes with multiple notions of what it means for two
"things" to be equal. The first challenge is in determining the nature of the "thing".
In programming without dependent types, the usual notion of equality is given by
_boolean equality_ between _terms_, that is, two terms are equal if their boolean equality evaluates
to `True`.

With dependent types we have access to a stronger notion of equality, not just between
values, but also between types, because types and terms are mixed, this notion is also
very powerful to prove statements about programs.

The standard library of Idris provides a propositional equality type that states that
equality between two terms $x : a$ and $y : b$ is given by a single inhabitant whenever
$a$ and $b$ are the same type and $x$ and $y$ are the same term.

```idris
data Equal : forall a, b . a -> b -> Type where
     [search a b]
     Refl : {0 x : a} -> Equal x x
```

In addition, the library provides two aliases, one for homogenous equality whenever boths
types are known to be the same, and one when the two types are not strictly the same
but ought to be equal.

```idris
(===) : (x : a) -> (y : a) -> Type
(===) = Equal

(~=~) : (x : a) -> (y : b) -> Type
(~=~) = Equal
```

In this work, we are going to use `===` for most purposes, we also define a shorter alias
`≡`. It is worth noting that the idris compiler overloads the symbol `=` to mean both
homogenous and heterogenous equality and the compiler will automatically disambiguate between
the two. While this feature is helpful to ease the learning curve for beginners, it obscures
the intent behind our proofs, and so we will be avoid it.
