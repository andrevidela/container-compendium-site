<!-- idris
module Data.Iso.Generic

import public Control.Relation
import public Control.Order
-->

### Generic Isomorphisms

We can extend the definition of isomorphism to work for any carrier type, morphisms and any equivalence relation between morphisms.

````definition
Given:

- a carrier type $c ∈ Set$
- a preorder relation $(\rightsquigarrow, \circ, id)$  on $c$ playing the role of morphisms
- a relation $(\approx): ∀ x, y ∈ c. x \rightsquigarrow y → x \rightsquigarrow y → Set$, playing the role of equality between morphisms

A general isomorphism between $a, b ∈ c$ is given by two maps $to : a \rightsquigarrow b$ and $from : b \rightsquigarrow a$ such that the following two relations hold $from \circ to \approx id$ and $to \circ from \approx id$

```idris {hidden=""}
%unbound_implicits off
public export
```

```idris
record GenIso (0 carrier : Type)
              (0 mor : Rel carrier)
              (0 equ : {0 x, y : carrier} -> Rel (mor x y))
              {auto tx : Transitive carrier mor}
              {auto rx : Reflexive carrier mor}
              (left, right : carrier) where
  constructor MkGenIso
  to : left `mor` right
  from : right `mor` left
  0 toFrom : (to `Relation.transitive` from) `equ` Relation.reflexive
  0 fromTo : (from `Relation.transitive` to) `equ` Relation.reflexive
```
````

In the idris definition we do not require the `equ` relation to be an
equivalence relation, because we do not make use of its properties in the
signature of the fields. In practice, there is always an equivalent relation in
scope at use-site.

```

refl : {0 c : Type} -> {0 m : Rel c} -> {0 e : {0 x, y : c} -> Rel (m x y)} ->
  (tx : Transitive c m) => (rx : Reflexive c m) =>
  {x : c} ->
  GenIso c m e {tx, rx} x x

export
{0 c : Type} -> {0 m : Rel c} -> {0 e :{0 x, y : c} -> Rel (m x y)} ->
  (tx : Transitive c m) => (rx : Reflexive c m) =>
  Reflexive c (GenIso c m e {tx} {rx}) where
    reflexive = ?ddd

trans : {0 c : Type} -> {0 m : Rel c} -> {0 e : {0 x, y : c} -> Rel (m x y)} ->
  (tx : Transitive c m) => (rx : Reflexive c m) =>
  {x, y, z : c} ->
  (f : GenIso c m e {tx, rx} x y) ->
  (g : GenIso c m e {tx, rx} y z) ->
  GenIso c m e x z
trans f g = ?trans_rhs

export
{0 c : Type} -> {0 m : Rel c} -> {0 e :{0 x, y : c} -> Rel (m x y)} ->
  (tx : Transitive c m) => (rx : Reflexive c m) =>
  Transitive c (GenIso c m e {tx} {rx}) where
  transitive f g = trans f g

sym : {0 c : Type} -> {0 m : Rel c} -> {0 e : {0 x, y : c} -> Rel (m x y)} ->
  (tx : Transitive c m) => (rx : Reflexive c m) =>
  {x, y : c} ->
  GenIso c m e {tx, rx} x y ->
  GenIso c m e {tx, rx} y x

export
{0 c : Type} -> {0 m : Rel c} -> {0 e :{0 x, y : c} -> Rel (m x y)} ->
  (tx : Transitive c m) => (rx : Reflexive c m) =>
  Symmetric c (GenIso c m e {tx} {rx}) where
    symmetric = ?symImpl

export
[ContIsoPre] {0 c : Type} -> {0 m : Rel c} -> {0 e :{0 x, y : c} -> Rel (m x y)} ->
  (tx : Transitive c m) => (rx : Reflexive c m) =>
  Preorder c (GenIso c m e {tx} {rx}) where
```
