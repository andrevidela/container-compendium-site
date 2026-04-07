<!-- idris
module Proofs.Sigma

import public Data.Sigma
import Data.Ops
import Proofs.Congruence

import Proofs.Transport
import Proofs.Equality

public export
-->

````lemma
Projecting both sides of a sigma and building a new sigma is the same as doing nothing.
```idris
sigmaProjId : {0 a : Type} -> {0 b : a -> Type} ->
              (x : Σ a b) -> (x.π1 ## x.π2) === x
sigmaProjId ((f ## s)) = Refl
```
````

```idris {hidden=""}
public export
```

````definition
Equality between sigma types is ensure when both the first and second projection are equal.
```idris
record SigEq (a, b : Σ f s) where
  constructor MkSigEq
  fstEq : a.π1 === b.π1
  sndEq : (a.π2 ≡≡ b.π2) {p = s}

export 0
sigEqRefl : (x : Σ f s) -> SigEq x x
sigEqRefl x = MkSigEq Refl (IRefl Refl)
```
````

The equality between sigma types relies on indexed propositional equality \defref{def:ix-eq} since the second projection is indexed by the first.

```idris {hidden=""}
export
```

````lemma
We can convert from `Σ`-equality to propositional equality
```idris
0 sigEqToEq : SigEq a b -> a === b
sigEqToEq {a = _ ## _} {b = _ ## _} (MkSigEq Refl (IRefl Refl)) = Refl
```
````

```idris {hidden=""}
public export
record SigEq' (a, b : Σ f s) where
  constructor MkSigEq'
  fstEq : a.π1 === b.π1
  sndEq : a.π2 === replace {p = s} (sym fstEq) b.π2

export
0 sigEqToEq' : SigEq' a b -> a === b
sigEqToEq' {a = _ ## _} {b = _ ## _} (MkSigEq' Refl Refl) = Refl

export
0 sigEqToIxEq : SigEq a b -> (a ≡≡ b) {p = Prelude.id}
sigEqToIxEq prf = rewrite sigEqToEq prf in IRefl Refl

export
0 sigEqRefl' : (x : Σ a b) -> SigEq' x x
sigEqRefl' x = MkSigEq' Refl Refl

public export
record SigEqS (a, b : Σ f s) where
  constructor MkSigEqS
  fstEq : a.π1 === b.π1
  sndEq : a.π2 === transport s (sym fstEq) b.π2

export
0 sigEqToEqS : SigEqS a b -> a === b
sigEqToEqS {a = _ ## _} {b = _ ## _} (MkSigEqS Refl Refl)
    = cong2Dep (##) Refl (applyRefl ? ?)

public export
record IxSigEq (a, b : Σ f s) where
  constructor MkIxSigEq
  fstEq : a.π1 === b.π1
  sndEq : IEq fstEq a.π2 b.π2 {b = s}

export 0
ixSigToEq : {a : Σ f s} -> IxSigEq a b -> a ≡ b
ixSigToEq {a = (b .π1) ## _} (MkIxSigEq Refl Refl) = sigmaProjId b

export 0
sigP1 : {a : Type} -> {b : a -> Type} -> (x : a) -> (y : b x) -> ((x ## y) {a, b}).π1 === x
sigP1 _ _ = Refl

{-
export
0 sigEqToIxEq : SigEq a b -> (a ≡≡ b) {p = Prelude.id}
sigEqToIxEq prf = rewrite sigEqToEq prf in IRefl Refl

%unbound_implicits off
public export
record IxSigEq {0 a : Type} {0 ix : a} {0 f : a -> Type}
               {0 s : (j : a) -> (f j) -> Type}
               (x, y : Σ (f ix) (s ix)) where
  constructor MkIxSigEq
  fstEq : (x.π1 ≡≡ y.π1) {p = f}
  sndEq : (≡≡) {p = s ix} x.π2 y.π2

export
0 ixSigEqToEq : {0 a : Type} -> {0 ix : a} -> {0 f : a -> Type} ->
                {0 s : (j : a) -> (f j) -> Type} ->
                (x, y : Σ (f ix) (s ix)) ->
                IxSigEq {a, ix, f, s} x y -> x === y
ixSigEqToEq (x1 ## x2) (_ ## y2)
    (MkIxSigEq (IRefl Refl) sndEq) = cong (x1 ##) (iEqToEq sndEq)
```
