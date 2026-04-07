```idris
import Data.Boundary
import Data.Sigma
import Data.Vect
import Data.Product
import Data.Iso

import Data.Container
import Data.Container.Descriptions.List
import Data.Container.Morphism
import Data.Container.Morphism.Closed

import Proofs.Extensionality
import Proofs.Congruence
import Proofs.Sigma
```

### Traversals are Closed lenses

The first observation to make is that the implementation of traversals is already formulated
in a way that is compatible with closed lenses \defref{def:closed-lens}. As a reminder, here is the
definition of traversal.

```idris
record Traversal (a, b : Boundary) where
  constructor MkTraversal
  extract : a.π1 -> Σ Nat (\n => Vect n b.π1 * (Vect n b.π2 -> a.π2))
```

We can find the correspondance  by performing the following series of steps, starting from the definition of traversal with type `Traversal (a, a') (b, b'):

- $a → Σ (n : Nat) . Vect\ n\ b ⊗ (Vect\ n\ b' → a')$
- $a → Σ (n : Nat) . Σ (\_: Vect\ n\ b) . Vect\ n\ b' → a')$ by isomorphism between ⊗ and Σ
- $a → Σ (ls : Σ (n : Nat). Vect\ n\ b) . Vect\ ls_{π1}\ b' → a'$ by currying
- $a \to Σ (ls : List\ b). Vect\ (length\ ls)\ b' \to a'$ by isomorphism between $Σ(n : Nat). Vect\ n\ a$ and $List\ a$

This last line already has the correct shape to be written as a closed lens with type `Closed (a, a') (ls : List b, Vect (length ls) b')`. Due to the dependency in the second boundary, this must be a morphism in the category of containers.

But we can do even better. By using two more isomorphisms here is what we can do:
- $a \to Σ (ls : List\ b). Vect\ (length\ ls)\ b' \to a'$, what we had before
- $a → Σ (ls : List\ b). All\ (const\ b')\ ls → a'$, by isomorphism $(ls : List\ a) \to Vect\ (length\ ls)\ b \approx All\ (const\ b)\ ls$
- $a \to Ex (ListCont\ \mathbin{▶}\ (b, b'))\ a'$ by definition of the extension and of `▶`

The last expression is actually written in the style of a pointful lens, but as we will see in the next section, it can be written as a monad on $Cont$.


### Traversals are isomorphic to the list monad on container morphisms

From the chapter on [monads on containers]()

```idris
---------------------------------------------------------------------------------
-- Traversal is isomorphic to the List Monad on Container
---------------------------------------------------------------------------------

vectToFn : {0 a : Type} -> {0 m : Nat} -> Vect m a -> Fin m -> a
vectToFn v i = index i v

fnToVect : {0 a : Type} -> {m : Nat} -> (Fin m -> a) -> Vect m a
fnToVect f {m = 0} = []
fnToVect f {m = (S k)} = f FZ :: fnToVect (f . FS)

vecIso : {0 a : Type} -> {n : Nat} -> Vect n a `Iso` (Fin n -> a)
vecIso = MkIso
  vectToFn
  fnToVect
  toFrom
  fromTo
  where
    fromTo : {0 n : Nat} -> (x : Vect n a) -> fnToVect (vectToFn x) === x
    fromTo [] = Refl
    fromTo (x :: xs) = cong (x ::) (fromTo xs)

    0 toFrom : {m : Nat} -> (fn : Fin m -> a) -> vectToFn {m} (fnToVect {m} fn) === fn
    toFrom {m = 0} fn = funExt $ \w => absurd w
    toFrom {m = (S k)} fn = funExt go
      where
        go : (w : Fin (S k)) -> index w (fn FZ :: fnToVect (\y => fn (FS y))) = fn w
        go FZ = Refl
        go (FS x) = app (vectToFn (fnToVect (fn . FS))) (fn . FS) (toFrom (fn . FS)) x

%unbound_implicits on
listIsTraversal : (a :- a') =%> ListCont ▶ (b :- b') -> Traversal (MkB a a') (MkB b b')
listIsTraversal (MkMorphism fwd bwd) = MkTraversal $ \x => (fwd x).ex1 ## (vecIso.from (fwd x).ex2 && \vx => bwd x (vecIso.to vx))

traversalIsList : Traversal (MkB a a') (MkB b b') -> (a :- a') =%> ListCont ▶ (b :- b')
traversalIsList (MkTraversal e) = MkMorphism
  (\x => MkEx (e x).π1 (vecIso.to (e x).π2.π1))
  (\x, f => (e x).π2.π2 (vecIso.from f))

lemma : {0 a : Type} -> (f : a -> TyList b) -> (x : a) -> MkEx (f x).ex1 (vectToFn {a=b, m = (f x).ex1} (fnToVect {a=b, m = (f x).ex1} ((f x).ex2))) === (f x)
lemma f x with (f x)
  lemma f x | (MkEx n m) = cong (MkEx n) (vecIso.toFrom m)

traversalIso : ((a :- a') =%> ListCont ▶ (b :- b')) `Iso` (Traversal (MkB a a') (MkB b b'))
traversalIso = MkIso
  listIsTraversal
  traversalIsList
  pp
  qq
  where
    pp : (zv : Traversal (MkB a a') (MkB b b')) -> listIsTraversal (traversalIsList zv) === zv
    pp (MkTraversal ex) = cong MkTraversal $ funExt $ fg
    where
      fg : (z : a) -> ? === ex z
      fg z with (ex z) proof prf
        fg z | (0 ## ([] && p)) = rewrite sym $ proj1 prf in
              cong2Dep (##) Refl $
              cong2 Product.(&&)
                       { a = fnToVect (vectToFn (((ex z) .π2) .π1))
                       , b = replace {p = \nm => Vect nm b} (sym $ proj1 prf) []
                       , c = (\vx => (ex z).π2.π2 (fnToVect (vectToFn vx)))
                       , d = replace {p = \nm => Vect nm b' -> a'} (sym $ proj1 prf) p}
                       (rewrite prf in Refl)
                       (funExt $ \vx => rewrite vecIso.fromTo vx in rewrite prf in Refl)
        fg z | ((S k) ## (xs && p)) = rewrite sym $ proj1 prf in
              cong2Dep' (##) Refl $
              cong2 Product.(&&)
                  { a = fnToVect (vectToFn (((ex z) .π2) .π1))
                  , b = replace {p = \nm => Vect nm b} (sym $ proj1 prf) xs
                  , c = (\vx => (ex z).π2.π2 (fnToVect (vectToFn vx)))
                  , d = replace {p = \nm => Vect nm b' -> a'} (sym $ proj1 prf) p}
                  (rewrite vecIso.fromTo (((ex z) .π2) .π1) in rewrite prf in Refl)
                  (funExt $ \vx => rewrite vecIso.fromTo vx in rewrite prf in Refl)

    0 qq : (x : (a :- a') =%> (ListCont ▶ (b :- b'))) -> traversalIsList (listIsTraversal x) === x
    qq (MkMorphism f b) = cong2Dep' MkMorphism
        (funExt $ lemma f)
        (funExtDep $ \v => funExt $ \w => cong (b v) (vecIso.toFrom w))
```
