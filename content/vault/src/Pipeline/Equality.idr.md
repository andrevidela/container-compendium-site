<!-- idris
module Pipeline.Equality

import Control.Category
import public Data.List.Quantifiers
import Data.Nat

%default total

public export
-->

### Congruence Pipelines

We've seen how to use `PreorderReasoning` to build proofs in Idris but
sometimes the proofs we build rely heavily on congruence, and
even nested congruence. For those cases, the proofs using`PreorderReasoning`
are obscured by the careful threading
of congruence application and seeing what is actually being proven becomes a
a challenge. This is especially the case when proving facts about large commuting
diagrams where each step results in a smaller commuting diagram over which
we need to apply a congruence.

- [ ] Show example if commuting diagram and congruence

To address this poor experience, we are going to use _Congruence Pipelines_
a small library inspired by the _Pipelines_ library which  is specialised for
proofs that make heavy use of congruence.

- [ ] Add link to pipeline library

A Congruence pipeline is split into two parts, first the proof _plan_
describes what steps are going to be taken and how to break appart
the proof into smaller constituent parts. Once the proof plan has been
devised, a proof _term_ is used to instanciate the proof plan and compute
the requested equality.

First we define the type of proof plans.

```idris
data CongPipeline : (size : Nat) -> (obj : Type) -> Type where
  Nil : CongPipeline Z o
  (::) : o -> CongPipeline n o -> CongPipeline (S n) o
  AddNest : {0 innerObj, outerObj : Type} ->
            {0 m, n : Nat} ->
            (fd : innerObj -> outerObj) ->
            (ts : CongPipeline (S n) innerObj) ->
            CongPipeline m outerObj ->
            {0 sum : Nat} ->
            (check : S n + m = sum) =>
            CongPipeline sum outerObj
```

The congruence pipeline is defined with three constructor, one for the empty
pipeline, one for adding an element to the pipeline, and one to add a _nested_
element to the pipeline, it is this nesting that allows to build a proof
through nested congruence.

```idris {hidden=""}
public export
```

To evaluate congruence pipeline into equalities, we need to extract their first
and last element. The challenge here is to correctly handle the nested case
where an arbitrary amount of congruence nesting can happen.

```idris
head : {0 n : Nat} -> (ts : CongPipeline (S n) o) -> o
head (x :: y) = x
head (AddNest f ts _) = f (head ts)
```

Obtaining the last element of a pipeline require careful use of `assert_total` which is explained in section \ref{totality-checking}.

```idris {hidden=""}
public export
```
```idris
last : {0 n : Nat} -> (ts : CongPipeline (S n) o) -> o
last (x :: []) = x
last (x :: n@(y :: z)) = last n
last (x :: (AddNest fd ts y)) = assert_total $ Equality.last (AddNest fd ts y)
last (AddNest f ts []) = f (last ts)
last (AddNest fd ts n@(x :: y)) = last n
last (AddNest fd ts (AddNest x y z)) = assert_total $ last (AddNest x y z)
```

This is necessary to implement the `ToList` function which takes a congruence pipeline
and return the list of types that make up the proof plan. This function has two jobs,
to flatten the congruence pipeline into a singular list rather than a nested structure,
and to appropriately insert "conversion proofs" in between steps that make use of congruence.

For example in the following proof plan:
```
a = F b = F c = G d = G e = f
```

Can be illustrated with the congruence pipeline:

```
a
={Cong F}
    b
    =
    c
={Cong G}
    d
    =
    e
=
f
```

Flattening the congruence pipeline naively would result in the proof sequence
`a = b = c = d = e = f` which is incorrect because we should see `a = F b` instead of `a = b` in the first step. A corrected sequence of
proof steps is:

```
  a = F b
  b = c   -- Here we don't have to apply congruence
F c = G d -- Here we need to convert between the two nested congruences
  d = e   -- No congruence here either
F e = f
```

Notice how intermediate steps are added to convert between outer elements, and nested elements.

```idris {hidden=""}
public export
```

```idris
ToList : {0 n : Nat} -> {0 ty : Type} -> CongPipeline n ty -> List Type

public export
combineRest : {0 ty : Type} -> (end : ty) -> (x : CongPipeline m ty) -> List Type
combineRest end [] = []
combineRest end (Equality.(::) x y) = (end === x) :: ToList (x :: y)
combineRest end (AddNest f y z) =
    (end === head (AddNest f y z)) :: ToList (AddNest f y z)

ToList [] = []
ToList (Equality.(::) x []) = []
ToList (Equality.(::) x (Equality.(::) y z)) = (x === y) :: ToList (y :: z)
ToList (Equality.(::) x (AddNest fd ts y))
    = (x === fd (head ts)) :: ToList ts ++ combineRest (fd (last ts)) y
ToList (AddNest fd ts x) = ToList ts ++ combineRest (fd (last ts)) x
```

This conversion into a flat list is how we build the `Prove` type which is an alias for a heterogenous list of types
each of which is one of the equality computed by `ToList`.
```idris {hidden=""}
public export
```

```idris
Prove : CongPipeline n ty -> Type
Prove x = HList (ToList x)
```

Once we have a proof plan in the form of a `CongPipeline` and a proof term in the form of `Prove` then we can
run the proof and obtain our resulting equality. Note how this function carefully threads the proof around
with uses of `cong` and `trans`. Notice how we also have to rely on `assert_total` since the compiler has no proof
that the result of calling `splitAt` results in a structurally smaller sub-term.

```idris {hidden=""}
export
```
```idris
runProof : (spec : CongPipeline (S n) ty) -> (steps : Prove spec) -> head spec === last spec
runProof (Equality.(::) x []) steps = Refl
runProof (Equality.(::) x (Equality.(::) y z)) (w :: v) = trans w (runProof (y :: z) v)
runProof (Equality.(::) x (AddNest fd ts y)) (s1 :: s2)
  = trans s1 $ runProof (AddNest fd ts y) s2
runProof (AddNest fd ts []) steps with (splitAt ? steps)
  runProof (AddNest fd ts []) steps | (p, _) =
    cong fd (assert_total $ runProof ts p)
runProof (AddNest fd ts (Equality.(::) x y)) steps with (splitAt ? steps)
  runProof (AddNest fd ts (Equality.(::) x y)) steps | (p1, p2 :: p3) =
    let q1 = assert_total $ runProof ts p1
        q2 = assert_total $ runProof (x :: y) p3
    in trans (cong fd q1) (trans p2 q2)
runProof (AddNest fd ts (AddNest f x y)) steps with (splitAt ? steps)
  runProof (AddNest fd ts (AddNest f x y)) steps | (p1, p2 :: p3) =
    let q1 = assert_total $ cong fd (runProof ts p1)
        q2 = assert_total $ runProof (AddNest f x y) p3
    in trans q1 (trans p2 q2)
```

```idris{hidden=""}
public export
record NestCong (outerObj : Type) where
  constructor Cong
  {0 inner : Type}
  fd : inner -> outerObj
  {0 plen : Nat}
  ps : CongPipeline (S plen) inner

export infixr 0 |<
export infixr 0 >|
export infixr 0 |=

public export
(|=) : o -> CongPipeline n o -> CongPipeline (S n) o
(|=) = (::)
public export
(>|) : (np : NestCong outerObj) ->
       CongPipeline m outerObj ->
       CongPipeline (S np.plen + m) outerObj
(>|) np x = AddNest {m} np.fd np.ps x
```

Note that the congruence pipeline library can be used in the same
way as `PreorderReasoning` and provide a linear sequence of terms
for which we need to apply congruence piecemeal manually. Here is
an example.

```idris
-- proof plan without nesting
flatPlan : (a, b, c, d : Nat) -> CongPipeline ? Nat
flatPlan a b c d =
  [ a + (b + (c + d))
  , a + (b + (d + c))
  , a + ((d + c) + b)
  , ((d + c) + b) + a
  , (d + (c + b)) + a
  , d + ((c + b) + a)
  , d + (c + (b + a))
  ]

flatSteps : {a, b, c, d : Nat} -> Prove (Equality.flatPlan a b c d)
flatSteps =
  [ cong (a +) (cong (b+) (plusCommutative c d))
  , cong (a +) (plusCommutative ? ?)
  , plusCommutative a ((d + c) + b)
  , cong (+ a) (sym $ plusAssociative d c b)
  , (sym $ plusAssociative d (c + b) a)
  , cong (d + ) (sym $ plusAssociative c b a)
  ]

flatProof : {a, b, c, d : Nat} -> a + (b + (c + d)) = d + (c + (b + a))
flatProof = runProof (flatPlan a b c d) flatSteps
```

The same example can be implemented using nested congruence, and
here we can see the tradeoff of the library: decyphering what
the terms are is a bit more difficult because the congruence obfuscate
them. But seeing the proof steps is much easier because they are all
neatly paired up. What is more the implementation of the proof is
much more readable since it is free from calls to congruence.
Finally, the interactive mode is much easier to leverage because
the types shown are free from noise.

```idris
test2 : (a, b, c, d : Nat) -> CongPipeline ? Nat
test2 a b c d =
  Cong (a +)
      (Cong (b +)
          [ c + d       -- commute c and d
          , d + c]      -- commute b and (d + c)
      >| [(d + c) + b]) -- comute a and (d + c) + b
  >| Cong (+ a)
      [ (d + c) + b     -- assoc d c b
      , d + (c + b)]    -- assoc a d (c b)
  >| Cong (d +)
      [ (c + b) + a     -- assoc c b a
      , c + (b + a)]
  >| Nil

test2Impl : {a, b, c, d : Nat} -> Prove (Equality.test2 a b c d)
test2Impl =
  [ plusCommutative {}
  , plusCommutative {}
  , plusCommutative {}
  , sym (plusAssociative {})
  , sym (plusAssociative {})
  , sym (plusAssociative {})
  ]

testRun2 : {a, b, c, d : Nat} -> a + (b + (c + d)) = d + (c + (b + a))
testRun2 = runProof (test2 a b c d) test2Impl
```

- [ ] Ideally we want this syntax for the proof plan: 🔽
  ```
  └ a + (b + (c + d))
      │ Cong (a +)
      └ b + (c + d)
          │ Cong (b +)
          └ c + d
          ┌ d + c
      ┌ b + (d + c)
      ├ (d + c) + b
  ┌ a + ((d + c) + b)
  └ ((d + c) + b) + a
      │ Cong (+ a)
      └ (d + c) + b
      ┌ d + (c + b)
  ∎ (d + (c + b)) + a
  ```
