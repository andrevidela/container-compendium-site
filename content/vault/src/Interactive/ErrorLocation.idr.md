## Introducing Functorial Application: Tracking Error Locations
Parsing and error reporting are two processes that ought to be related to each other, but the correspondance is hard to make formal. In this example, I show how to use the `Some` Comonad on containers to collect partial failures of sub-processes and re-interpret them in a larger context.

### The `Some` relation on lists

We've seen how the List container with `▶` results in a type that is isomorphic to `All` and `○` is isomorphic to `Any`, but is there something in between? `All` ensures a predicate is true for all elements of a given list, and `Any` ensures exactly one fits the bill. But is there a way to say only _some_ of the elements satisfy the preducate and others do not? Well, we can write this type first and then find out what it means:

<!-- idris
module Interactive.ErrorLocation

import Data.Product
import Data.Container
import Data.Container.Morphism
import Data.Container.Maybe.Definition
import Data.Container.List.Functor
import Data.Container.Descriptions.List
import Data.Container.Descriptions.Maybe

import Data.Iso
import Data.List.Quantifiers
import Proofs
-->

```idris
data Some : (a -> Type) -> List a -> Type where
  End : {0 a : Type} -> {0 p : a -> Type} ->  Some p []
  Take : {0 a : Type} -> {0 p : a -> Type} -> {0 xs : List a} -> {0 x : a} -> p x -> Some p xs -> Some p (x :: xs)
  Drop : Some p xs -> Some p (x :: xs)
```

This data definition is surprisingly close to the definition of a _thinning_.

```
data (<=) : List a -> List a -> Type where
  None : [] <= xs
  Take : xs <= ys -> x :: xs <= x :: ys
  Drop : xs <= ys -> xs <= x :: ys
```

The difference being that a thinning does not carry values, only a "selection". But this is already helpful, as we can write our `Some` datatype using a thinning and the existing `All` relation:

```
Some' : (p : a -> Type) -> List a -> Type
Some' p ls = Σ (xs : List a) | xs <= ls * All p xs
```

In prose, it says that given a predicate and a list, we can create the subset of all values satisfying the predicate using a thinning.

### The `Some` Functor on Container

Regardless of how we define it, we use `Some` in the same way as `All` and `Any` in their container-as-monad definition. By using a `List` in the message, and a wrapped predicate in the response

```idris
SomeC : Container -> Container
SomeC c = (xs : List c.req) !> Some c.res xs
```

This transforms an 'input/response' pair into "multiple inputs, some of which can fail in their responses"

### The truth behind `Some`

In the above, we've only worked with `Some` defined as a datatype in Idris, but previously,
we established a correspondance between containers using idris datatype definitions and
maps of containers using different monoidal products and actions. If we assume that every
map on container we can define in idris has a construction in terms of existing monoidal
products. What would it be for `Some`?

A good candidate would be `SomeC = AllC (MaybeC a)` since we have seen previously that
`AllC (MaybeAny a)` can also represent partial results. However those two types are not
equal. To see this, we attempt to implement the map `AllC (MaybeAnyIdris a)`. If they are the
same, this morphism should be equivalent to the identity.

```idris
attempt1 : All.List (Any.Maybe a) =%> SomeC a
attempt1 = ?Problem <! ?attempt1_rhs_1
```

However, problems start right away, since the forward map must be of type
`List (Maybe a.req) -> List a.req` and there is no way to do this while keeping around
all the elements of the input list. For this to work, we need an identity on the
shapes. Ideally we want those signatures:

- `fwd : List a.req -> List a.req`
- `bwd : (xs : List a.req) -> All (?thing .  a.res) xs -> Some a.res xs`

Such that `All (?thing .  a.res) xs -> Some a.res xs` is also an identity. If we were to
find what `thing` is, then we could represent `SomeC` in terms of `AllC`. This is the
insight we were missing, because another way to understand `Some` is as a predicate
on all elements of a list, some of which might fail. This possiblity of failure can be
represented with `Maybe`. So if we can prove that `Some p xs` is the same as
`All (Maybe . p) xs` then we will have found a way to write `Some` in terms of `All`.

```idris
rebuild1 : (xs : List a) -> All (\x => Maybe (b x)) xs -> Some b xs
rebuild1 [] [] = End
rebuild1 (x :: xs) (Nothing :: z) = Drop (rebuild1 xs z)
rebuild1 (x :: xs) ((Just y) :: z) = Take y (rebuild1 xs z)

rebuild2 : (xs : List a) -> Some b xs -> All (\x => Maybe (b x)) xs
rebuild2 (x :: ls) (Take y z) = Just y :: rebuild2 ls z
rebuild2 (x :: ls) (Drop y) = Nothing :: rebuild2 ls y
rebuild2 [] End = []

rebuildPrf : {0 p : a -> Type} -> (xs : List a) -> (x : All (\x => Maybe (p x)) xs) ->
             rebuild2 xs (rebuild1 xs x) = x
rebuildPrf [] [] = Refl
rebuildPrf (x :: xs) (Nothing :: ys) = cong2 (::) Refl (rebuildPrf xs ys)
rebuildPrf (x :: xs) ((Just y) :: ys) = cong2 (::) Refl (rebuildPrf xs ys)

rebuildPrf2 : {0 p : a -> Type} -> (xs : List a) -> (x : Some (\arg => p arg) xs) -> rebuild1 xs (rebuild2 xs x) = x
rebuildPrf2 [] End = Refl
rebuildPrf2 (y :: xs) (Take x z) = cong (Take x) (rebuildPrf2 xs z)
rebuildPrf2 (y :: xs) (Drop x) = cong Drop (rebuildPrf2 xs x)

SomeAllIso : {xs : _} -> Some p xs ≅ Quantifiers.All.All (Maybe . p) xs
SomeAllIso = MkIso
    (rebuild2 xs)
    (rebuild1 xs)
    (rebuildPrf xs)
    (rebuildPrf2 xs)
```

From this we can also build the isomorphism with the container map `SomeC`.

```idris
allToSome : All.List ((x : a) !> Maybe (b x)) =%> SomeC ((!>) a b)
allToSome = id <! rebuild2

someToAll : SomeC ((!>) a b) =%> All.List ((x : a) !> Maybe (b x))
someToAll = id <! rebuild1
```

### Error location tracking using `Some`

This application of lenses will reconstruct contextual information from parsing data line-by-line without placing extra information in the parsed data, but by keeping it as part of the parsing/printing relationship between the input and the output of a parser.

The parse we are going to write has two stages: First we split appart the input in areas of interest. For this example, each line will be it own area of interest. For each of those areas, we are going to run the parser, with the additional constraint that the parser is written in a manner that is agnostic to location tracking. After running the parser, we collect the potential errors that the parser produced at each area of interest, those errors are then matched with the area of interest and printed.

```
input example:

-- 0| ok
-- 1| No
-- 2| ok
-- 3| ok
-- 4| Ok
-- 5| yes
-- 6| oui
-- 7| ok
-- 8| wat

output example

line 1: error, only positive answers allowed, cannot answer "no"
line 4: error, capitalised "ok".
line 8: error, unexpected response "wat"
```

We are going to use `SomeC` on a container `String :- ParseError` resulting in a container `(xs : List String) !> Some (const ParseError) xs`. This way, the parser is always written as a function that might return a parse error.

### What is actually going on

`SomeC` is a combination of the `List` monad on containers applied to the `Lift Maybe` comonad on containers. Hear me out:

The `List` monad applied to a container `(x : q) !> r x` results in a container `(xs : List q) !> All r xs`. The `SomeC` functor does almost the same but filters out some responses, we can achieve this by wrapping the response in a `Maybe` where the `Nothing` value represents a skipped result and the `Just` represents a valid response. The `SomeC` functor can then be written as `(xs : List q) !> All (Maybe . r) xs`.

While this hardcoding works, we can do better, we notice that if we look at this expression as a container applied to the list monad, the container given is `(x : q) !> Maybe (r x)`. This container is related to the original `(x : q) !> r x` via the _lifting_ of responses using the `Maybe` monad on types. We write such lifting `Maybe • _` and therefore, the container given in argument to the list monad is `Maybe • ((x : q) !> r x)`.

From this we conclude that we write the `SomeC` functor on containers as

```
SomeC : Container -> Container
SomeC c = ListAll (Maybe • c)
```

It is worth noting that both `ListAll _ ` and `Maybe • _` are functors, and so their composition remains a functor. But because `ListAll _` is a monad and `Maybe • _` is a comonad, their composition fails to be either.
