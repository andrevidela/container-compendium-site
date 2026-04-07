<!-- idris
module Data.Container.Descriptions.Some

import Data.Container
import Data.Container.Category
import Data.Container.Descriptions.List
import Data.Container.Morphism
import Data.Container.Morphism.Eq

import Data.Category.Functor

import Data.Fin
import Data.Iso
import Data.Some
import Data.Product
import Data.Coproduct
import Data.List.Quantifiers
import Data.String

import Syntax.PreorderReasoning

import Proofs.Congruence
import Proofs.Extensionality

import System.File

%hide Prelude.(&&)
-->

## Some results

We've seen a number of interactive systems making use of lists
for their query and response mechanisms. That approach is quite
useful because it allows us to collate multiple results and makes
use of the well-known list-monad.

Some interactive system use lists for their queries, but only
a subset of those elements will have an appropriate response.
We are going to see an example of this right here.

Unlike `All`, we do not want to reply to every single element
of the query, and unlike `Any` we don't want to answer to just
one query, but 0 or more. We want a datatype with signature
`(p : a -> Type) -> (xs : List a) -> Type` just like `Any` or `All`,
but which values capture the subset of `xs` which satisfy the
predicate. We can write this as a data type:

```
public export
data Some : (a -> Type) -> List a -> Type where
  Take : {0 p : a -> Type} -> p x -> Some p ls -> Some p (x :: ls)
  Drop : {0 x : a} -> {0 p : a -> Type} -> Some p ls -> Some p (x :: ls)
  Empty : Some p []
```

Some keen-eyed viewers might recognise the structure of a
thinning. Indeed we can also write the `Some` datatype using a
thinning: `Some p xs = Σ (ys : List) | ys <= xs * All p ys` where
`<=` is the type constructor for thinnings.

Using `Some` we can define a map of containers that will take
a container an map it to its `Some` counterpart. This is using
the same structure as with the `All` or `Exists` monads on
containers.

```idris
SomeC : Container -> Container
SomeC c = (!>) (List c.message) (Some c.response)
```

This is marketly different than `AllC (MaybeC a)` because we are
not wrapping our result in a `Maybe` in the shapes, only the
positions exhibit partial results. Time to look at an example

### Returning partial results

There are many ways to parse a file, but a nice way to do it
is line-by-line such that for each line you parse, you carry
around the line number so that you can report the correct
line if something goes wrong. Let's say you are parsing
a list of numbers and each line in a file is a number, you
want to produce errors that look like this:

```
Error at line 12, could not parse `12e`
```

For a typical parser, this means that you have to run in
a state monad, and carry around the "current state". But
really error reporting, and parsing are two different activities
and therefore they should be separate. Entangling them together
is simply going to make software engineering more difficult.

To this end, let's design a parser as a lens, where the forward
part splits the file in lines and the backward part rebuilds
errors for each line that failed.

```idris
splitFile : String -> List String
splitFile = lines

rebuild : (input : String) -> Some (const Nat) (lines input) -> String
rebuild input x = unlines (map (renderError (lines input)) (absents x))
  where
```

This lens splits a string into multiple lines, on the backward part it rebuilds
a string from the list of errors that occurred. An error happens when the
value returned is `Nothing`.

The `rebuild` function itself has an interesting type, it says that, for all lines in `lines input`
we have either a value of type `Nat` or a unit value, representing the error.
The dependency with the input ensures that we only ever get errors _for a given line_, errors without a line number, or with an out of bounds line number, are impossible.

This is rendered obvious with the function that translates a value of "some" into a list of indices `absents : Some p xs -> List (Fin (length xs))`. This function will collect all the indices in the list `xs` that do not have an associated value.

```idris
  absents : Some p xs -> List (Fin (List.length xs))
  absents Empty = []
  absents (Take x xs) = map FS (absents xs)
  absents (Drop xs) = FZ :: map FS (absents xs)
```

In turn, we can use it to return the text at this index as part of the error message:

```idris
  renderError : (ls : List String) -> Fin (length ls) -> String
  renderError ls idx = "Error at line \{show $ finToNat idx}: \{index' ls idx}"
```

Those functions explain the implementation of `rebuild` above. Combining everything above we can build the error tracking lens that tracks errors for each line and produce an appropriate error message when the parsing fails:

```idris
lineError : (String :- String) =%> ((ls : List String) !> Some (const Nat) ls)
lineError = splitFile <! rebuild
```

Combining everything together, we can write a program that will attempt to parse
a list of numbers into a list of `Nat`, using our lens. What is remarkable about this
program is that the activity of error tracking and parsing are completely decoupled. The parser does not know about error tracking and the error tracking lens does not know about parsing.

```idris

runParser : Costate (String :- Maybe Nat)
runParser = costate parsePositive

main : IO ()
main = do
  fileContent <- readFile "file"
  run (renderError)
```

```idris
fromSomeBack : {0 a : Container} -> (xs : List a.shp) ->
               All (\x => () + a.pos x.π2) (listMap (\arg => () && arg) xs) ->
               Some a.pos xs
fromSomeBack [] [] = Empty
fromSomeBack (x :: xs) (+> y :: ys) = Take y (fromSomeBack xs ys)
fromSomeBack (x :: xs) (<+ y :: ys) = Drop (fromSomeBack xs ys)

fromSome : SomeC a =%> ListAllIdris (CUnit * a)
fromSome = MkMorphism (listMap (() &&)) fromSomeBack

toSomeBack : {0 a : Container} -> (xs : List (() * a .shp)) -> Some (a .pos) (listMap π2 xs) -> All (\x => () + a .pos (x .π2)) xs
toSomeBack [] Empty = []
toSomeBack (x :: xs) (Take y z) = +> y :: toSomeBack xs z
toSomeBack (x :: xs) (Drop y) = <+ () :: toSomeBack xs y

toSome : ListAllIdris (CUnit * a) =%> SomeC a
toSome = MkMorphism (listMap π2) toSomeBack

mapProductComposeInverse : (v : List a) -> listMap π2 (listMap (() &&) v) = v
mapProductComposeInverse v = Calc $
    |~ listMap π2 (listMap (() &&) v)
    ~~ listMap (π2 . (() &&)) v ..<(allCompFwd π2 (() &&) v)
    ~~ listMap id v             ...(cong (\x => listMap x v) Refl)
    ~~ v                        ...(listMapId v)

takeInj1 : Take x y = Take x' y' -> x = x'
takeInj1 Refl = Refl

-- %unbound_implicits off
-- fromToSomeBackward :
--     {0 a : Container} ->
--     (x1 : List (a .shp)) ->
--     (x2 : Some (a .pos) (listMap π2 (listMap (\arg => () && arg) x1))) ->
--     fromSomeBack {a} x1 (toSomeBack {a} (listMap (\arg => () && arg) x1) x2) === replace {p = Some a.pos} (mapProductComposeInverse x1) x2
-- fromToSomeBackward [] Empty = Refl
-- fromToSomeBackward (x :: xs) (Take y z) = cong (rewrite sym $ mapProductComposeInverse (x :: xs) in Take y) ?bdb
-- fromToSomeBackward (x :: xs) (Drop y) = ?fromToSomeBackward_rhs_3
-- fromToSomeBackward (x :: xs) Empty = ?fromToSomeBackward_rhs_4
--
-- 0 fromToSome : {a : Container} -> (fromSome {a} |> toSome {a}) `DepLensEq` identity
-- fromToSome = MkDepLensEq mapProductComposeInverse ?ahudihu -- fromToSomeBackward
--
-- toFromSome : {a : Container} -> toSome {a} |> fromSome {a} `DepLensEq` identity
-- toFromSome = MkDepLensEq ?fromToSome_rhs_02 ?fromToSome_rhs_123
```

## Some p is All (Maybe p)

Because the `Some` datatype holds a predicate for each element of the list in index, we can write it in terms of the existing `All` type on lists:
`All : (a -> Type) -> List a -> Type` by composing the predicate with `Maybe`.
This ensures that for all elements of the list, either the predicate holds, or the value is missing.
We verify the isomorphism quite easily:

```idris
AllM : {x : Type} -> (x -> Type) -> List x -> Type
AllM f = All (Maybe . f)

someToAll : {0 a : Type} -> {0 p : a -> Type} -> {ls : List a} -> Some p ls -> AllM p ls
someToAll {ls = []} Empty = []
someToAll {ls = (y :: xs)} (Take x z) = Just x :: someToAll z
someToAll {ls = (y :: xs)} (Drop x) = Nothing :: someToAll x

allToSome : {0 a : Type} -> {0 p : a -> Type} -> {ls : List a} -> AllM p ls -> Some p ls
allToSome {ls = []} x = Empty
allToSome {ls = (y :: xs)} (Nothing :: z) = Drop (allToSome z)
allToSome {ls = (y :: xs)} ((Just x) :: z) = Take x (allToSome z)

someAllSome : {ls : List a} -> (x : Some p ls) -> allToSome (someToAll x) === x
someAllSome {ls = []} Empty = Refl
someAllSome {ls = (y :: xs)} (Take x z) = cong (Take x) (someAllSome z)
someAllSome {ls = (y :: xs)} (Drop x) = cong Drop (someAllSome x)

allSomeAll : {ls : List a} -> (x : AllM p ls) -> someToAll (allToSome x) === x
allSomeAll {ls = []} [] = Refl
allSomeAll {ls = (y :: xs)} (Nothing :: z) = cong (Nothing ::) (allSomeAll z)
allSomeAll {ls = (y :: xs)} ((Just x) :: z) = cong (Just x ::) (allSomeAll z)

0
AllMSomeIso : Iso (AllM p ls) (Some p ls)
AllMSomeIso = MkIso allToSome someToAll someAllSome allSomeAll
```

We can now use this definition to write our `Some` Container, and verify that it is isomorphic with the previous definitons of `Some` on containers.

```idris
AllMaybe : Container -> Container
AllMaybe c = (x : List c.shp) !> AllM c.pos x

SomeToAllMaybe : SomeC c =%> AllMaybe c
SomeToAllMaybe = MkMorphism id (\ls => allToSome)

AllMaybeToSome : AllMaybe c =%> SomeC c
AllMaybeToSome = MkMorphism id (\ls => someToAll)

SomeAllSome : {0 c : Container} -> SomeToAllMaybe {c} |> AllMaybeToSome {c}
              `DepLensEq` identity {a = SomeC c}
SomeAllSome = MkDepLensEq (\_ => Refl) (\x, y => someAllSome y)

AllSomeAll : {0 c : Container} -> AllMaybeToSome {c} |> SomeToAllMaybe {c}
             `DepLensEq` identity {a = AllMaybe c}
AllSomeAll = MkDepLensEq (\_ => Refl) (\x => allSomeAll)

AllMaybeSomeIso : {0 c : Container} -> ContIso (AllMaybe c) (SomeC c)
AllMaybeSomeIso = MkGenIso
    AllMaybeToSome
    SomeToAllMaybe
    AllSomeAll
    SomeAllSome
```

However, it's not clear what the properties of that map on container is. If we were able to write it as an operation on containers we could better understand what makes `Some` different from `All` and `Any`.

## SomeC is All (Lift Maybe)

It turns out `SomeC` can be written as an operation on containers, rather than an operation on types. This mapping allows us to understand why `SomeC` is not a monad, and how it's related to existing definition. For this we make use of `Lift`,
recall that lift takes a functor and a container and applies the functor to the "responses" of the container: `Lift f (a !>  b) = (a !> f . b)`. If we give `Maybe` as the functor we obtain a map that applies `Maybe` to the response `(x : a !> Maybe (b x))`. If we apply `ListAll` to this container we wrap the queries in a list and the response in a `All` predicate, resulting in `(x : List a !> All (Maybe . b) x)` and now you can see how the second argument is actually the same as the definition of `Some` using `All`. In fact they are definitionally equal:

```idris
AllMaybeLift : Container -> Container
AllMaybeLift c = ListAllIdris (Lift Maybe c)

LiftSame : AllMaybeLift c === AllMaybe c
LiftSame = Refl
```

Writing it this way makes a couple thinkgs more clear. Because `Some` can be built
from existing structures, it inherits the properties of the underlying structures.
In particular, it is not a _monad_ but a _comonad_ due to the fact that `Maybe` is
a monad. Because both `ListAll` and `Lift Maybe` are functors, their composition
remains a functor. We can verify those facts by providing the appropriate instances:

```idris
SomeIsFunctor : Functor Cont Cont
SomeIsFunctor = ?SomeIsFunctor_rhs
```

```idris
SomeIsComonad : Monad Cont.op Cont.op
```

### Conclusion

Even with complex and bespoke requirement like error tracking we can build a lens using the existing combinators. Because their properties carry around properly, we can keep building larger and larger programs without fear of losing composability and we can always keep track of what notion of monad we are able to use to keep composing programs.
