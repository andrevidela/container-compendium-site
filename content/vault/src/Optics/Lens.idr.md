## Plain lenses for programmers

A plain lens is a data structure used in programming to update and query information about
other data structures. A typical example is a JSON object that holds data about
users and their information.

```json
{
    "firstname" : "john",
    "lastname" : "appleseed",
    "address" : {
        "street" : "street place 12",
        "street2" : "",
        "postcode" : "123-345",
        "countrycode" : "UK",
    },
    "registerinfo" : {
        "joined" : {
            "year" : "2019",
            "month" : "06",
            "day" : "02"
        },
        "accounttype" : "google",
    },
    "birthday" : {
        "year" : "2000",
        "month" : "01",
        "day" : "12"
    }
}
```

Given this structure we might want to ask
- "how to obtain the first name"
- "how to obtain the postcode"
- "how to update the last name"
- "how to update the day of the registration date"

Those questions are quite simple, and in a programming language such as javascript, quite
easy to perform, assuming our json data is in a variable called `user`, we can perform
each operation by chaining field accessors and field assignment:

- `user.fistname`
- `user.address.postcode`
- `user.lastname = newLastname`
- `user.registerinfo.joined.day = newRegistrationDay`

Doing this in Javascript is no big deal, but functional programmers and mathematicians work
in a different context, one where mutation is forbidden. We can
easily extract the fields out of the objects, and we will use the same syntax for that, but we cannot
update them in-place.

Because mutation is not allowed, the only way to "update" some data is to copy all the fields, except
the one we want to change, and insert our new field instead. For example, here is a function
that "updates" the `firstname` field of a `User`:

```
updateFirstName : User -> String -> User
updateFirstName (MkUser oldFirstName lastname address regInfo birthInfo) newFirstName =
    MkUser newFirstName lastname address refINfo birthInfo
```

It constructs a new `User` with `MkUser` and copies all the fields except for `oldFirstName`
since we use `newFirstName` instead.

This is already quite tedious, but becomes infinitely more-so when you want to update nested
fields. For example, updating the day of the registration info would look like this:

```
updateRegDay : User -> Day -> User
updateRegDay (MkUser fs ls addr (MkRegInfo (MkDate year month oldDay) acct) birthday) newDay=
    MkUser fs ls addr (MkRegInfo (MkData year month newDay) acct) birthday
```

And having to write an "update" function for all possible fields of an object is just unsustainable.

Instead, it was discovered that we can build bigger update functions by combining existing ones,
to show this, imagine we have update functions for a `Date` object and update functions for our
`User`:

```
updateDay : Date -> Day -> Date
updateMonth : Date -> Month -> Date
updateYear : Date -> Year -> Date

updateFirstName : User -> String -> User
updateLastName : User -> String -> User
updateAddress : User -> Address -> User
updateRegInfo : User -> RegInfo -> User
updateBirthDay: User -> Date -> User
```

I left out the implementation because it takes a lot of room and it's doing the same as described
above: copy out unchanged fields and replacing the new one by the value given.

With those functions, we can build an update function that will change the birth year only using
what we have defined above:

```
updateUserBirthYear : User -> Year -> User
updateUserBirthYear user year = updateBirthday user (updateYear user.birthday year)
```

It turns out we can do this for any nested fields, as long as we have the appropriate update
functions.

You will notice that I had to use `user.birthday` but this is no problem in functional programming,
only mutation is problematic.

Of course, we did not stop there, by abstracting one more layer, we can generalise this concept
of "drilling down" in order to update a nested field by combining existing update functions.
Update functions, and their field accessor all have the same shape! For an object `o` and a field
`f`, the field accessor has type `o -> f` and for the same object, an update function has type
`o -> f -> o`.

If we are given two objects `o` and `p` and `o` has a field `p` and `p` has a field `q`, then we
can update the nested `q` inside of `o` by combining the update functions:

```
-- called as x.getP
getP : o -> p
updateP : o -> p -> o

getQ : p -> q
updateQ : p -> q -> p

getQInO : o -> q
getQInO oVal = getQ (getP oVal)

updateQInP : o -> q -> o
updateQInP oVal newQ = updateP oVal (updateQ oVal.getP newQ)
```

If you squint a bit, you should see that it's the same implementation as `updateUserBirthYear`
but with more general functions. And this is the final step to understand lenses, those general
functions are what we call a lens. GIven an object `o` and a field `p`, a lens is a pair of function

```
get : o -> p
set : o -> p -> O
```

and we can combine those lenses to build bigger lenses. Once we have a lens, we can use
either its `get` part to extract a field out of an object, or `set` to update the content of an
object.

## An implementation of lenses

<!-- idris
module Optics.Lens

import Data.Category.Ops
import Data.Boundary
import Data.Product
import Data.Coproduct
import Data.Vect
import Data.Sigma

%hide Prelude.Monoid
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
public export
-->

After this exposition, we are ready to implement lenses for real, both as a mathematical object, and as a library for in-place updates of functional programs.

In category theory, a lens is a morphism between pairs of types, which here are called boundaries. Each lens is parameterised by
two `Boundary`.

```idris
record Lens (a, b : Boundary) where
  constructor MkLens
  get : a.π1 -> b.π1
  set : a.π1 -> b.π2 -> a.π2
```

The left boundary represents the "original" data structure, in our json example above, it would be a pair `JSON, JSON`. The right boundary represents the "focus" of the lens, in the above example, it would be one of the fields, if we take the "birthday" lens more specifically, the boundary would be a pair `(Year, Year)`

Lenses also have a graphical representation, if we draw the `get` function as an
arrow and the `set` as another one, going the opposite way, we get this drawing:

```tikz
\begin{document}
\begin{tikzpicture}

\draw (0.5,0) rectangle (3.5,2);
    \draw[->] (0, 1.5) node [left] {X} -- (0.5,1.5) ;
    \draw[<-] (0, 0.5) node [left] {X'} -- (0.5,0.5) ;
    \draw[->] (3.5, 1.5) -- (4.0,1.5) node [right] {Y} ;
    \draw[<-] (3.5, 0.5) -- (4.0,0.5) node [right] {Y'} ;

    \draw (2.5,1.3 ) rectangle (3.2,1.7) node [anchor=north east, yshift=2] {get} ;
    \draw [->] (0.5,1.5) -- (2.5,1.5) ;
    \draw (3.2,1.5) -- (3.5,1.5) ;

    \draw [->](2,1.5) node[circle,fill,inner sep=1pt] {} -- (2,0.7)  ;

    \draw (1.6,0.3) rectangle (2.3,0.7) node [anchor=north east, yshift=2] {set} ;
    \draw (0.5,0.5) -- (1.6,0.5) ;
    \draw [<-] (2.3,0.5) -- (3.5,0.5) ;

\end{tikzpicture}
\end{document}
```

Where the boundaries `a` and `b` are defined to be $(X, X')$ and $(Y, Y')$, writing down the type of the `get` and `set` functions explicitly gives us:
- $get : X \to Y$
- $set : X \to Y' \to X'$

Which we can deduce by following the flow of arrows.

If we remove the internal details we have the much cleaner picture :

```tikz
\begin{document}
\begin{tikzpicture}

\draw (5.0,0) rectangle (8.0,2);
\draw[->] (8, 1.5) -- (8.5,1.5) node [right] {Y};
\draw[<-] (8, 0.5) -- (8.5,0.5) node [right] {Y'};
\draw[->] (4.5, 1.5) node [left] {X}  -- (5.0,1.5) ;
\draw[<-] (4.5, 0.5) node [left] {X'}  -- (5.0,0.5) ;
\end{tikzpicture}
\end{document}
```

Since we are here, we can also remove the details of the boundaries, and draw them simply as boxes between boundaries $A = (X, X')$ and $B = (Y, Y')$.
This time, since we are not concerned about the input and output of the internal functions, we are simply not going to draw pointy arrows anymore:

```tikz
\begin{document}
\begin{tikzpicture}

\draw (-1,0) rectangle (1,1);
\draw (1, 0.5) -- (1.5,0.5) node [right] {B};
\draw (-1.5, 0.5) node [left] {A} -- (-1,0.5) ;
\end{tikzpicture}
\end{document}
```

With this representation, it now seems like we should be able to chain multiple lenses together if they have the right matching boundaries:

```tikz
\begin{document}
\begin{tikzpicture}

\draw (-1,0) rectangle (1,1);
\draw (1, 0.5) -- (1.5,0.5) node [right] {B};
\draw (-1.5, 0.5) node [left] {A} -- (-1,0.5) ;
\draw (2.5,0) rectangle (4.5,1);
\draw (4.5, 0.5) -- (5,0.5) node [right] {C};
\draw (2, 0.5)  -- (2.5,0.5) ;
\end{tikzpicture}
\end{document}
```

#### Sequential composition

This is what the composition operation on lenses does, it takes two lenses with a matching intermediate boundary, and sticks them together
to make a new lens:

```idris
||| Lens composition
export
(|>) : Lens a b -> Lens b c -> Lens a c
(|>) l1 l2 = MkLens (l2.get . l1.get)
  (\x => l1.set x . l2.set (l1.get x))
```

We can again understand the implementation graphically by matching up the internal arrows appropriately, and drawing the composite as a larger box around
the smaller two:

```tikz
\providecommand{\complexdrawing}[6]{%
    \begin{scope}[shift={(#1,#2)}]
    \draw (0.5,0) rectangle (3.5,2);
    \draw[->] (0, 1.5) node [left] {#3} -- (0.5,1.5) ;
    \draw[<-] (0, 0.5) node [left] {#4} -- (0.5,0.5) ;
    \draw[->] (3.5, 1.5) -- (4.0,1.5) node [right] {#5} ;
    \draw[<-] (3.5, 0.5) -- (4.0,0.5) node [right] {#6} ;

    \draw (2.5,1.3 ) rectangle (3.2,1.7) node [anchor=north east, yshift=2] {get} ;
    \draw [->] (0.5,1.5) -- (2.5,1.5) ;
    \draw (3.2,1.5) -- (3.5,1.5) ;

    \draw [->](2,1.5) node[circle,fill,inner sep=1pt] {} -- (2,0.7)  ;

    \draw (1.6,0.3) rectangle (2.3,0.7) node [anchor=north east, yshift=2] {set} ;
    \draw (0.5,0.5) -- (1.6,0.5) ;
    \draw [<-] (2.3,0.5) -- (3.5,0.5) ;
    \end{scope}%
}
\begin{document}
\begin{tikzpicture}
\complexdrawing{1}{1}{X}{X'}{Y}{Y'}
\complexdrawing{5.5}{1}{}{}{Z}{Z'}
\draw (1.25, 0) rectangle (9.25, 4) ;
\end{tikzpicture}
\end{document}
```

If we remove the internal boxes, we can now follow the implementation by following the arrows:

```tikz
\providecommand{\complexdrawing}[6]{%
    \begin{scope}[shift={(#1,#2)}]
    \draw (0.5,0) rectangle (3.5,2);
    \draw[->] (0, 1.5) node [left] {#3} -- (0.5,1.5) ;
    \draw[<-] (0, 0.5) node [left] {#4} -- (0.5,0.5) ;
    \draw[->] (3.5, 1.5) -- (4.0,1.5) node [right] {#5} ;
    \draw[<-] (3.5, 0.5) -- (4.0,0.5) node [right] {#6} ;

    \draw (2.5,1.3 ) rectangle (3.2,1.7) node [anchor=north east, yshift=2] {get} ;
    \draw [->] (0.5,1.5) -- (2.5,1.5) ;
    \draw (3.2,1.5) -- (3.5,1.5) ;

    \draw [->](2,1.5) node[circle,fill,inner sep=1pt] {} -- (2,0.7)  ;

    \draw (1.6,0.3) rectangle (2.3,0.7) node [anchor=north east, yshift=2] {set} ;
    \draw (0.5,0.5) -- (1.6,0.5) ;
    \draw [<-] (2.3,0.5) -- (3.5,0.5) ;
    \end{scope}%
}
\begin{document}
\begin{tikzpicture}
\complexdrawing{1}{1}{X}{X'}{Y}{Y'}
\draw (1.25, 0) rectangle (9.25, 4) ;
\end{tikzpicture}
\end{document}
```

#### Parallel composition

Another operation we can perform on lenses is to run two of them in parallel, we implement this
witht the aptly named function:
<!--

```idris
||| Parallel composition
export
parallel : Lens a b -> Lens x y -> Lens (cartesian a x) (cartesian b y)
parallel l1 l2 = MkLens (bimap l1.get l2.get) (\x => bimap (l1.set (fst x)) (l2.set (snd x)))
```
-->

A basic feature of lenses is that we can define and identity lens that does nothing in the
`get` part, and also does nothing in the `set` part:
<!-- idris
public export
-->

```idris
idLens : Lens x x
idLens = MkLens id (const id)
```

With `(|>)` and `idLens`, we have the basic building blocks to build the category of boundaries and
lenses.

We can also start building concrete examples like we have seen in the introduction by using `|>`.

```idris
-- type aliases
Year = String
Month = String
Day = String

record Date where
  constructor MkDate
  year : Year
  month : Month
  day : Day

year' : Dup Date `Lens` Dup Year
year' = MkLens year (\date, newYear => MkDate newYear date.month date.day)

record User where
  constructor MkUser
  firstName : String
  lastName : String
  birthday : Date

birthday' : Dup User `Lens` Dup Date
birthday' = MkLens birthday (\user, newBd => MkUser user.firstName user.lastName newBd)

johnWrong : User
johnWrong = MkUser "John" "Appleseed" (MkDate "2001" "01" "12")

johnCorrect : User
johnCorrect = MkUser "John" "Appleseed" (MkDate "2000" "01" "12")

userBirthYear : Dup User `Lens` Dup Year
userBirthYear = birthday' |> year'

-- because the next function uses lowercase identifiers in the type we need to use this setting
%unbound_implicits off
-- test that updating the birth year works:
testBirthYear : johnCorrect === userBirthYear.set johnWrong "2000"
testBirthYear = Refl
%unbound_implicits on
```

#### Lens coproduct

Using `parallel` and `|>` we can define complex operations by combining smaller lenses into
larger ones. Crucially, there is no coproduct operator on lenses that performs as we expect,
such combinator would have type: `choose : Lens a b -> Lens x y -> Lens (a + x) (b + y)`
with `(+)` defined on boundaries as the point-wise coproduct

```idris
(+) : Boundary -> Boundary -> Boundary
(+) x y = MkB (x.π1 + y.π1) (x.π2 + y.π2)

partial
choose : Lens a b -> Lens x y -> Lens (a + x) (b + y)
choose l1 l2 = MkLens
    (bimap l1.get l2.get)
    (let set1 = l1.set ; set2 = l2.set
    in \case (<+ v1) => \case (+> v2) => ?choose_rhs)
```

But we are stuck when implementing the hole `choose_rhs` because we have as goal.
The problem occurs when matching on the first two arguments, it is possible to match
on the left first, and then on the right, resulting with the context

```
   set1 : a .π1 -> b .π2 -> a .π2
   set2 : x .π1 -> y .π2 -> x .π2
   v1 : a .π1
   v2 : y .π2
─────────────────────────────────
choose_rhs : a .π2 + x .π2
```

This particular branching is impossible to implement with the given context. Either
we need more than the two `set` functions given by our lenses _or_ we need to make
sure that if the first argument is a left injection, then the second argument must also
be one. We will see later how containers and dependent lenses allow this second
implementation.
