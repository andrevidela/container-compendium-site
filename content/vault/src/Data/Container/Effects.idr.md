<!-- idris
module Data.Container.Effects

import Data.Category.Endofunctor
import Data.Category.Set

import Data.Container.Lift
import Data.Container.Apply.Definition
import Data.Container.Definition
import Data.Container.Morphism
import Data.Container.Morphism.Context
import Data.Container.Tensor.Bifunctor
import Data.Container.Tensor.Monoidal
import Data.Container.Sequence.Bifunctor
import Data.Container.Sequence.Monoidal
import Data.Container.List.Functor

import Data.List.Quantifiers

import Data.Vect

import System
import System.File
import System.Utils

import Syntax.PreorderReasoning.Generic

import Control.Monad.Either
import Control.Monad.Trans

readChars : List Char -> IO (List Char)
readChars acc = do
  end <- fEOF stdin
  if end
    then pure acc
    else do
      c <- getChar
      assert_total $ readChars (c :: acc)

readLines : IO (String)
readLines = reverse <$> pack <$> readChars []
-->

## Running Effects


Functorial lifts and costates give us all the tools to describe effects
in the category of lenses.
Programming with pure functions is extremely helpful in writing correct
software as it dramatically reduces the combinatorial space, which in
turn reduces the opportunity for bugs to appear. But at some point, a program
needs to interact with the outside world, and this interaction is modelled with
an effect.

Functorial lifts explain how to introduce an effect in the fibre of a container
which we can then use as a costate to introduce an effectful function.

```idris
-- an effectful program can be seen as a costate lens with an IO lift
-- since it's isomorphic to a function (m : program.message) -> IO (program.response m)
exampleEffectfulLens : Costate (IO • program)
```

But sometimes we want to place an effect in the _forward_ part of a lens, for example
a program that reads a file from the filesystem and passes along to the rest of the program.
We can imagine a lens interacting with the fileSystem and the terminal that reads files
in the forward part, and prints files in the backward.

```idris
covering
readPrint : String :- IO () =%> IO (Either FileError String) :- String
readPrint = readFile <! const (putStrLn {io = IO})
```

And if this lens was to be turned into a costate it would have the completely
appropriate type `String -> IO ()`, but turning it into such costate is barrier
to using this approach. To do so would require coming up with a lens
`Costate (IO (Either FileError String) :- String)`, which implies defining a
function `IO (Either FileError String) -> String`. But because the argument
is wrapped in `IO`, we cannot extract it from the `IO` monad, the only
thing we could do is also wrap the output in `IO` and use a lens of type
`IO (Either FileError String) :- IO String`. But this is very unsatisfying
because now the backward part of `readPrint` is inaccurately defined since
it's requires a function `IO String -> IO ()` but in reality we do not require
the input to be in `IO`.

This kind of changes is to be expected from effectful programs, once inserted
they tend to pollute the rest of the program, sometimes needlessly.

In this section we are going to see how to introduce effect such that we can
carefully control where and when they occur and ensure their scope is only
as big as necessary. We are going to drive the development of effectful
lenses by implementing a simple but highly effectful program, `tee`.

### The `tee` program

`tee` is a command line utility taking some input on standard-input
and a destination file and performing two actions at once: printing and
writing to the file.

The name `tee` refers to the pronounciation of the letter `T` which represents
the flow of information that the utility performs.

```

STDIN >───────•────────>STDOUT
              │
              │
              │
              │
              V
          Filesystem
```

This programm is full of side-effects, reading from STDIN, reading command-line
arguments, writing to the filesystem, there is almost nothing pure about this
program, so how do we write it using lenses? What even is its API?

Because this program takes no input in argument, its messages are trivial, because
its output is only a side-effect, its output is also trivial. The API of this
program is therefore `Unit :- Unit` the tensor unit, written `I`.

Running this program however results in a definition of type `IO ()` or `() -> IO ()`
which is the continuation represented by the container `IO • I`

Effects in this setting are represented by delegating the effect to an outside
process via the sequence product. For example, the effectful printing interface
takes a string and returns unit : `String -> IO ()`. As a container we can see
this as the term `IO • (String :- Unit)`. We can separate the role of `IO` from
the interface of the function and write

```idris
PrintLn : Container
PrintLn = String :- Unit
```

Because our program `Tee` reads from the command line, and that's also an effectful
operation, we reproduce the same strategy by identifying what "reading the command-line
arguments" means as an API. Because it's implemented with a function
`getArgs : IO (List String)` we see this as a container `Unit :- List String` and wrap
the fibre in `IO` for its handler.

```idris
GetArgs : Container
GetArgs = Unit :- List String
```

The API for writing to a file takes a string in argument and does not return anything, except
errors, ignoring effects, the API is therefore `String :- Unit`

```idris
record WriteFileOp where
  constructor MkWrite
  filename : String
  content : String

WriteFile : Container
WriteFile = (WriteFileOp :- Unit)
```

Finally, we need to read STDIN, this purely effectful program takes no argument and produces
a string delimited by an `eof` token.

```idris
STDIN : Container
STDIN = Unit :- String
```

We now have all the pieces to write out `tee` program using containers by describing the effects
it performs. First we need to read the command-line arguments to find out to what file we are going to
write the output. We also need to read the standard input to collect the data to write. Once both of those
actions are done, we need to write the content collected to a file with the name given in argument and also
to standard-output.

```idris
Tee : I =%> (GetArgs ⊗ STDIN) ▷ (PrintLn ⊗ All.List WriteFile)
```

Notice the careful mix of tensor and sequencing, indicating some operations can happen concurrently
but others need to happen in sequence. The implementation of this lens performs the data shuffling one
would expect by using the command-line argument as file-name for the write operation and duplicating the
data from `STDIN` to feed it to both `PrintLn` and the write operation.

```idris
Tee = state  (MkEx (() && ())
    $ \case ((_ :: files) && content) => content && map (\file => MkWrite file content) files
            (_ && content) => content && [])
```

The program is written but is currently purely symbolic, we cannot execute `Tee` since there is no way
actually extract the information from the operating system, for this we need `IO` and error handling.

To implement a lens with side effects, we need to provide _handlers_ for each of their advertised effect.
In our case we need a handler for `GetArgs` `STDIN` `PrintLn` and `WriteFile`. Those handlers
are going to work in `FSIO = IO . Either FileError` a IO Monad capable of throwing filesystem errors. The
implementation is routine as they merely use the functions exposed by idris's filesystem library.

```idris
FSIO : Type -> Type
FSIO = EitherT FileError IO

handleSTDIN : Costate (FSIO • STDIN)
handleSTDIN = costate $ const (lift readLines)

handlePrintLn : Costate (FSIO • PrintLn)
handlePrintLn = costate $ lift . putStrLn

parseN : (n : Nat) -> List a -> Maybe (Vect n a)
parseN Z [] = Just []
parseN (S n) (x :: xs) = (x ::) <$> parseN n xs
parseN _ _ = Nothing

handleGetArgs : Costate (FSIO • GetArgs)
handleGetArgs = costate $ \_ => getArgs

handleWriteFile : Costate (FSIO • WriteFile)
handleWriteFile = costate $ \(MkWrite name content) => MkEitherT $ writeFile name content
```

We've seen before that any lens `a => b` can be "run" if we provide a _costate_ `b => I`. To run
effectful programs, the same intuition holds but needs to be adapted to take the effects into account.

In particular, we need to explain what happens when we have multiple effects that are sequenced and also
run in a monad $m$, such lenses have type $a ⇒ b ▷ c$ and need to result in a lens $m • a ⇒ I$.

````theorem
A lens $a ⇒ b ▷ c$ can be run _with effects_ if we provide costates $m • b ⇒ I$ and $m • c ⇒ I$ and results in a _costate_ $m • a ⇒ I$.
````

The proof is given by this sequence of operations involving the fact that `m • _` is a functor and there
is a map `δ : m • (a ▷ b) => m • (a ▷ m • b)`:

```idris
run : {m : Type -> Type} ->
      {a, b, c : Container} -> Monad m =>
      Costate (m • b) -> Costate (m • c) -> a =%> (b ▷ c) -> Costate (m • a)
run handleB handleC lens =
  CalcWith {leq = (=%>), x = m • a, y = I} $
    |~ m • a
    <~ m • (b ▷ c)
      ...(fmap {m} lens) -- map our lens into one with effects
    <~ m • (b ▷ m • c)
      ...(δ)             -- distribute the effect
    <~ m • (b ▷ I)
      ...(fmap {m} (identity b ~▷~ handleC)) -- handle the nested effect
    <~ m • b
      ...(fmap {m} (unitR1 {a = b}))         -- remove the extra unit
    <~ I
      ...(handleB)                           -- handle the remaining effect
```

We apply this principle here to our `Tee` lens to run it and turn it into a costate `() -> IO ()` which
is equivalent to `IO ()`, the signature for a `main` function.

<!-- idris
export
pushTensor : Monad m => {0 b : Container} ->
    m • (All.List b) =%> All.List (m • b)
pushTensor = (\x => x) <! pushBwd
  where
    pushBwd :
      (xs : List b.request) ->
      All.All (m . b.response) xs ->
      m (All.All b.response xs)
    pushBwd [] x = pure []
    pushBwd (y :: ys) (x :: xs) = do
      x' <- x
      xs' <- pushBwd ys xs
      pure (x' :: xs')

-->

```idris


covering
main : IO ()
main = eitherT
  printLn  -- print errors
  pure  -- handle values in IO  normally
  $ runCostate teeProgram () -- run the `() -> IO ()` program
  where

  -- handling the command line input and stdin input
  handleInputs : Costate (FSIO • (GetArgs ⊗ STDIN))
  handleInputs = CalcWith $
    |~ FSIO • (GetArgs ⊗ STDIN)
    <~ (FSIO • GetArgs) ⊗ (FSIO • STDIN)
    ...(distribTensor {m = FSIO, a = GetArgs, b = STDIN})
    <~ I ⊗ I
    ...(handleGetArgs ~⊗~ handleSTDIN)
    <~ I
    ...(unitR {a = I})

  -- Handling the printing and the writing at once
  handleFile : Costate (FSIO • (PrintLn ⊗ All.List WriteFile))
  handleFile = CalcWith {leq = (=%>)} $
    |~ FSIO • (PrintLn ⊗ All.List WriteFile)
    <~ FSIO • PrintLn ⊗ FSIO • All.List WriteFile
    ...(distribTensor {m = FSIO, a = PrintLn, b = All.List WriteFile})
    -- distribute the effect across ⊗
    <~ FSIO • PrintLn ⊗ All.List (FSIO • WriteFile)
    ...(identity (FSIO • PrintLn) ~⊗~ pushTensor {m = FSIO, b = WriteFile})
    <~ I ⊗ All.List I
    ...(handlePrintLn ~⊗~ mapList handleWriteFile)
    -- Handle printing and writing the file concurrently
    <~ I ⊗ I
    ...(identity I ~⊗~ elimI)
    <~ I
    ...(unitR {a = I})

  -- The program after applying all handlers
  teeProgram : Costate (FSIO • I)
  teeProgram =
        (run {a = I, b = (GetArgs ⊗ STDIN), c = PrintLn ⊗ All.List WriteFile}
            handleInputs handleFile Tee)
```
