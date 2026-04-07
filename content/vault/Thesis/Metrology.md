## Interactive Systems in Metrology

Because of the tight relationship between the University of Strathclyde, and the National Physical Laboratory, I have had
the opportunity to learn about metrology and their tech stack as well as participate in developing solutions for their software.

The software written at NPL spans a large range between small bespoke scripts to complex services with a need for reliability and correctness. To demonstrate the power of an API-first architecture, we are going to replicate the functionality of an existing program using a high-level specification for it. The API-first architecture will then permits choosing what interaction model we want to use to interact with the program, without changing its core implementation.

Metrology software spans the entire spectrum, starting from hardward to cloud services. Those tools that perform
data collection require low-level drivers to communicate with conventional operating systems. Those in turn need to store
the data for further processing in a permanent storage solution, often a database. The content of the database is then accessed
by one or multiple scientists to perform analysis using off-the-shelf tools such as Python, R, or even Excel. The result
of this analysis is again stored in permanent storage such that it can be queries for certification or for further academic
analysis, like drawing graphs.

This workflow can be summarized by three interaction patterns:

- Data collection: Take the raw data and store it
- Data analysis: Once the data has been collected, we can run some analysis and store its result
- Data retrieval: After an analysis is done, we can output a certificate, as a PDF document

Each one of those interaction patterns can be written as a container, the first two perform a side effect on the storage solution, and the third reads the data base to generate a file.
In the container view we can write this is program as a lens `Measurement + Analysis + Certification => Storage` describing
all the ways to interact with the storage.

In this section, I will implement a prototype of a metrology stack using the containers-as-API architecture with the lenses
I suggested above. While showcasing the benefits it provides in terms of extensibility and providing multiple interfaces
for a common underlying data layer. This program uses the NodeJS runtime for is powerful and industry leading libraries.

### The data layer

The first step is to reproduce the database schema used in production for storing and retrieving measurement data. For this we use SQL bindings to Idris as well as a bespoke library that offers a container interface to SQL.

The database schema used here is not the real one used at NPL but one adapted to be smaller in scope yet still representative
of a conventional workflow at NPL. It contains 7 tables:

- Measurments: raw data from measuring devices
- Values: storage of resistor data after analysis
- Organisation: names associated with resistor manufacturers
- Resistors: list of resistors involved in the measurements
- Job: Identifier for a request of measurement
- Certificates: Certificates issued in the past using the data
- Status: Possible statuses for a single job

The way the data is handled is separate from the question of what messages make sense to send to the system. Like
mentioned above. there are three main messages we want to send, despite the fact that we have more than 3 tables.
This is a common pattern in API development, since the API is meant to abstract over the underlying details of the
storage strategy.

The SQL interface as a container is defined as a coproduct of two APIs: Commands and queries.

```
SQL_API : Container
SQL_API = DBCmd + DBQry
```

`DBCmd` is a container for _commands_ that do not directly run a query, this interaction model performs purely a side effect, and so its definition is `SQLCommand :- ()`. `DBQry` in the contrary runs a query and is expected to return a table of the type described by the query. Therefore it is defined with the container `(q : DBQuery) !> Table q.schema`.

Using the `DBCmd` container we can execute any message to the database using a costate `SQLM SQL_API =%> End`. The `SQLM` monad lifts responses into `EitherT SQLErr IO` to allow the database to perform side effects. We can now tackle the messages needed for this application. To abstract over this last wrapper, we define `SQL = SQLM SLQ_API`.

### Adding new measurements

When measuring the resistance of an object, we need to compare a
measurement with a _known_ resistor and so each measurement needs
to provide information about the measured resistor, called _unknown resistor_
in the code, and the benchmark, called _known resistor_.
Additionally, each measurement exists in the context of a _session_ as
identified by its date and the customer who provided the unknown resistor.
We can package the above information into a single message to add new
measurements to the database in a way that can be retrieved later.

To represent measurements we provide the type of a resistor measurement and then the type of a message that we send containing both the known and unknown resistor.

```
record ResistorMeasure where
  constructor MkResistorMeasure
  session_id : String
  ur_serial_no : String
  ur_device_type : String
  ur_dev_ppm : Double


record NewMeasurement where
  constructor MkNewMeasurement
  unknown : ResistorMeasure
  known : ResistorMeasure
  session : String
  date : String
  client : String
```

The container for this message is simply `Measure = NewMeasurement :- ()` because we do not expect any return value when we send the message, only confirmation that the side effect happened.

To implement this functionality we provide a lens `Measure =>> SQL_API` that converts the measurement into the appropriate database query

### Performing analysis

Once all the measurements have been taken, the relevant data needs to be
computed. This information is derived from the measurements and can be
done as an in-place update of the database from the `measurements` table
into the `values` table. The computation itself is quite simple, it amounts to
computing some averages from the measurement data. This computation can be done entirely through database queries, and it only needs the session ID to run. However we need to send three requests in a row to make it happen correctly. To represent such sequence of queries we use the composition operator containers and therefore provide a lens `SessionID :- () =>> SQL_API &> SQL_API &> SQL_API` to implement it.

### Generating certificates

Certificates are generated for customers according to the data that was
collected and analysed in the previous stages. Due to how the business
operates, certificates are generated from a single session identifier. All
measurements done during this session are the object of the certificate
and will find themselves in the output data.

This query also requires an ID to run but we expect a PDF file in return, therefore the interaction profile of this message is a container `CertID :- PDF`.

To simplify things, and also because it is good programming practice, we are going to first generate a JSON data that we will then convert to PDF. Giving us more flexibility in the way we export the data and separate the responsibility of generating a response with the data from the generation of the PDF itself. The final program would still be a lens `CertID :- PDF =>> DB` but most likely implemented in two steps, first `CertID :- PDF =>> ID :- JSON` and then `CertID :- JSON =>> SQL_API`. There is one final subtlety to handle and that's the fact that, unlike the other two message which always _add_ data and don't expect any result back, here we _expect_ something back and should advise when the data we expected is missing. Because of that we wrap the container in a maybe monad: `MaybeAll (CertID :- PDF)`.

### One implementation multiple interactions

The core of the implementation lies in the data base communication, before we do anything, we need to ensure we can contact a database
and perform queries. For this, we use the `runDB : Costate SQL` lens.
This lens is a _costate_, which directly converts queries into responses, it also wraps responses in the appropriate monad `SQLM` which returns
errors when the database fails to process a query.

First we sumarise the three types of interactions we have as containers

```
Certification : API
Certification = MaybeAll (CertID :- PDF)

Analysis : API
Analysis = SessionID :- ()

Measurement : API
Measurement = NewMeasurement :- ()
```

For each of those messages, we need to provide a lens that interacts with the database. We've already given the type of each translation into database queries, but because we are going to combine all three lenses into one, we need to have them share the same _codomain_. The type that can accomodate both inhabitants `SQL_API` and `SQL_API $> SQL_API $> SQL_API` is the Kleene star on containers, written `Star SQL_API`. With it, we can write all three lenses:

```
addMeasurement : Measurement =%> Star SQL_API
runAnalysis : Analysis =%> Star SQL_API
genCertificate : Certification =%> Star SQL_API
```

Using the coproduct on lenses we can combine everything into one big lens with a choice as the domain. We write this choice `AppAPI` to represent that the overall interface of the application.

```idris
AppAPI : Container
AppAPI = Measurement + Analysis + Certification

app : AppAPI =%> Star SQL_API
app = addMeasurement ~+~ runAnalysis ~+~ genCertificate |%> dia3
```

That is not the end because those three lenses merely convert messages and responses, but don't match the type of the costate that _runs_ queries. Remember that any database interaction needs to interact with a container `SQLM SQL_API` performing side-effects.

```idris
runSQL : DB => Costate (SQLM AppAPI)
```

To adapt our existing `app` to one that can handle side-effect we map across it and use the fact that side effects commute with the Kleene star.

```idris
runApp : DB => SLQM AppAPI =>> SQLM
```

We can now abstract over the "frontend" of the application and write
a function that will take a lens `a =%> MaybeAll AppAPI` and return
a costate that will implement the functionality of the application.

```idris
export
plugFrontend : DB => a =%> MaybeAll AppAPI -> Costate (SQLM a)
plugFrontend frontend =
       liftMap frontend
    |> distribMaybeAF {a = AppAPI}
    |> map_MaybeAll runApp
    |> maybeAUnit

```

`plugFrontend` can be understood graphically as the diagram:

This level of abstraction enable writing three implementation that each perform the same operations but with different interaction modes, the first one instantiates a HTTP server, the second one starts an interactive REPL, and the third one is run through the command line.

```idris
mainHTTP : DB => IO ()
mainHTTP = init >> http' (localhost 3000) (plugFrontend httpRouter)

mainREPL : DB => IO ()
mainREPL = init >> repl' (plugFrontend replRouter)

mainCLI : DB => IO ()
mainCLI = init >> cli' (plugFrontend cliRouter)
```

Similarly, given an appropriate translation from `AppAPI`, one can use different data storage solutions for the same application. For example, an in-memory one for testing, or a different data storage altogether, for example MangoDB.

```idris
MangoDB : Container

Memory : Container

toMangoDB : AppAPI =>> MangoDB

runMangoDB : Costate (IO • MangoDB)

runMemory : Costate (IO • Memory)

mainMangoDB : IO ()
mainMangoDB = cli' (lift IO (runApp |> toMangoDB) |> runMangoDB)

mainMemory : IO ()
mainMemory = cli' (lift IO (runApp |> toMemory) |> runMemory)
```

This compositional power allows for unprecedented flexibility in writing industry-ready software, carving slides of functionality where none could be seen before. The ability to precisely separate the main functionality from the database or the interaction model makes every component more readily reusable and exposes the requirement for which the code needs to be adapted to remain compatible with the existing architecture.

### The Command Line Interface

The comand line interface container is defined as `CLI = List String :- String` to mean that a CLI program takes a list of strings as input and returns a string to display in the standard output.

Any CLI program can be interpreted from a lens `CLI =%> End` using a function
```
cli : Costate CLI -> IO ()
cli cos = do line <- readLine
             output <- costate cos line
             putStrLn output
```
reading from the program arguments and printing the result in STDOut.

This representation assumes that there is a _parser_ for commands that maps the `CLI` API into the internal commands the program understands. Here is an example of a simple command line API with two commands

```
-f filename
json
```

Both of them operate on the same kind of data, but in one case, the data is sent via a reference to a file, and in the other, as an inline JSON value. We can represent this interface with a data type `data Arg = FileArg String | JSONArg JSON`. A parser for argument would have type `List String -> Maybe Arg`. From this data, there are two ways of implementing the program:

- Handle `FileArg String` and `JSONArg JSON` separately, treating the filename and the file content as two distinct programs.
- Collapse both constructor into one value of type `JSON` by reading the file off the filesystem.

We're interested in doing the second one because the processing of the file is going to be the same regardless of the way it was given as argument. To achieve this, we use the following functions:

```idris
readFile : String -> IO String

parseJSON : String -> Maybe String

readJSON : String -> IO (Maybe JSON)
readJSON name = parseJSON <$> readFile name

processJSON : JSON -> output
```

`processJSON` is the main part of our program, it generates an output that will then be converted into a string for output in the terminal. Once we line up the types as containers and lenses we have the following diagram:

![[IMG_0787.jpeg]]

The forward part will read the input file, and obtain a JSON from it, this JSON file is then converted into an output and the output is printed out. This approach has a big problem: The IO nature of reading files off the filesystem makes it impossible to write this program as a traditional _lens_.

This is because, writing out the types, there is no way to extract the dependency between the `JSON` file and its output if it is wrapped in an `IO` action.

```
fwd : List String -> IO JSON
bwd : (x : List String) -> output (fwd x) -> String
```

`output` expects a value of type `JSON` but is given a value `IO JSON`, because we are implementing this during typechecking, we cannot extract a value `JSON` from our `IO` action, this type is only inhabited at runtime.

This motivates the move towards monadic closed lenses. Recall the definition of closed lenses as a single continuation mapping between two containers:

```
Closed : Container -> Container -> Type
Closed a b = (x : a.message) -> Σ b.message (\y => b.response y -> a.response x)
```

We parameterise this definition with two maps `f, g : Type -> Type` to obtain monadic closed lenses:

```
Mon: (f, g : Type -> Type) -> Container -> Container -> Type
Mon f g a b = (x : a.message) -> f (Σ b.message (\y => b.response y -> g (a.response x)))
```

For this notion of morphism to compose, we require `f` and `g` to be _monads_. When both functors are the same, we use the notation `a -[f]> b` to indicate that the morphism from `a` to `b` is wrapped in the effect `f`.

Equipped with this notion of effectful lens, we can write lenses to operate on the filesystem to read files or read from standard input.

```
FSError : API
FSError = FileError :- Void

export
readLine : HasIO io => (() :- a) -[io]> (String :- a)
readLine = ioFwd (\x => getLine)

readFile : HasIO io => (String :- a) -[io]> (FSError + (String :- a))
readFile = \\ (\x => ReadWrite.readFile x >>=
              \case (Left y) => pure (<+ y ## absurd)
                    (Right y) => pure (+> y ## pure))

putStrLn : HasIO io => (a :- ()) -[io]> (a :- String)
putStrLn = ioBwd putStrLn
```

You will notice the `FSError` API, it describes errors when interacting with the filesystem. The responses being `Void` indicate that the error must be handled before reaching that layer of the stack. In most cases, we cannot recover from a file system error, and so the error is handled by printing out a nice error message and ending the program with an appropriate error code.

We would like our program to have the following interface:

```
metrology: Handle measurement data for customers.

options:
  add measure|(-f filename)
    Add the content given to the data base, argument could be either a measurement
    inline or a file name with multiple measurements.

  analyse id
    Perform analysis on a set of measurement with a common identifier. Do this once
    you have collected all the measurements for a given session.

  certificate filename id+
    Obtain a certificate for a set of identifiers. The certificate will be written
    in the current directory with the given filename.
```

### The HTTP Interface

For the HTTP interface, we do the same as we have done for the [[Meteorology.idr]] section and use our bespoke DSL do describe endpoints and generate parsers and serialisers for the data.

Our application's API is given by the coproduct `AppAPI = Measurement + Analysis + Certification` which suggests that we need three  different endpoints that each produce a `Measurement`, `Analysis`, and `Certification` message.

```tikz

\usepackage{tikz}
\usepackage{amsfonts}
\begin{document}
\newcommand{\myrect}[3]{%
  \draw (#1,#2) rectangle (#1+2, #2+1);%
  \node[font=\footnotesize] at (#1+1, #2+0.5) {#3};%
}
\begin{tikzpicture}
\myrect{0}{0}{parseInline}
\myrect{0}{1.25}{parseFile}
\myrect{0}{2.5}{parseSTDIN}
\myrect{0}{-1.25}{analyse}
\myrect{0}{-2.5}{generatePDF}

\end{tikzpicture}
\end{document}
```


### Conclusion and Possible improvements

The above is not meant to replace existing software in scientific applications, rather it is meant to illustrate
that the overall architecture emerging from containers as APIs is sophisticated enough to be applied to
real-world applications. While Idris is not going to take over data science any time soon, it is quite encouraging
to see that it is good enough _today_ to implement all the funtionalities of existing software in a matter of
hours. Not only the gain in productivity is remarkable, the flexibility of the framework allows for changes in
the features of the programs in a type-safe way previously impossible.

In recent years, the idea of generating _digital_ certificates rather than paper ones has gained traction. One
could ask themselves what it would take to implement digital signatures along with storage and retrieval of
the data in a way that ensures that certificates are appropriately signed with their corresponding digital keys
that identify each measurement.

While I have not done this work. I speculate we can do this by using the para construction on containers so
that each input contains both the data for a measurement, along with its cryptographic key that identifies
the measurement. Each access to the database is now made with a key so that both the data requested
and the key must match , otherwise the client might obtain a measurement that does not match the hardware
they use.
