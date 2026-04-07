

### Functional Programming & Dependent types

The content of this thesis spans three distincts area of knowledge, generally
associated with computer science, mathematics, and engineering, rather than
seen as one.

Because of the breadth of each topic, I cannot provide a comprehensive introduction
to all of them, instead I will give a small exposition of each, pointing out what
aspects to them I will be using, and drive the reader toward resources that might
help them get up to speed.

Functional programming is a core aspect of my research, it underpins every
aspect of this research, and is the foundation between all the topics
presented here.

Functional programming is a programming practice where the fundamental
building block is a _function_. This is in contrast to other programming
practices where the fundamental building block are objects, or stacks. This
notion of programming is particularly well suited to mathematical formalism
where one can build their entire language upon sets and functions
between them.

Functional programming has also been successful in large-scale industrial
operations, and many languages have, after observing the success of functional
programming languages in the industry, like Haskell and Scala, adopted key
features of functional programming languages: anonymous function defintions,
higher-order functions, and pattern matching. Because of this, it is no surprise
that we observe modern architectures make use of more declarative libraries to
write and maintain code (React, SwiftUI), rather than imperative ones.

Functional programming comes in many flavors but the one I will be using
is based on _pure, total, dependently-typed_ functional programming. That is:

- Programs cannot have side effects.
- Programs must terminate.
- Programs can manipulate types as a first-class construct.

The combination of those features make for an extremely flexible programming
experience, while maintaining the benefits of a typed-programming language.

One of the difficulties with types is that the type-system is sometimes unable
to understand that a program is safe, leading to the use of escape hatches
which erode trust in the system, whose entire purpose was to keep users safe.
Dependently-typed systems allow programs to appear in types, consequently,
programs can now be written in ways that only meta-programming
permitted before.

The combination of those features is also characteristic of a _proof assistant_
and I will make use of the ability of the programming language to prove statements
as well. This strategy showcases the ability of an advanced programming language
encompassing a wide range of use-cases, from low-level implementation, to
capable and robust abstraction mechanisms, but also formal verification and
proof. I will use the Idris2 programming language for my demonstrations,
libraries, and proofs.

## Category Theory

Category theory is the main toolbox to describe our programs and their properties.
This fits in decades of tradition since Moggi introduced monads
[[@moggiNotionsComputationMonads1991]] as the main abstraction for effectful computation.
Category theory has permeated the space as the main tool to represent and formalise
the semantics of programs. However, it also has the reputation to be slightly too high
of an abstraction to be useful, and for this, it is accused of being the source of \emph{abstract nonsense}.
The notions we will need are Functors, Natural Transformations, Monoids, Monads
and Actions. Those concepts will be presented as we go when we can relate them
to our use-cases in software engineering.

## Software engineering

Software engineering is often placed at odds with mathematical formalism, for commercial reasons. Getting things done as fast as possible as cheaply as possible creates an environment where avoiding programming errors is economically hard to justify. This creates an environment where academic research about safety of program is divorced from the day-to-day issues that arise in the
practice of software engineering. Because of that, the communities and their
interest are split by an ever growing chasm.
This work, however, really sits in the middle of this gap between software engineering and mathematics, one cannot be understood without the other. In particular, it is hard to motivate the development of the tools presented here without understanding the challenges that come up in industrial software engineering. There are two topics of software engineering that are central to the abstraction I will present: data structure manipulation, and backend server development.

### Server development

Server development is a large part of modern software products. The era of cloud
computing standardised the practice of applications connected to a server
hosting the one single source of truth for the internal state of the
application. This model only furthered developped with the large scale
deployment of mobile application which came with the expectation that software
must be cross platform and automatically synchronised between platforms. To
achieve this level of always-online architecture, applications adopted a model
where two program are developed in sync with each other: a client, often called
front-end, offering user-side programming logic, such as rendering and
interaction models. And a server, often called back-end, offering online
services, such as state retrieval, online collaboration and synchronisation.
While both front-end and backend development deserve more attention paid to
them, in term of mathematical formalisation, I personally found that backend
development is most amenable to mathematical reasoning. Because of this, it is
the topic I have decided to focus on when thinking about a problem to solve
using my knowledge of type theory, and mathematics. However, to empathise with
the problem in the first place, one need to be familiar with the challenges
surrounding backend software development. While I will not attempt to provide a
0-to-60 bootcamp-style introduction to server backend development, I will
attempt to showcase the problems that occurs as motivation to provide a
solution. This will require some amount of knowledge about network architecture,
network protocols and software libraries. Category theorists and computer
scientists, get ready to dust off your undergrad networking course.
