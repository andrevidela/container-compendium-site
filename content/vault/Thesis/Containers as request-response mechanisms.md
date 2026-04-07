
Until now we've seen structures over containers but nothing about how to use those structures to build programs. There are two things that are important to state relating to this section:
- Software is complex, and while complexity cannot always be avoided, it can be tamed using different kinds of abstractions. The problem I want to solve is the one of building large applications that talk to each other using different protocols, languages even. Because of the nature of software and programming languages. It is very hard to talk about what makes multiple pieces of software in different realm compatible or _composable_. This problem of combining multiple pieces of software from different realm is what I would like to solve
- The essence of category theory is compositionality, compositional system are not necessarily easy or simple, but they give a notion of "building up" objects using exisitng ones, in a such a way that the larger complex system remain compatible with the smaller more primitive ones.

I hope you can see how applying category theory to the problem statement would be a potential recipe for a solution to the stated problem. What is left to do is pick an appropriate representation for the objects we are trying to manipulate. 

What I've chosen to focus on are Containers, and how containers form the basis of an Application Programming Interface (API). When containers are APIs, container morphisms are API-transformers, mapping from one interface to another. Effectively acting as a _translator_. This ability to translate from one API to another gives us the power to talk about high level abstractions and implement them in terms of lower level APIs. This chapter is about why containers and their morphisms form the perfect language to talk about APIs and how their morphisms enable the implementation of APIs in terms of other APIs.

### Containers are APIs

An API is a specification for interacting with a program. It does not say how the program should be implemented, but it says what messages the program expects, and what responses the program will return for each message sent. Here are examples of APIs:

#### The Open Weather API

https://openweathermap.org/api/one-call-3#current

If you want to obtain weather information about a location on earth, you can perform an HTTP request at the Open Weather servers and obtain a response that will include the information that the server has for this location. Because of the nature of this work, I think it is interesting to look at the types involved. This API takes in argument three values: 
- Latitude.
- Longitude.
- API id.
The first two define the geographical position, the last one carries a unique identifier used for billing each individual user of the API.

The server will then send a response containing a record of fields including:
- The latitude that was asked about.
- The longitude that was asked about.
- The timezone at the location
- The current weather information as a nested record
- The hourly forecast for that location as a nested record
- and more…

One way we could type this request is by using a product over all fields used. The API would amount to some notion of asynchronous effectful function 

```
Lat * Lon * APIKey -> Lat * Long * Tz * Weather Current * Weather Hourly * …
```

Of course this is a big over-simplification, but for now I want to focus on giving intuition rather that delving into the details of HTTP.

#### A Filesystem's API

Modern computers are built of many individual parts that talk to each other using shared conventions. Some of those convention include not only what kind of messages a system receives and responds, but also a specific order in which the messages need to be sent. One example is how a programming language such as C interacts with the operating system to interact with files.

File storage is complex, due to the variety of formats it can take, thankfully, operating systems aim to abstract away the details of storage technology and provide a singular API for all programs. This API is then translated into lower-level instructions via a driver to interact with the physical media and store the data. Posix is a popular convention to provide basic access to computer hardware. Implementations of Posix in operating systems such as Unix, Linux, MacOS all implement the same set of basic operations to allow software to interact with basic operating system features. One of them is how software is meant to interact with files.

Regardless of the hardware layer, the operating system provides a common interface for programs to write and read files from storage. This interface is composed of the following functions:

- open
- Close
- Read
- write

What makes this interface different from the ones we have seen before is that it is _stateful_. You need to call "open" before doing anything else. You cannot perform any action after calling "close".  Any valid interaction with this API will start with "open", have any number of "read" and "write", including 0, and end with "close".

If we were to write this using a syntax reminiscent of a BNF grammar we have that the API can be described like this:

``` 
OPEN := "open"
CLOSE := "close"
READ := "read"
WRITE := "write"
WR := READ | WRITE
API := OPEN WR* CLOSE
```

There are many APIs that require the client to send a subset of queries in a given order, like web APIs to login, request 2-factor authentication codes, Bluetooth connection protocols, 