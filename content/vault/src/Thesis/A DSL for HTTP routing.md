
One of the strength of the system presented here is that it fits perfectly with existing programming practices, allowing to write code
in a very intuitive yet, correct way. Not only the code will be correct, _it cannot be wrong_, this is the power of correct-by-construction 
software.

Server development involves routing requests. There is a number of libraries that make this experience much nicer, few of them 
allow type-safe manipulation of request, none allow manipulation of entire APIs at once. This is what this section is about: how
do we make writing web APIs easy and type-safe in a way that enables routing automatically.

## What is a Web API?

First, a small review of about Web APIs. I'm going to refer to "Web API" any list that describes multiple kinds of HTTP requests
that one can send to a server. This lists form the "API" of the server, to avoid confusion with general purpose use of the word
"API" I will specify "web API" instead. Each element of the list is a description of an HTTP request one can send, I will call
each of those request description an "endpoint". Ideally each endpoint specifies the following:
- A URL path
- An HTTP method
- A header
- A list of query parameters
- Depending on the method, a request body
- A list of possible answers to the request

The URL path is a path as-in filesystem paths. Historically, those were indeed paths in the filesystem of the server, but in 
recent years, it has been repurposed as a way to select what functionnality the server shoudl perform for the client.

The HTTP method is an enumeration of X possible values. Again, historically, they were meant to represent different kinds
of file manipulation on the server, but now, it is used to further specify the kind of functionality we expect from the server.

Request headers contain metadata about the request itself. It will record where the request comes from, what kind of data
is contained within it. What size it is and so forth. Usually request headers do not contain very much data, but sometimes
authentication data can be stored within it.

Query parameters are dictionary containing arguments, they are inserted as part of the path of the request. The play the
role of carrying data when the request itself does not carry a request body. For example `GET` requests are not meant to
carry a request body, and so, to send data to the server along with a `GET` request, the data is placed within the query
parameters instead.

While `GET` requests cannot have a request body carrying data, `POST` requests can. This kind of information turns the
type of HTTP requests into a dependent type since, depending on the value of the HTTP method, the request might or 
might not have a request body. It is important to notice that the request body is just arbitrary bytes, and the way to 
interpret them is given by a value in the header, another example of dependent types.

Finally, each request sent to a server should result in the server responding to the client. Responses have their own format
but the most interesting part of it is:
- Has the request succeeded
- If so what is the value
- If not, why?
Requests come back carrying "response codes", numbers indicating what happened on the server. Code `200` means that
everything went well, `4xx` and `3xx` indicate different kinds of errors that typically occur, the most well known might just
be "Error `404`, page not found".

## A DSL for Web APIs



## Web APIs as Containers

The key insight necessary to understand the solution I propose is to identify what web APIs are, and how our container
model fit that description. 