# Containers as API, Morphisms as API-transformers

Containers can be conceptualised as a request-reponse pair. In this document, 
we use this request-reponse to model generic Application Programming Interfaces (API).
Using monoids on containers, those APIs can be combined to obtain richer APIs. This
practice gives rise to a programming paradigm where the container play the role of
types and container morphisms play the role of functions. Mapping between two containers
amount to translating between one interface to another.

## Illustrating containers as APIs: vending machines

We've already seen containers and their monoids but without explaining how they relate to
manipulating APIs. For this, I will use real-life analogies to illustrate what is the effect of 
different operations on containers when seen as an API.

We are going to use vending machines as the leading analogy for APIs. A vending machine
is a tool that takes in some currency, and outputs a product. 


*A vending machine selling various kinds of drinks and snacks*

We can illustrate the interaction model of a vending machine with the following diagram:



This interaction model can be represented as a container $(Currency \rhd Drink)$,
that is, the client provides some amount of currency, and the result is a drink.

### Using two vending machines at once

Imagine now that we have two different vending machines, one that sells hot, and
one that sells cold drink. The one selling hot drinks takes Japan Yen(JYP) as currency,
the one selling cold drinks takes US Dollars (USD). 

You're now with a friend and task them to buy for you one cold drink, and one hot one.
For this, you need to give them both USD and JYP. After a short time they come back
holding both a hot coffee and a cold ice tea.

This interaction model is the parallel product of containers, the container for the cold
drink machine $(USD \rhd cold)$ and the one for the hot drinks $(JYP \rhd hot)$. For you
to properly request the two drinks, you need to provide a pair of USD and JYP and you will
obtain a pair of drinks, one cold and one hot, the container is then 
$(USD \times JYP \rhd cold \times hot)$

<!-- ![[77a3fe60fa45cb706f21f395c92ef27b8b7280ea.pdf]] -->

### Dealing with the demon

Now you friend is thirsty as well and want to take one of your drinks, you don't have a preference
between hot or cold, so you give both currencies to your friend, and they will come back to you
with one of the drink, and keep the change. In this circumstance, from your point of view, you
provide both currencies, but obtain only one of the two drinks. It is therefore a container
$(USD \times JYP \rhd cold + hot)$. This operation is the dirichelet product on containers.

This mode of interaction enables some non-determinism on the part of the response, although
we provide all possible inputs in the request.

### Making choices ahead

If you are in front of two vending machines that accept two different currencies, and you want
a drink, but do not really care from what machine it comes from, you need to make the choice 
of a vending machine. Once the choice is made, and you've given your money, the response
will always match the choice you've made ahead. If you gave USD, you will obtain a (cold) drink
from the USD vending machine, and if you've given JYP, you will obtain a (hot) drink from the
JYP machine. It is impossible for you to spend USDs and get a drink form the JYP machine.
This interaction model indicates that given a choice of request, the response will always match
the original request. We write this as a coproduct on the request, and an eliminator on the responses
$(USD + JYP \rhd [hot, cold])$ where $[hot, cold]$ is the function with type 
$a + b -> (a → Type) → (b → Type) → Type$
that matches on the input and applies the first or second argument function to the argument.

$[f, g] (inl\ x) \mapsto f\ x$
$[f, g] (inr\ x) \mapsto g\ x$



Alex and Jay

Alex asks Jay to buy her a drink, she doesn't know exactly what she wants but both are in a hurry
so she says "Jay here are some yens and USD, just get me anything from either machines I don't care"

Jay then walks away and comes back with a cold drink. "That all they had", Alex infers that 

What happens when jay buy a drink?

Jay starts by inserting money into the machine, the machine then lights up only the drinks that Jay can afford
with the amount inserted. For example Jay inserted 100 yen and only the top row lighted up. That's because 
the next three row of drinks are 120 or 200 yen.

This dependency indicates that the set of follow up actions depends on the previous interaction with the
machine. enabling only a subset of available action depending on the value of the first interaction.

To make a decision Jay also has a choice, in fact, Jay has as many choices as there are drinks. Each drink
it itself a small interaction structure between its label and its physical manifestation. For example if
a can of coke is labeled with the number 21, then the interaction model for ordering a can of coke is the container
$(21 \rhd coke)$. Selecting a drink from the vending machine is therefor a choice between all possible interaction
fragments that order an individual drink. so the vending machine api for odering is 
$(number \rhd drink) = (01 \rhd coke) + (02 \rhd tea) + (03 \rhd coffee) + \ldots$