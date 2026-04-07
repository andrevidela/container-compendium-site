OKay so this is both my thesis and research work so I think it should go here before it goes into my thesis: I've been exploring how to push effects outside of the container language for as much as possible. Previously I was using lenses enriched in a monad to model effects in the forward part. 

TO be perfectly comprehensive, the problem i have is as follows:

I have a function $a → m\ b$ that is paired with a function $b' → m\ a'$. Ideally I would like those two to form a lens $(a, a') \Rightarrow (b, b')$ But of course the monad $m$ gets in the way.

To address this, I have been using morphisms of the form $(a, a') \to^m (b, b') = (x : a) → m (Σ (y : b)) . b' y → m (a'\ x)$ This works, but it's a little bit unsastifactory because it introduces effects inside the lenses, but we would like to have them be outside so we can have better control of them. We can reduce the proliferation of effects using the "functor application" operator which I define like so 
- $\bullet : (Set \to Set) → Cont → Cont$
- $F \bullet (a, a') = (a, F(a'))$

and monad-enriched lenses compose with functor-applied lenses so $b →^m c$ composes with $m \bullet a → b$ to form $a \to^m c$, that helps but it's still not great.

That's the old approach, now here is the new approach:

Instead of pairing up $a → m\ b$ with $b' → m\ a'$, we are going to think of $a → m\ b$ as the _costate lens_ $m \bullet a \Rightarrow I$ and $b' → m\ a'$ as the continuation from $a$. The only reasonable way of combining those two this way is with a lens of type $(a, a') \Rightarrow (a, b) \circ (b', 1)$ and treat $(a, b)$ as the effect of the lens $(a, a') \Rightarrow (b', 1)$. This is of course a co-parameterised lens $a \Rightarrow^p b$ where the monoidal product used is composition $\circ$. Another way to see this lens is as _a writer monad that add an effect token_, but doesn't actually perform the effect, it only declares a pair of input-output that needs to be executed by an external handler.

We see this notion of handler when we try  to turn those lenses into executable programs. A lens $a \Rightarrow b$ becomes executable when we give it a costate (or a _handler_) for b $handler: b \Rightarrow I$. Whenever we deal with a coparameterised lens, we need to give two handlers: one for the effects and one for the codomain that is, $a \Rightarrow^p b$ becomes executable if we have $effectHandler : p \Rightarrow I$ and $valueHandler : b \Rightarrow I$. 

Now where does that leave us wrt to effectful computation using a monad in $Set$? well it turns out there is a more powerful version of the effect handler above. we can write the following:
$handle : a \Rightarrow^p b → m \bullet p \Rightarrow I → m \bullet b \Rightarrow I → m \bullet a \Rightarrow I$
That is. Given a parameterised lens $a \Rightarrow^p b$ and two _effectful handlers_, we can compose the lense with its effectful handlers and obtain an effectful costate lens in this case isomorphic to a function $(x : a) → m (a' x)$. All this even if the original lens has _ZERO_ effectful computation in Set. It also allows the user to chose $m$ at a later date, leaving the effect specification only for running the program later, not as part of its specification originally.

I'm still exploring how this is used when combined with kleisli category of monads on containers (typically `Maybe : Cont -> Cont`) and I'm not done with my basic prototype that uses `m = IO` and reads a file off the filesystem, but so far, things seem to be working as expected 