**Proof assistants are great.** You can use them to prove critical properties
about large software systems (like the absence of certain costly or dangerous bugs).
The act of proving critical properties about
a software system is called _verification_, and the act of engineering large
verified software systems is called _[proof engineering](https://dependenttyp.es/pdf/QEDatLarge.pdf)_.

I like to work on **automation** for these proof assistants.
The [intro lecture for my class](https://www.youtube.com/watch?v=bzo4FTAmaOM)
(which is just twenty minutes long) is a good summary of what these proof assistants
are and how they work, and what automation can do and why I care about it
(and why I think everyone should care about it). It's a pretty good tl;dr of this repository,
and probably watches well on 1.5x speed.

I'm going to write more stuff here though because I'm bad at not talking.
And I'm going to drop some files in here that I use as demos for people who
want to learn things.

# How Proof Assistants Work

To develop a verified system using a proof assistant, the proof engineer does three things:

1. **programs** in a functional programming language,
2. **specifies** what it means for the program to be correct, and
3. **proves** that the program satisfies the specification.

The process of writing this proof is **interactive**: The proof engineer sends strategies
(called _tactics_) to the proof assistant to solve an outstanding proof obligation, and
the proof assistant responds with a new proof obligation. This continues until the proof assistant finds a proof that it can check.

**Fun Fact**: In my favorite proof assistants, the proof that the proof assistant
discovers and checks in the end is actually a _term_ in that same functional programming
language that the proof engineer uses to implement the program. A proof proves a theorem
when the term corresponding to that proof has the _type_ corresponding to that theorem.
So the proof checker is literally a type checker. Just, for a very fancy language
where terms and types can express really beautiful things like induction, universal
quantification, and computation of existing terms in the program. Like you can write a type
like "for all n, the length of appending two lists of length n is 2 * n," and that type
is inhabited precisely by the proofs that such a statement holds. This badass correspondence
between programs and proofs is called the _Curry-Howard Isomorphism_. Boom, baby.

# Separation of Concerns

OK so what's really, really cool about the process of writing these proofs is that
these tools have this beautiful separation of concerns between _producing_ the proof
and _checking_ the proof. The proof checker is a **small logical kernel that can be vetted
by a human**---this and the specification that one proves are the _trusted_ parts,
which is why human vetting is important.

What this means is that the rest of the process is _trustworthy_, not just _trusted_.
Like, we can stick **arbitrarily fancy automation** on top of the process of producing the proof,
as long as we don't touch the kernel, and as long as we vet our specification in the end.

**Fun Fact**: This separation of concerns is called the _de Bruijn criterion_, if you're
curious. Yes, I'm pretty sure it's because of the same de Bruijn dude who did literally
everything else.

# Tell Me More About Automation

**Proof automation** is my jam, like I teach [a whole class](https://dependenttyp.es/classes/598sp2022.html) on it. Check it out if you're intersted! The schedule of that class is
basically set up to read like a textbook. At the bottom of each page for each reading
or hacking session, there's a link to the previous session and to the next session.
This took me hundreds of hours to put together so I do appreciate people reading it
and doing the exercises.

The [tactics](https://dependenttyp.es/classes/artifacts/6-languages.html)
I mentioned earlier are one traditional kind
of automation people write---and these tactics can pretty much encode arbitrary
search procedures (like literally whatever you want to write in OCaml) as long as,
in the end, they produce a proof that the kernel can check.
We can think of this process of going from tactics to something that the kernel can check
as a kind of compilation from a high-level language of search procedures down to a low-level
language of _proof objects_ or _proof terms_---kind of the binary of proofs.

So what kinds of tactics _do_ people use? Typically things like decision procedures,
domain-specific or program-specific automation strategies, more general
proof strategies (like induction), and a whole lot more. But we can get _way more creative_
than that.

**Fun Fact**: The first proof of program correctness was written by Alan Turing in the 1940s. He was a cool dude.

# Oh? How Creative?

I recommend [this podcast](https://soundcloud.com/thesis-review/41-talia-ringer-proof-repair) to hear some of my recent ideas, but like, some examples:
A tactic can _take a proof term as input_ and _transform it_ to create another
proof term, like quite literally a _proof term transformation_ (a program
transformation, but for proofs). We can use this to do pretty much whatever we could do to programs by transformation: refactor them, repair them, mutate them to find new proofs 
of new theorems, adapt them across libraries, compile them across language levels.
We can even do wild things by the way like _slap a whole-ass neural network_ behind a tactic
or have a neural network produce tactics (neural automation working with symbolic 
automation as building blocks, which is very cute), as long as in the end we produce a term.

This is the blessing of de Bruijn. A whole world of automation to explore.
An oracle to check the end result. **Arbitrary power**, but **no loss of guarantees**.
This is why I love proof assistants.

**Fun Fact**: Polar bear fur is actually translucent, not white.
(IDK I'm out of proof facts for now, and I like bears a lot.)

# Some Cool Proof Assistants

A small sample:

- [Coq](https://coq.inria.fr/)
- [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php)
- [Isabelle/HOL](https://isabelle.in.tum.de/)
- [HOL](https://hol-theorem-prover.org/)
- [Lean](https://leanprover.github.io/)

# Some Cool Verified Systems

An even smaller sample of [vast, vast literature](https://dependenttyp.es/pdf/QEDatLarge.pdf):

- [Bagpipe](http://bagpipe.uwplse.org/bagpipe/) verified BGP configuration checker, lest we try to bring the whole internet down again
- [CompCert](https://compcert.org/) verified optimizing C compiler, used in airplanes
- [Fiat Crypto](http://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf) verified cryptographic code, used in BoringSSL which is in Chrome and Android
- [seL4](https://sel4.systems/) verified operating system microkernel, used to make an autonomous helicopter resilient to hacking
- [DaisyNFS](https://www.chajed.io/papers/tchajed-thesis.pdf) formally verified
concurrent file system, extremely performant with strong guarantees

# Can We Verify Machine Learning Systems This Way?

Oh, which part of the systems? I guess "yes but" is kind of my answer here.

**The Models**: So far, there hasn't been much work here, but I think there's a lot of hope
for embedding models and reasoning about them interactively. IMO this shouldn't be
much different from embedding a state machine and reasoning about it interactively,
and there is a ton of work on embedding very large state machines while concisely
representing them and avoiding state space explosion. I think one could do something
similar for a large neural network, and I think it'd be fun. It'd also let you kind of
interactively explore parts of the network. I want to try this one day with a small
neural network to start.

**The Training**: Yeah there is existing work here and if there's anything you'd like
your code here to do, this really isn't an issue, it should be totally doable.
Interfacing with Python might be annoying though, and you're probably writing Python.
Getting probabilistic guarantees might be somewhat annoying but it has been done.
Thinking of useful specifications might be hard still.

**The Framework**: Yes you're all just compilers people in disguise. 
For sure it's possible to verify important properties of machine learning frameworks 
and languages this way. Not just possible, but also probably pretty tractable.
Like we have so much work on verified compilers and languages.
This would be fun.

# But This Clashes With My Programming Workflow >:(

That's cool. That's why **I'm so obsessed with making these easier to use**.
I think the future will feature a smooth continuum between tests and proofs,
drawing on all sorts of automation with a nice interface to look _[a hell of lot better](https://twitter.com/TaliaRinger/status/1365433319572185092)_. I'm excited to build
this future. I just want lots of people to help me out!

