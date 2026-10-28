# sponge
A modular proof checker for propositional axiomatic systems aimed at allowing the user to work at a high level of abstraction, so that the user can sketch axiomatic proofs as if on paper and get them automatically checked. 

### The project has a few guiding ideas/goals: 
- The user should input proofs as close to as they would on paper
- The user should be able to abstract parts of a system that they are not focused on away
- The specifications of the logics should reflect their modular nature
- (I get some practice with Haskell and Datalog)

On the first point, the idea is the tool should be easy to use for anyone who wants to learn axiomatic proofs or practice them or do them for fun, _regardless_ of their programming background. (I should say I think sponge is _currently_ far from that goal, particularly for people looking to learn doing axiomatic proofs.) Since axiomatic proofs are usually taught on paper (in math and philosophy from my experience at least), having the input resemble how the user would write proofs on paper makes the learning curve for the tool as smooth as possible. Right now, proofs are fully in `.txt` files, but specifications and adding derived rules/abstractions involves getting into the Haskell code, which is less optimal. (The reason I've left the specifications in Haskell is that I found myself thinking that the Haskell data structure for specifying logics isn't all that opaque, and other ways of defining them it seemed to me would be only marginally less opaque. See [`Defs/Specs.hs`](Defs/Specs.hs) for the Haskell specifications of logics.)

On the second point, if you follow an axiomatic system to the foot of the letter then you have to justify _every_ line with an axiom or an inference rule. This doesn't correspond with how axiomatic proofs are done for systems where the user only cares about the reasoning relative to a fragment of the language, like in axiomatic proofs in modal logics. Consequently, the idea is to, as much as possible, let the user be able to abstract away rote sequences of axioms and inference rules, with e.g. derived rules, citing previous results, etc, if the point of the proof at hand isn't those steps, while at the same time having the proofs compile down to a datalog representation that is just rote axiomatic checking.[^1]

[^1]: Part of abstracting things away is being able to define derived rules. Right now, defining derived rules isn't too straight forward (see the derived rules for K reasoning and strengthening in [`DerivedRules`](DerivedRules)). Although derived rules are done in Haskell and so require some comfort with code, the goal is to make the specification of derived rules as easy as possible. For more on derived rules, see [`DERIVEDRULES.md`](DERIVEDRULES.md).

<!-- [^1]: To pursue this goal fully is arguably impossible. If you're not operating _completely_ in the formal system, you're relying on some amount of abductive reasoning for you and your proof's reader to reach a common understanding of what you are saying in your proof (which is why we tolerate such vague justifications), just as in informal, everyday communication. Since precision is highly valued in math and logic, these abductive reasoning paths in proofs are often very close to definable procedures. For example, "K reasoning" usually means pushing boxes or diamonds through a formula, but it doesn't _necessarily_ mean that. I have a derived rule in sponge for recursively pushing boxes through a formula, and I call that derived rule "K reasoning", but I'm not claiming that every time someone would write "by K reasoning" on a paper proof they mean they're pushing boxes through a formula (unlike other derived rules, like modus tollens, which do have a settled meaning that doesn't need to be gotten to via abductive reasoning on every use on a paper proof). -->

On the third point, oftentimes with modal logics (and axiomatic systems generally) it's nice to be able to define one system as a simple extension of another. As a result, the logics for this proof checker should be defined modularly to reflect that and make adding logics as easy as possible. For example, K is defined as classical logic + the K axiom and necessitation; classical logic is defined as intuitionistic logic + excluded middle; and intuitionistic logic is defined as minimal logic + explosion. 

For details on the architecture and design choices (and some neat optimizations), see [`ARCHITECTURE.md`](ARCHITECTURE.md). For stuff on derived rules (a big part of what makes sponge nice I think), see [`DERIVEDRULES.md`](DERIVEDRULES.md). 

## Using sponge
The project needs the following things:
1. Souffle Datalog
2. Haskell
3. Make

For now, clone this repository, run `make all` in the main directory, and then write proofs in the `user_proofs` directory as `.txt` files. See [`PROOFS.md`](PROOFS.md) for some details on the required syntax of proof files. To check a proof, run `make check-proof LOGIC_NAME PROOF_NAME` from the main directory, where `PROOF_NAME` is the name of the `.txt` file for your proof (without `.txt`) and `LOGIC_NAME` is the name of the logic you are using (the folder your proof file is in within [`user_proofs`](user_proofs)).  You can see the operators/axioms/inference rules of a logic with `make show-logic LOGIC_NAME` (also ran from the main directory). 

<!-- ### The idea is motivated by a few desires: 
- I really like doing axiomatic proofs of propositional systems, especially modal logics (just because there's more going on than the duller Hilbert-style systems for intuitionistic and classical propositional logic), so I want a centralized place where I can keep track of all the proofs I've done so I can reuse them (this is especially relevant when logics are contained within each other, like in modal logic). Paper is only contingently centralized. Something on a computer less so. 
- Since I really like axiomatic proofs, I want the tool to feel as similar as possible to writing axiomatic proofs on paper. 
- Computer proofs can be nice over paper proofs in that you can easily go down a rabbit hole in a proof to see if it works, and if it doesn't it's just a matter of deleting a few lines or tweaking some things here and there.
- While axiomatic proofs canonically use forward reasoning, it's helpful to sometimes try out a few lines of backwards reasoning. A system that easily allows that and allows one to keep track of both ends would be nice. I'm not sure if I'll be able to incorporate backwards reasoning, but it's a goal.  -->
