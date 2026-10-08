# sponge
A modular proof checker for propositional axiomatic systems supporting abstractions like deduction, (eventually) derived rules, and (eventually) citing other proofs. (A separate ambition is to define translations between logics as well.)

### The project has (at least?) three guiding ideas: 
- The user should input proofs as close to as they would on paper.
- The user should be able to abstract parts of a system that they are not focused on away. 
- The specification of the logics should reflect their modular nature. 

On the first point, the idea is the tool should be easy to use for anyone_ who wants to learn axiomatic proofs or practice them or do them for fun, _regardless_ of their technical background. Since axiomatic proofs are usually taught on paper (or mathematical notation—the point is not code), having the input resemble how the user would write proofs on paper makes the learning curve for the tool as smooth as possible. Right now, proofs are fully in .txt files, but specifications and adding derived rules/abstractions involves getting into the Haskell code, which is less optimal. (The reason I've left the specifications in Haskell is that I found myself thinking that the Haskell data structure for specifying logics isn't all that opaque, and any other way of defining them would be only marginally less opaque.)

On the second point, if you follow an axiomatic system to the foot of the letter then you have to justify _every_ line with an axiom or an inference rule. This doesn't correspond with how axiomatic proofs are done for systems where the user only cares about the reasoning relative to a fragment of the language, like in axiomatic proofs in modal logics. Consequently, the idea is to let the user be able to abstract rote sequences of axioms and inference rules, with e.g. derived rules, citing previous results, etc. 

On the third point, oftentimes with modal logics (and axiomatic systems generally) it's nice to be able to define one system as a simple extension of another. As a result, the logics for this proof checker should be defined modularly to reflect that and make adding logics as easy as possible. For example, K is defined as classical logic + the K axiom and necessitation; classical logic is defined as intuitionistic logic + LEM; and intuitionistic logic is defined as minimal logic + explosion. 

## Using sponge
The project needs the following things:
1. Souffle Datalog
2. Haskell
3. Make

For now, clone this repository, run `make all` in the main directory, and then write proofs in the `hand_proofs` directory as text files. See [PROOFS.md](PROOFS.md) fod details on the required syntax of proof files. To check a proof, run `make check-proof LOGIC_NAME PROOF_NAME` from the main directory, where `LOGIC_NAME` is the name of the logic you are using (the folder your proof is in) and `PROOF_NAME` is the name of the file your proof is in (without `.txt`).  

<!-- ### The idea is motivated by a few desires: 
- I really like doing axiomatic proofs of propositional systems, especially modal logics (just because there's more going on than the duller Hilbert-style systems for intuitionistic and classical propositional logic), so I want a centralized place where I can keep track of all the proofs I've done so I can reuse them (this is especially relevant when logics are contained within each other, like in modal logic). Paper is only contingently centralized. Something on a computer less so. 
- Since I really like axiomatic proofs, I want the tool to feel as similar as possible to writing axiomatic proofs on paper. 
- Computer proofs can be nice over paper proofs in that you can easily go down a rabbit hole in a proof to see if it works, and if it doesn't it's just a matter of deleting a few lines or tweaking some things here and there.
- While axiomatic proofs canonically use forward reasoning, it's helpful to sometimes try out a few lines of backwards reasoning. A system that easily allows that and allows one to keep track of both ends would be nice. I'm not sure if I'll be able to incorporate backwards reasoning, but it's a goal.  -->
