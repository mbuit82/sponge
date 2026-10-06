# sponge
A modular proof checker for propositional axiomatic systems with (eventually, not right now) abstraction so that the proofs are fun and you can cite other proofs and deduction lemma etc and it's not just to-the-letter-of-the-axioms Hilbert-style hell. The hope is to focus on modal systems but it really doesn't matter—the point is to use it not to do tedious Hilbert-style proofs in ugly axiomatizations, but rather fun proofs where we can abstract that tediousness away (even if deep down we are defining our logics using not so pretty axiomatizations). 

10/6 update: deduction lemma now works. Next step is a front end, from which I can do the citing other proofs thing. 

### The idea is motivated by a few desires: 
- I really like doing axiomatic proofs of propositional systems, especially modal logics (just because there's more going on than the duller Hilbert-style systems for intuitionistic and classical propositional logic), so I want a centralized place where I can keep track of all the proofs I've done so I can reuse them (this is especially relevant when logics are contained within each other, like in modal logic). Paper is only contingently centralized. Something on a computer less so. 
- Since I really like axiomatic proofs, I want the tool to feel as similar as possible to writing axiomatic proofs on paper. 
- Computer proofs can be nice over paper proofs in that you can easily go down a rabbit hole in a proof to see if it works, and if it doesn't it's just a matter of deleting a few lines or tweaking some things here and there.
- While axiomatic proofs canonically use forward reasoning, it's helpful to sometimes try out a few lines of backwards reasoning. A system that easily allows that and allows one to keep track of both ends would be nice. I'm not sure if I'll be able to incorporate backwards reasoning, but it's a goal. 

Right now don't have a front end (will probably do that rather late) but will eventually get to that lol
