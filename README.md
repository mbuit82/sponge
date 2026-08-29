# axiomatic_proofs_in_rocq
A tool for writing axiomatic proofs of propositional systems. Starting with the intuitionistic and classical logic, goal is to add modal systems.

### The idea is motivated by a few desires: 
- I really like doing axiomatic proofs of propositional systems, especially modal logics (just because there's more going on than the duller Hilbert-style systems for intuitionistic and classical propositional logic), so I want a centralized place where I can keep track of all the proofs I've done so I can reuse them (this is especially relevant when logics are contained within each other, like in modal logic).
- Since I really like axiomatic proofs, I want the tool to feel as similar as possible to writing axiomatic proofs on paper. 
- Rocq proofs are nice over paper proofs in that you can easily go down a rabbit hole in a proof to see if it works, and if it doesn't it's just a matter of deleting a few lines or tweaking some things here and there.
- While axiomatic proofs canonically use forward reasoning, it's helpful to sometimes try out a few lines of backwards reasoning. A system that easily allows that and allows one to keep track of both ends would be nice. Rocq proofs can do that (though of course the kosher thing to do is backward reasoning, so maybe an indication that it isn't the _best_ possible tool out there for this lol). 
