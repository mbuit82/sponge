# Proof Search

## Overview
Proof search is semidecidable in axiomatic systems. This is not good enough. However, it is decidable in sequent systems, and there are particularly effective decision procedures for sequent systems (e.g. G4ip), and (crucially) you can translate sequent proofs to axiomatic proofs (meaning I don't have to give up the "everything is checked in Datalog" aspect of sponge). 

So this feature is proof search in a version of G4ip, together with a compiler from sequent proofs in G4ip to axiomatic systems (to the ND-esque axiomatization with primitive negation that is currently the base of nearly all the logics that have theorems proved for them in sponge right now). 

We can get classical results by first checking if a theorem is an intuitionistic theorem. If it is, we compile that proof. If it isn't, we look for a proof of the sentence under double negation, and then apply DNE at the end of the proof. (I think any more efficient choice would be to come up with a classical sequent calculus proofsearch procedure, which maybe would not have been a bad idea, and was potentially a good idea in case I wanted to extend proofsearch to classical Kor classical S4.)

The proofsearch also works for sentences with nonclassical operators, so long as the result actually does follow classically. This is accomplished by replacing all rules in G4ip that have the propositional restriction with versions without that restriction. This is admissible, so it is ok. More details on deviations from G4ip below. 

## Details on the logic used in the proof search
The proof search happens in a system that is a variant of G4ip as seen in [Troelstra and Schwichtenberg's book](https://www.cambridge.org/core/books/basic-proof-theory/928508F797214A017D245A1FB67CCCD9) (page 113 ish) and also [Dyckhoff's original formulation](https://www.cs.cmu.edu/~fp/courses/15317-f08/cmuonly/dyckhoff92.pdf), except that negation is primitive. The reason negation is primitive is because my axiomatic system has negation as primitive, and the axiomatic system has negation as primitive because it makes some classical derived rules smoother for modal operators (since Diamond := Not Box Not, which with Bot would be (Box(A -> Bot) -> Bot); this makes accessing A very hard for e.g. strengthening, which is a desirable derived rule to be able to use in modal axiomatic proofs). 

Some other design choices for the sequent system that differ from the aforementioned sources:
- The axiom rule is for all sentences, not just propositional sentences. This is admissible in G4ip, so is ok. This change is necessary to look for proofs of sentences like e.g. `((LA & (LA -> LB)) -> LB)`. 
- L0-> (or L1-> in Dyckhoff's terminology, which I use in the code) is for all sentences, not just propositional sentences. This is also admissible, and the reason Dyckhoff restricts it to atomic sentences is that it make the system nice in that every operator has its own L-> rule. It is necessary in this system for the same reason. 
- L->4 (or L->->, Troelstra's name for it) has `C` in the (conditional) antecedent of the succedent, not in the (sequent) antecedent. This makes the compiler nicer. The Troelstra rule, L->->, is immediately derivable by applying R-> to the first premise of Dyckhoff's L->4. 

## Details on the compiler
The compiler is rather straight forward, and takes advantage of the ND-style axiomatization that has been used for minimal/intuitionistic/classical logic so far. 

Here the choice of negation axioms picked finally becomes relevant. 
Picking `~P -> (P -> Q)` (called `Negation Elim` in the code) allows for easy compiler cases of `L~1`, `L~4`, and `L~5`. 
The choice of negation introduction axiom is a little harder. `(P -> Q) -> ((P -> ~Q) -> ~P)` (`Negation Intro` in the code) mirrors the (intuitionistic) ND rule for negation, so is a cohesive choice, given the rest of the axiomatization. 
However, it results in a compiler case for `R~` that does not use the recursive case, instead searching in the current antecedent `Gamma` of the sequent for a sentence `X` such that `Gamma, A => X` and `Gamma, A => ~X`. (I'm not sure how I'd even use the recursive case anyways, since it has an empty succedent.) 
Another option is to use `(P -> ~P) -> ~P`, called `reductio` in the code. This would actually be nicer, since it would result in only one nonconstructive case. However, the proof from `Negation Intro` to `reductio` is quite immediate (7 lines in datalog), so I am not convinced it would be best to use it as an axiom if in other cases `Negation Intro` results in shorter proofs than `reductio`. (The two are equivalent though, using minimal logic and `Negation Elim` as a base.)

Ultimately the choice of second negation axiom depends not only on what makes this compiler case nice but also what makes other often-used proofs, like contraposition, short. 

I have tested this case extensively in the `Tests.hs` file in the `DerivedRules/ProofSearch` directory, and I am pretty sure it is sound (though I have not formally verified it). 
