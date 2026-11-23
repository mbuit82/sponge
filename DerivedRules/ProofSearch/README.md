# Proof Search

## Overview
Proof search is semidecidable in axiomatic systems. This is not good enough. However, it is decidable in sequent systems, and there are simple and effective decision procedures for sequent systems (e.g. G4ip), and (crucially) you can translate sequent proofs to axiomatic proofs (meaning I don't have to give up the "everything is checked in Datalog" aspect of sponge). 

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
Nearly all cases take advantage of what is essentially partial evaluation via derivation composition. 
Negation is the only place there's interesting discussion (beyond the partial evaluation). 

### Negation
Here the choice of negation axioms picked finally becomes relevant. 
Picking `~P -> (P -> Q)` (called `Negation Elim` in the code) allows for easy compiler cases of `L~1`, `L~4`, and `L~5`. 
The choice of negation introduction axiom is a little harder. `(P -> Q) -> ((P -> ~Q) -> ~P)` (`Negation Intro` in the code) mirrors the (intuitionistic) ND rule for negation, so is a cohesive choice, given the rest of the axiomatization. 
However, it results in a compiler case for `R~` that does not use the recursive case, instead searching in the current antecedent `Gamma` of the sequent for a sentence `X` such that `Gamma, A => X` and `Gamma, A => ~X`. 
Such a pair of sequents are guaranteed to exist, particularly (and rather trivially) with `X := A`. 

This means that, in the general case, the nonconstructive proof search reduces to `reductio` (`(P -> ~P) -> ~P`), since the proof search case above expressed as a sequent rule (`Gamma, A => ~A / Gamma => ~A`) is just the axiom of `reductio` (the other case, the positive case, is trivial). Using this case always actually removes the need for the nonrecursive proof search in the `Negation Elim` solution. The sequent rule just above is also completely valid, and trivially invertible, so we're all good on those sides of things. It would, however, require looping in the proof search, getting rid of the beauty of G4ip. We can get around this by replacing `~A` in the premise with a placeholder `NotA` that at compile time we replace with `~A`. This is what happens in the code now. The compiler case also cites the (rather short) proof of `reductio` from `Negation Intro`, instead of citing `Negation Intro` directly. 

I've left `Negation Intro` as the negation axiom for intuitionistic logic because it gives some pretty short derivations for commonly used derived rules/theorems like contraposition, and the derivation from `Negation Intro` to `reductio` is rather short (7 datalog lines). Would be interesting to more rigorously check advantages/disadvantages of using one or the other by seeing if `reductio` has short proofs of e.g. contraposition. 