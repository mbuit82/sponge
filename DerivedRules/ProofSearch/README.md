# Proof Search

### Overview
Proof search is semidecidable in axiomatic systems. This is not good enough. Fortunately, it is decidable in sequent systems, and there are particularly effective decision procedures for sequent systems (e.g. G4ip), and (most importantly) you can translate sequent proofs to axiomatic proofs (meaning I don't have to give up the "everything is checked in Datalog" aspect of sponge). So this feature is proof search in G4ip, together with a compiler from sequent proofs in G4ip to axiomatic systems (to the ND-esque axiomatization with primitive negation I have). 

### Status
This is still under construction, but you can now search for theorems of minimal logic (modulo substitution of operators). As soon as I get the compiler cases for negation, it will extend to intuitionistic logic (and classical logic, by double negation translation and DNE). 


### Details
The proof search happens in a system that is a variant of G4ip as seen in [Troelstra and Schwichtenberg's book](https://www.cambridge.org/core/books/basic-proof-theory/928508F797214A017D245A1FB67CCCD9) (page 113 ish) and also [Dyckhoff's original formulation](https://www.cs.cmu.edu/~fp/courses/15317-f08/cmuonly/dyckhoff92.pdf), except that negation is primitive. The reason negation is primitive is because my axiomatic system has negation as primitive, and the axiomatic system has negation as primitive because it makes some classical derived rules smoother for modal operators (since Diamond := Not Box Not, which with Bot would be (Box(A -> Bot) -> Bot); this makes accessing A very hard for e.g. strengthening, which is a desirable derived rule to be able to use in modal axiomatic proofs). 

Some other design choices for the sequent system that differ from the aforementioned sources:
- The axiom rule is for all sentences, not just propositional sentences. This is admissible in G4ip, so is ok. 
- L0-> (or L1-> in Dyckhoff's terminology, which I use in the code) is for all sentences, not just propositional sentences. This is also admissible, and the reason Dyckhoff restricts it to atomic sentences is that it make the system nice in that every operator has its own L-> rule. 
- L->4 (or L->->, Troelstra's name for it) has `C` in the (conditional) antecedent of the succedent, not in the (sequent) antecedent. This makes the compiler nicer. The Troelstra rule, L->->, is immediately derivable by applying R-> to the first premise of Dyckhoff's L->4. 
