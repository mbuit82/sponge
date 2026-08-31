Create HintDb judgement_db.
Create HintDb mp_db. 

Inductive Sentence : Set :=
| Snt (n : nat)
| Arrow (s : Sentence) (s : Sentence)
| Or (s : Sentence) (s : Sentence)
| And (s : Sentence) (s :Sentence)
| Bot.

Notation "a <--> b" := (And (Arrow a b) (Arrow b a)) (at level 61, right associativity).
Infix "-->" := Arrow (at level 60, right associativity).
Infix "&" := And (at level 59, right associativity).
Infix "v" := Or (at level 58, right associativity). 
Notation "~~ a" := (Arrow a Bot) (at level 57, right associativity).


Inductive J_Supp : Sentence -> Prop :=
| supposition : forall p, J_Supp p.

Definition Modus_Ponens (P : Sentence -> Prop) : Prop :=
  forall p q, P p -> P (p --> q) -> P q.
Hint Unfold Modus_Ponens : mp_db. 

(* start with intuitionistic calculus *)
Inductive J_IPC : Sentence -> Prop :=
| Axiom2 : forall p q, J_IPC (p --> (q --> p))
| Axiom3 : forall p q r, J_IPC ((p --> q) --> ((p --> (q --> r)) --> (p --> r)))
| AndIntro : forall p q, J_IPC (p --> q --> (p & q))
| AndL : forall p q, J_IPC ((p & q) --> p)
| AndR : forall p q, J_IPC ((p & q) --> q)
| OrL : forall p q, J_IPC (p --> (p v q))
| OrR : forall p q, J_IPC (q --> (p v q))
| OrElim : forall p q r, J_IPC ((p --> r) --> (q --> r) --> (p v q) --> r)
| ExFalso : forall p, J_IPC (Bot --> p)
| MP_IPC : forall p q, J_IPC p -> J_IPC (p --> q) -> J_IPC q
| Supp : forall p, J_Supp p -> J_IPC p.

Hint Resolve MP_IPC : mp_db. 

Axiom modus_ponens_monotone :
  forall P P', Modus_Ponens P -> (forall s, P s -> P' s) -> Modus_Ponens P'.
Hint Resolve modus_ponens_monotone : mp_db. 

Ltac write line_number judgement justification :=
  assert (line_number : judgement) by (eauto using justification with judgement_db).

Ltac evident := assumption.

Theorem Axiom1 : forall p, J_IPC (p --> p).
Proof.
  intros.
  write L1 (J_IPC ((p --> (p --> p)) --> ((p --> ((p --> p) --> p)) --> (p --> p)))) Axiom3.
  write L2 (J_IPC (p --> p --> p)) Axiom2.
  write L3 (J_IPC ((p --> ((p --> p) --> p)) --> (p --> p))) (MP_IPC _ _ L2 L1).
  write L4 (J_IPC (p --> ((p --> p) --> p))) Axiom2.
  write L5 (J_IPC (p --> p)) (MP_IPC _ _ L4 L3).
  evident.
Qed.

Theorem Bot_contradiction : forall p, J_IPC (Bot <--> p & ~~ p).
Proof.
  intros.
  write L1 (J_IPC ((Bot --> p & ~~p) --> (p & ~~ p --> Bot) --> (Bot --> p & ~~p) & (p & ~~ p --> Bot))) AndIntro.
  write L2 (J_IPC (Bot --> p & ~~ p)) ExFalso.
  write L3 (J_IPC ((p & ~~ p --> Bot) --> (Bot --> p & ~~p) & (p & ~~ p --> Bot))) (MP_IPC _ _ L2 L1).
  write L4 (J_IPC ((p & ~~ p --> p) --> (p & ~~ p --> (p & ~~ p --> p)))) Axiom2.
  write L5 (J_IPC (p & ~~ p --> p)) AndL.
  write L6 (J_IPC (p & ~~ p --> (p & ~~ p --> p))) (MP_IPC _ _ L5 L4).
  write L7 (J_IPC ((p & ~~ p --> ~~ p) --> (p & ~~ p --> (p & ~~ p --> ~~ p)))) Axiom2.
  write L8 (J_IPC (p & ~~ p --> ~~ p)) AndR.
  write L9 (J_IPC (p & ~~ p --> (p & ~~ p --> ~~ p))) (MP_IPC _ _ L8 L7).
  write L10 (J_IPC ((p & ~~ p --> p) --> (p & ~~ p --> ~~ p) --> (p & ~~ p --> Bot))) Axiom3.
  write L11 (J_IPC ((p & ~~ p --> ~~ p) --> (p & ~~ p --> Bot))) (MP_IPC _ _ L5 L10).
  write L12 (J_IPC (p & ~~ p --> Bot)) (MP_IPC _ _ L8 L11).
  write L13 (J_IPC (Bot <--> p & ~~ p)) (MP_IPC _ _ L12 L3).
  evident.
Qed.



  

Theorem and_comm : forall p q, J_IPC (p & q <--> q & p).
Proof.
  Print J_IPC.  
  
Admitted.


Theorem Axiom4 : forall p q, J_IPC ((p --> Bot) --> p --> q).
Proof.
  intros.
  write L1 (J_IPC (~~ p --> p --> ~~ p & p)) AndIntro.
Admitted.

(* Theorem uncurrying : forall p q r, J_IPC ((p --> q --> r) --> (p & q --> r)). *)
(* Proof. *)
(*   intros. *)
  

(* Theorem currying : forall p q r, J_IPC ((p & q --> r) --> (p --> q --> r)). *)
(* Proof. *)
(*   intros. *)

(* NOTE: not meant for general usage. Just to make the Deduction_Lemma proof go through. *)
Ltac deduction_lemma_case axiom_content axiom_cons J_Pred L1 L2 L3 a :=
  write L1 (J_Pred (axiom_content --> (a --> axiom_content))) Axiom2;
  write L2 (J_Pred axiom_content) axiom_cons;
  write L3 (J_Pred (a --> axiom_content)) (MP_IPC _ _ L2 L1);
  evident.

Theorem IPC_deduction : forall a b, (J_Supp a -> J_IPC b) <-> J_IPC (a --> b).
Proof.
  intros a b.
  apply conj.
  - intros.
    induction H. 
    + deduction_lemma_case (p --> q --> p) Axiom2 J_IPC L1 L2 L3 a.
    + deduction_lemma_case ((p --> q) --> ((p --> (q --> r)) --> (p --> r))) Axiom3 J_IPC L1 L2 L3 a.
    + deduction_lemma_case (p --> q --> (p & q)) AndIntro J_IPC L1 L2 L3 a.
    + deduction_lemma_case ((p & q) --> p) AndL J_IPC L1 L2 L3 a.
    + deduction_lemma_case ((p & q) --> q) AndR J_IPC L1 L2 L3 a.
    + deduction_lemma_case (p --> (p v q)) OrL J_IPC L1 L2 L3 a.
    + deduction_lemma_case (q --> (p v q)) OrR J_IPC L1 L2 L3 a.
    + deduction_lemma_case ((p --> r) --> (q --> r) --> (p v q) --> r) OrElim J_IPC L1 L2 L3 a.
    + deduction_lemma_case (Bot --> p) ExFalso J_IPC L1 L2 L3 a.
    + write L1 (J_IPC q) (MP_IPC _ _ j1 j2).
      write L2 (J_IPC (q --> a --> q)) Axiom2.
      write L3 (J_IPC (a --> q)) (MP_IPC _ _ L1 L2).
      evident.
    + apply Supp in H.
      write L1 (J_IPC (p --> a --> p)) Axiom2.
      write L2 (J_IPC (a --> p)) (MP_IPC _ _ H L1).
      evident.
    + apply supposition.
  - intros L1 L2.
    apply Supp in L2.
    write L3 (J_IPC b) (MP_IPC _ _ L2 L1).
    evident.
Qed.

Theorem Deduction_Lemma_gen : forall a b P, (forall x, J_IPC x -> P x) -> (J_Supp a -> P b) <-> P (a --> b).
Proof.
Abort.

(* deduction is the deduction lemma for whatever system you're using *)
Ltac use deduction line_number := apply deduction; intros line_number; apply Supp in line_number.

Theorem double_negation_intro : forall p, J_IPC (p --> ~~ ~~ p).
Proof.
  intros.
  use IPC_deduction L1.
  use IPC_deduction L2.
  write L3 (J_IPC Bot) (MP_IPC _ _ L1 L2).
  evident.
Qed.

Theorem switch_func_args_3_deductions : forall p q r, J_IPC ((p --> q --> r) --> (q --> p --> r)).
Proof.
  intros.
  use IPC_deduction L1.
  use IPC_deduction L2.
  use IPC_deduction L3.
  write L4 (J_IPC (q --> r)) (MP_IPC _ _ L3 L1).
  write L5 (J_IPC r) (MP_IPC _ _ L2 L4).
  evident.
Qed.

Theorem switch_func_args_2_deductions : forall p q r, J_IPC ((p --> q --> r) --> (q --> p --> r)).
Proof.
  intros.
  use IPC_deduction L1.
  use IPC_deduction L2.
  write L3 (J_IPC (q --> p --> q)) Axiom2.
  write L4 (J_IPC (p --> q)) (MP_IPC _ _ L2 L3).
  write L5 (J_IPC ((p --> q) --> (p --> q --> r) --> (p --> r))) Axiom3.
  write L6 (J_IPC ((p --> q --> r) --> (p --> r))) (MP_IPC _ _ L4 L5).
  write L7 (J_IPC (p --> r)) (MP_IPC _ _ L1 L6).
  evident.
Qed.

Theorem switch_func_args_1_deduction : forall p q r, J_IPC ((p --> q --> r) --> (q --> p --> r)).
Proof.
  intros.
  use IPC_deduction L1.
  write L2 (J_IPC (q --> q)) Axiom1.
  write L3 (J_IPC ((q --> p --> q) --> q --> (q --> p --> q))) Axiom2.
  write L4 (J_IPC (q --> p --> q)) Axiom2.
  write L5 (J_IPC (q --> q --> p --> q)) (MP_IPC _ _ L4 L3).
  
  
  Print J_IPC.
  write L2 (J_IPC ((q --> (p --> q --> r)) --> (q --> (p --> q --> r) --> (p --> r)) --> (q --> p --> r))) Axiom3.
  write L3 (J_IPC ((p --> q --> r) --> q --> (p --> q --> r))) Axiom2.
  write L4 (J_IPC (q --> (p --> q --> r))) (MP_IPC _ _ L1 L3).
  write L5 (J_IPC ((q --> (p --> q --> r) --> p --> r) --> q --> p --> r)) (MP_IPC _ _ L4 L2).
  

  
  write L1 (J_IPC ((p --> q --> r) --> (p --> q --> r))) Axiom1.
  write L2 (J_IPC (p --> p)) Axiom1.
  write L3 (J_IPC (q --> q)) Axiom1.
  Print J_IPC. 
  
  write L1 (J_IPC ((p --> q --> r) --> (q --> (p --> q --> r)))) Axiom2.
  write L2 (J_IPC 
  Print J_IPC.
  (* (((p --> q --> r) --> Q) --> ((p --> q --> r) --> Q --> (q --> p --> r)) --> (p --> q --> r) --> (q --> p --> r)) *)
            Admitted.

            (* what if you make deduction not extensible? Like, by design. I never once used deduction in my modal logic homework. That't not what I want my system to be for. But it sure as hell is nice for getting things set up nicely. The sort of thinking that deduction is doesn't really seem as common for modal logic proofs. *)

            (* the funny thing is, I do want substitution of logical identicals lmfao. And that would actually go through super easily in practice by deduction.
               what am I even doing this for? Like, that's not clear to me. Not the meta-level why, I got that. The object-level why of what sort of proofs I want to be doing, what sort of reasoning I'm trying to isolate.

               I think the ideal version of the tool lets the user choose whether glossy reasoning is allowed for a certain proof. Wow, this is hard. What should it take to turn glossy reasoning on? Damn, this is hard lmfao. Design choices. 
             *)

Theorem triple_negation_elim : forall p, J_IPC (~~ ~~ ~~ p --> ~~ p).
Proof.
  intros.
  use IPC_deduction L1.
  use IPC_deduction L2.
  write L3 (J_IPC ((~~ ~~ p --> Bot) --> (~~ ~~ p --> ~~ p))) Axiom4.
  write L4 (J_IPC (~~ ~~ p --> ~~ p)) (MP_IPC _ _ L1 L3).
  write L5 (J_IPC (p --> ~~ ~~ p)) double_negation_intro. (* AWESOME! you can use proved theorems! *)
  write L6 (J_IPC
              ~~ ~~ p) (MP_IPC _ _ L2 L5).
  write L7 (J_IPC ~~ p) (MP_IPC _ _ L6 L4).
  write L8 (J_IPC Bot) (MP_IPC _ _ L2 L7).
  evident.
Qed.

Inductive J_CPC : Sentence -> Prop :=
| IPC_in_CPC : forall p, J_IPC p -> J_CPC p
| Axiom5 : forall p, J_CPC (~~ ~~ p --> p). (* consider changing this name *)
Hint Resolve IPC_in_CPC : judgement_db.
Hint Resolve IPC_in_CPC : mp_db.

Theorem MP_CPC : Modus_Ponens J_CPC.
Proof. apply (modus_ponens_monotone J_IPC); eauto with mp_db. Qed.

Definition MP_CPC_proof_term := modus_ponens_monotone J_IPC J_CPC MP_IPC.
Compute MP_CPC_proof_term. 

Theorem classical_deduction : forall a b, (J_Supp a -> J_CPC b) <-> J_CPC (a --> b).
Proof.
  intros.
  apply conj.
  - intros.
    induction H.
    + apply IPC_in_CPC. apply IPC_deduction. intros. apply H.
    + write L1 (J_CPC ((~~ ~~ p --> p) --> (a --> (~~ ~~ p --> p)))) Axiom2;
        write L2 (J_CPC (~~ ~~ p --> p)) Axiom5.
      write L3 (J_CPC (a --> (~~ ~~ p --> p))) (MP_CPC _ _ L2 L1).
      evident. 
    + apply supposition.
  - intros. apply Supp in H0.
    apply IPC_in_CPC in H0. 
    write L3 (J_CPC b) (MP_CPC _ _ H0 H).
    evident.
Qed.

Theorem ex_falso_quodlibet_classical : forall p, J_CPC (Bot --> p).
Proof. (* I'll do the proof that doesn't use axiom 4! *)
  intros.
  use classical_deduction L1; apply IPC_in_CPC in L1. (* deduction is still not completely fixed *)
  write L2 (J_CPC (Bot --> (~~ p --> Bot))) Axiom2.
  write L3 (J_CPC (~~ ~~ p)) (MP_CPC _ _ L1 L2).
  write L4 (J_CPC (~~ ~~ p --> p)) Axiom5.
  write L5 (J_CPC p) (MP_CPC _ _ L3 L4).
  evident. 
Qed.

Theorem axiom4_classically_redundant : forall p q, J_CPC ((p --> Bot) --> (p --> q)).
Proof.
  intros.
  use classical_deduction L1; apply IPC_in_CPC in L1.
  use classical_deduction L2; apply IPC_in_CPC in L2.
  write L3 (J_CPC Bot) (MP_CPC _ _ L2 L1).
  write L4 (J_CPC (Bot --> q)) ex_falso_quodlibet_classical.
  write L5 (J_CPC q) (MP_CPC _ _ L3 L4).
  evident.
Qed.

(* TODO: extensions. I think extension with modus ponens is going to be a bitch. *)
(* No: the real bitch is going to be extending the definition of sentences! *)
(* Actually what Ima do is make a new file w Heyting's axiomatization, and then have the definition of sentences include Box and Diamond. and then just not use those till I get extensions with modal logic lol. Kinda just to have the fullest and most usable version that's completely Rocq, and actually get to writing modal logic proofs. Just kinda to see where these design decisions take me--after all, part of the point of this is learning about making something from the ground up. *)

