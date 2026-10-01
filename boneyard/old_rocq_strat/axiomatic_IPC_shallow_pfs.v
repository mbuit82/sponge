Create HintDb judgement_db.
Create HintDb mp_db. 

(* we'll start with a simple axiomatic propositional calculus for now *)
(* bezhanishvili has a Hilbert-style system w /\ and \/ in chapter 3 of his book on intuitionistic logic--if later you determine that having those as primitive would be better *)
Inductive Sentence : Set :=
| Snt (n : nat)
| Arrow (s : Sentence) (s : Sentence)
| Bot.

Infix "-->" := Arrow (at level 60, right associativity).
Notation "~~ a" := (Arrow a Bot) (at level 59, right associativity).

(* this was a way to get around the deduction lemma with current setup *)
(* I think this is the best way to do it, because you should never suppose in the middle of a proof in an axiomatic proof, so the trivial case where you just prove the statement by supposition is taken care of in that yeah you're allowed to do that but it's clearly contrary to the intention *)
(* To do this with natural deduction would be a different story, you'd want to encode levels of supposition. *)
(* I think the best way to frame the tool that emerges from this approach is one that's complete (rather trivially), but not sound; however, under a certain usage of it (viz never asserting J_Supp in a proof), it is also sound. *)
Inductive J_Supp : Sentence -> Prop :=
| supposition : forall p, J_Supp p.
(* If you just treat Rocq's Prop type as things that you _can_ say, well then yes, you _can just suppose_ any sentence. You can also _say_ any sentence is derivable. What you need though is evidence for that judgement. In other words, here you're treating Prop as the type of judgements. Given how M-L says mathematicians use the word "proposition", that might actually be exactly the right thing to do. Or maybe I'm just coping lol *)

Definition Modus_Ponens (P : Sentence -> Prop) : Prop :=
  forall p q, P p -> P (p --> q) -> P q.
Hint Unfold Modus_Ponens : mp_db. 

(* we start with the smallest system we (currently anticipate we will) use: intuitionistic propositional calculus. *)
(* really, we probably won't use it, but it serves as a test case for extension. *)
Inductive J_IPC : Sentence -> Prop :=
| Axiom1 : forall p,  J_IPC (p --> p)
| Axiom2 : forall p q, J_IPC (q --> (p --> q))
| Axiom3 : forall p q r, J_IPC ((p --> q) --> ((p --> (q --> r)) --> (p --> r)))
| Axiom4 : forall p q, J_IPC ((p --> Bot) --> (p --> q))
| MP_IPC : forall p q, J_IPC p -> J_IPC (p --> q) -> J_IPC q
| Supp : forall p, J_Supp p -> J_IPC p.
Hint Resolve MP_IPC : mp_db. 

Axiom modus_ponens_monotone :
  forall P P', Modus_Ponens P -> (forall s, P s -> P' s) -> Modus_Ponens P'.
Hint Resolve modus_ponens_monotone : mp_db. 

Theorem ex_falso_quodlibet : forall p, J_IPC (Bot --> p).
Proof.
  intros.
  assert (J_IPC ((Bot --> Bot) --> (Bot --> p))) by (apply Axiom4).
  assert (J_IPC (Bot --> Bot)) by (apply Axiom1).
  assert (J_IPC (Bot --> p)) by (apply (MP_IPC _ _ H0 H)).
  apply H1.
Qed.
(* a bit clunky lol *)

(* I'll just redefine |- later, doing this just for ease now *)
Notation "|- a" := (J_IPC a) (at level 61, no associativity). (* does associativity matter for unary operators? *)

Ltac write_old line_number judgement justification :=
  assert (line_number : judgement) by (apply justification).

Ltac write line_number judgement justification :=
  assert (line_number : judgement) by (eauto using justification with judgement_db). 

Ltac evident := assumption.

Theorem ex_falso_quodlibet_2 : forall p, |- Bot --> p.
Proof.
  intros. 
  write L1 (|- ((Bot --> Bot) --> (Bot --> p))) Axiom4.
  write L2 (|- (Bot --> Bot)) Axiom1.
  write L3 (|- (Bot --> p)) (MP_IPC _ _ L2 L1).
  evident.
Qed.
(* better, ideally I get rid of the f? I'm not clear on whether we should lol *)
(* if we phrase f as the act of writing (now named write), it's just the externalization of a judgement. Which makes sense: the inner act of judging has already occurred, putting it on paper is nothing but externalizing it. *)

(* NOTE: not meant for general usage. Just to make the Deduction_Lemma proof go through. *)
Ltac deduction_lemma_case axiom_content axiom_cons J_Pred L1 L2 L3 a :=
  write L1 (J_Pred (axiom_content --> (a --> axiom_content))) Axiom2;
  write L2 (J_Pred axiom_content) axiom_cons;
  write L3 (J_Pred (a --> axiom_content)) (MP_IPC _ _ L2 L1);
  evident.

(* this is a limited form of deduction lemma: can only do one supposition *)
(* well actually I don't think it's limited in any other sense. I mean, it's a biconditional. *)
(* and below we have a proof where we do it twice *)
(* note from when I thought this approach was a bad idea: I think the reason the deduction lemma had to have this honestly pretty ad hoc fix was that the proof of the deduction lemma that you have in mind is within a system where the proofs themselves are defined objects that can be looked into in a particular way. Here, proofs are at the meta-level, they're in Ltac, so we can't really talk about them in Gallina, much less look at specific lines (because there is no notion of a line in a Gallina proof term). I'm going to call this way of doing things a shallow embedding of proofs. I think we need a deep embedding of proofs. *)
(* I'm not sure anymore. I think this idea is defendable. So far it's gotten the job done! *)
Theorem IPC_deduction : forall a b, (J_Supp a -> J_IPC b) <-> J_IPC (a --> b).
Proof.
  intros a b.
  apply conj.
  - intros.
    induction H. 
    + deduction_lemma_case (p --> p) Axiom1 J_IPC L1 L2 L3 a.
    + deduction_lemma_case (q --> (p --> q)) Axiom2 J_IPC L1 L2 L3 a.
    + deduction_lemma_case ((p --> q) --> ((p --> (q --> r)) --> (p --> r))) Axiom3 J_IPC L1 L2 L3 a.
    + deduction_lemma_case ((p --> Bot) --> (p --> q)) Axiom4 J_IPC L1 L2 L3 a.
    + write L1 (|- ((a --> p) --> ((a --> p --> q) --> a -->q))) Axiom3.
      write L2 (|- (a --> p --> q) --> a --> q) (MP_IPC _ _ IHj1 L1).
      write L3 (|- (a --> q)) (MP_IPC _ _ IHj2 L2).
      evident.
    + apply Supp in H.
      write L1 (|- (p --> (a --> p))) Axiom2.
      write L2 (|- (a --> p)) (MP_IPC _ _ H L1).
      evident. 
    + apply supposition.
  - intros L1 L2.
    apply Supp in L2.
    write L3 (|- b) (MP_IPC _ _ L2 L1).
    evident.
Qed.

Theorem Deduction_Lemma_gen : forall a b P, (forall x, J_IPC x -> P x) -> (J_Supp a -> P b) <-> P (a --> b).
Proof.
Abort.

Ltac use deduction line_number := apply deduction; intros line_number; apply Supp in line_number.

Theorem double_negation_intro : forall p, J_IPC (p --> ~~ ~~ p).
Proof.
  intros.
  use IPC_deduction L1.
  use IPC_deduction L2.
  write L3 (|- Bot) (MP_IPC _ _ L1 L2).
  evident.
Qed.

Theorem triple_negation_elim : forall p, J_IPC (~~ ~~ ~~ p --> ~~ p).
Proof.
  intros.
  use IPC_deduction L1.
  use IPC_deduction L2.
  write L3 (|- ((~~ ~~ p --> Bot) --> (~~ ~~ p --> ~~ p))) Axiom4.
  write L4 (|- (~~ ~~ p --> ~~ p)) (MP_IPC _ _ L1 L3).
  write L5 (|- (p --> ~~ ~~ p)) double_negation_intro. (* AWESOME! you can use proved theorems! *)
  write L6 (|- ~~ ~~ p) (MP_IPC _ _ L2 L5).
  write L7 (|- ~~ p) (MP_IPC _ _ L6 L4).
  write L8 (|- Bot) (MP_IPC _ _ L2 L7).
  evident.
Qed.

Inductive J_CPC : Sentence -> Prop :=
| IPC_in_CPC : forall p, J_IPC p -> J_CPC p
| Axiom5 : forall p, J_CPC (~~ ~~ p --> p).
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
