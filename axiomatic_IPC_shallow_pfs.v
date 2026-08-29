Create HintDb judgement_db.

(* we'll start with a simple axiomatic propositional calculus for now *)
Inductive Sentence : Set :=
| Snt (n : nat)
| Arrow (s : Sentence) (s : Sentence)
| Bot.

Infix "-->" := Arrow (at level 60, right associativity).
Notation "~~ a" := (Arrow a Bot) (at level 59, right associativity).

(* this was a way to get around the deduction lemma with current setup *)
(* I think this is the best way to do it, because you should never suppose in the middle of a proof in an axiomatic proof, so the trivial case where you just prove the statement by supposition is taken care of in that yeah you're allowed to do that but it's clearly contrary to the intention *)
(* To do this with natural deduction would be a different story, you'd want to encode levels of supposition. *)
Inductive J_Supp : Sentence -> Prop :=
| supposition : forall p, J_Supp p.

(* we do the smallest system we (currently anticipate we will) use: intuitionistic propositional calculus. *)
(* really, we probably won't use it, but it serves as a test case for extension. *)
Inductive J_IPC : Sentence -> Prop :=
| Axiom1 : forall p,  J_IPC (p --> p)
| Axiom2 : forall p q, J_IPC (q --> (p --> q))
| Axiom3 : forall p q r, J_IPC ((p --> q) --> ((p --> (q --> r)) --> (p --> r)))
| Axiom4 : forall p q, J_IPC ((p --> Bot) --> (p --> q))
| ModusPonens : forall p q, J_IPC p -> J_IPC (p --> q) -> J_IPC q
| Supp : forall p, J_Supp p -> J_IPC p.

Theorem ex_falso_quodlibet : forall p, J_IPC (Bot --> p).
Proof.
  intros.
  assert (J_IPC ((Bot --> Bot) --> (Bot --> p))) by (apply Axiom4).
  assert (J_IPC (Bot --> Bot)) by (apply Axiom1).
  assert (J_IPC (Bot --> p)) by (apply (ModusPonens _ _ H0 H)).
  apply H1.
Qed.
(* a bit clunky lol *)

(* I'll just redefine |- later, doing this just for ease now *)
Notation "|- a" := (J_IPC a) (at level 61, no associativity). (* does associativity matter for unaary operators? *)

Ltac write line_number judgement justification :=
  assert (line_number : judgement) by (apply justification).

Ltac evident := assumption.

Theorem ex_falso_quodlibet_2 : forall p, |- Bot --> p.
Proof.
  intros. 
  write L1 (|- ((Bot --> Bot) --> (Bot --> p))) Axiom4.
  write L2 (|- (Bot --> Bot)) Axiom1.
  write L3 (|- (Bot --> p)) (ModusPonens _ _ L2 L1).
  evident.
Qed.
(* better, ideally I get rid of the f? I'm not clear on whether we should lol *)
(* if we phrase f as the act of writing (now named write), it's just the externalization of a judgement. Which makes sense: the inner act of judging has already occurred, putting it on paper is nothing but externalizing it. *)

(* NOTE: not meant for general usage. Just to make the Deduction_Lemma proof go through. *)
Ltac deduction_lemma_case axiom_content axiom_cons L1 L2 L3 a :=
  write L1 (|- axiom_content --> (a --> axiom_content)) Axiom2;
  write L2 (|- axiom_content) axiom_cons;
  write L3 (|- (a --> axiom_content)) (ModusPonens _ _ L2 L1);
  evident.

(* this is a limited form of deduction lemma: can only do one supposition *)
(* well actually I don't think it's limited in any other sense. I mean, it's a biconditional. *)
(* and below we have a proof where we do it twice *)
Theorem Deduction_Lemma : forall a b, (J_Supp a -> J_IPC b) <-> J_IPC (a --> b) .
Proof.
  intros a b. 
  apply conj.
  - intros.
    induction H. 
    + deduction_lemma_case (p --> p) Axiom1 L1 L2 L3 a.
    + deduction_lemma_case (q --> (p --> q)) Axiom2 L1 L2 L3 a.
    + deduction_lemma_case ((p --> q) --> ((p --> (q --> r)) --> (p --> r))) Axiom3 L1 L2 L3 a.
    + deduction_lemma_case ((p --> Bot) --> (p --> q)) Axiom4 L1 L2 L3 a.
    + write L1 (|- ((a --> p) --> ((a --> p --> q) --> a -->q))) Axiom3.
      write L2 (|- (a --> p --> q) --> a --> q) (ModusPonens _ _ IHj1 L1).
      write L3 (|- (a --> q)) (ModusPonens _ _ IHj2 L2).
      evident.
    + apply Supp in H.
      write L1 (|- (p --> (a --> p))) Axiom2.
      write L2 (|- (a --> p)) (ModusPonens _ _ H L1).
      evident. 
    + apply supposition.
  - intros L1 L2.
    apply Supp in L2.
    write L3 (|- b) (ModusPonens _ _ L2 L1).
    evident.
Qed.

Ltac use_deduction line_number := apply Deduction_Lemma; intros line_number; apply Supp in line_number.

Theorem double_negation_intro : forall p, J_IPC (p --> ~~ ~~ p).
Proof.
  intros.
  use_deduction L1.
  use_deduction L2.
  write L3 (|- Bot) (ModusPonens _ _ L1 L2).
  evident.
Qed.

Theorem triple_negation_elim : forall p, J_IPC (~~ ~~ ~~ p --> ~~ p).
Proof.
  intros.
  use_deduction L1.
  use_deduction L2.
  write L3 (|- ((~~ ~~ p --> Bot) --> (~~ ~~ p --> ~~ p))) Axiom4.
  write L4 (|- (~~ ~~ p --> ~~ p)) (ModusPonens _ _ L1 L3).
  write L5 (|- (p --> ~~ ~~ p)) double_negation_intro. (* AWESOME! you can use proven theorems! *)
  write L6 (|- ~~ ~~ p) (ModusPonens _ _ L2 L5).
  write L7 (|- ~~ p) (ModusPonens _ _ L6 L4).
  write L8 (|- Bot) (ModusPonens _ _ L2 L7).
  evident.
Qed.

Inductive J_CPC : Sentence -> Prop :=
| IPC_Incl : forall p, J_IPC p -> J_CPC p
| Axiom5 : forall p, J_CPC (~~ ~~ p --> p).
Hint Constructors J_CPC : judgements.


(* TODO: extensions. I think extension with modus ponens is going to be a bitch. *)
(* I think the reason the deduction lemma had to have this honestly pretty ad hoc fix was that the proof of the deduction lemma that you have in mind is within a system where the proofs themselves are defined objects that can be looked into in a particular way. Here, proofs are at the meta-level, they're in Ltac, so we can't really talk about them in Gallina, much less look at specific lines (because there is no notion of a line in a Gallina proof term). I'm going to call this way of doing things a shallow embedding of proofs. I think we need a deep embedding of proofs. *)
