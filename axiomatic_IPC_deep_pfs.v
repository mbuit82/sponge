From Stdlib Require Import Bool List Arith.

(* we'll start with a simple axiomatic propositional calculus for now *)
Inductive Sentence : Set :=
| Snt (n : nat)
| Arrow (s : Sentence) (s : Sentence)
| Bot.

Infix "-->" := Arrow (at level 60, right associativity).
Notation "~~ a" := (Arrow a Bot) (at level 75, right associativity).

Fixpoint sent_eq (a : Sentence) (b : Sentence) : bool :=
  match a, b with
  | Snt m, Snt n => n =? m
  | Arrow s s', Arrow t t' => andb (sent_eq s t) (sent_eq s' t')
  | Bot, Bot => true
  | _, _ => false
  end.

Inductive IPC_Axiom : Sentence -> Prop :=
| AS1 : forall p,  IPC_Axiom (p --> p)
| AS2 : forall p q, IPC_Axiom (q --> (p --> q))
| AS3 : forall p q r, IPC_Axiom ((p --> q) --> ((p --> (q --> r)) --> (p --> r)))
| AS4 : forall p q, IPC_Axiom ((p --> Bot) --> (p --> q)).

(*
- a proof is just a list of sentences, where each line is either an instance of the axioms or follows from a lines j,k < i by modus ponens.
- a proof is then a proof of whatever the last sentence is
*)

(* NO! DO NOT WANT THIS! NOT ALL LISTS OF SENTENCES ARE PROOFS! *)
(* Definition Pf := list Sentence. *)

(* "follows from modus ponens" means there exists lines earlier in the proof of the form |- p --> q and |- p for some p. *)
(* you could do a predicate has_valid_proof s, which would be true iff exists p, is_valid_proof p /\ last thing in p is a  *)
                                               
(* with the deep embedding I have a problem though. I can't think of a way to automatically check correctness of a fake proof in the middle of it, but I can for the shallow embedding. Fock. *)


Fixpoint valid_proof (p : Pf) : Prop :=
  match p with
  | s :: p' => IPC_Axiom s /\ valid_proof p'
  | nil => False
  end. 

Fixpoint locate (s : Sentence) (p : Pf) (i : nat) : option nat :=
  match p with
  | s' :: p' => match sent_eq s s' with
                | true => Some i
                | false => locate s p'(i + 1)
                end
  | nil => None
  end. 

Fixpoint earlier_in_proof' (s : Sentence) (p : Pf) (i : nat) : (bool * option nat) :=
  match p with
  | s' :: p' => match sent_eq s s' with
                | true => (true, Some i)
                | false => earlier_in_proof' s p'(i + 1)
                end
  | nil => (false, None)
  end. (* i will be how many lines behind s its match is *)

Definition earlier_in_proof (s : Sentence) (p : Pf) (i : nat) : (bool * option nat) :=
  match p with
  | s' :: p' => earlier_in_proof' s p' i
  | nil => (false, None)
  end.

(* right now we have proofs being _backwards_ lists... but that's only because of these functions. *)





forall p s, J_IPC s -> is_proof_of (s :: nil) s
forall p s, 

Fixpoint is_proof_of (p : Pf) (s : Sentence) : Prop :=
  | 







Inductive Sentence : Type :=
| phi
| psi
| Box (s : Sentence)
| Diamond (s : Sentence)
.



Theorem triple_negation :
  forall P : Prop, ~ P <-> ~ ~ ~ P.
Proof.
  intros.
  apply conj.
  - unfold not. intros. apply H0. apply H.
  - unfold not. intros. apply H. intros. apply H1. apply H0.
Qed.



Inductive TruthValue : Type :=
| top
| M
| bot.

Definition implies (phi : TruthValue) (psi : TruthValue) : TruthValue :=
  match phi, psi with
  | top, top => top
  | top, M => M
  | top, bot => bot
  | M, top => top
  | M, M => top
  | M, bot => bot
  | bot, top => top
  | bot, M => top
  | bot, bot => top
  end.
Infix "-->" := implies (at level 60, right associativity).

Notation "~~ a" := (implies a bot) (at level 75, right associativity).

Definition valid (phi : TruthValue) : Prop :=
  phi = top. (* not quite the real deal but good enough for us *)

Ltac brute_force :=
  intros;
  repeat match goal with
  | x : TruthValue |- _ => destruct x
  end;
  reflexivity.

Theorem axiom_1_valid : forall phi, valid (phi --> phi).
Proof. brute_force. Qed.

Theorem axiom_2_valid : forall phi psi, valid (phi --> psi --> phi).
Proof. brute_force. Qed.

Theorem axiom_3_valid : forall a b c,
    valid ((a --> b) --> ((a --> (b --> c)) --> (a --> c))).
Proof. brute_force. Qed. 

Theorem axiom_4_valid : forall phi psi,
    valid ((phi --> bot) --> (phi --> psi)).
Proof. brute_force. Qed.

Theorem modus_ponens_preserving : forall phi psi,
    valid phi -> (valid (phi --> psi)) -> valid psi.
Proof.
  intros phi psi. intros H. unfold valid in H.
  rewrite H. intros Himp. unfold valid in Himp.
  destruct psi; try reflexivity; inversion Himp.
Qed.

Theorem axiom_5_not_valid : ~ forall phi, valid ((~~ ~~ phi) --> phi).
Proof.
  intros H.
  pose proof (H M) as Hspec.
  unfold valid in Hspec.
  simpl in Hspec. inversion Hspec.
Qed. 

  
