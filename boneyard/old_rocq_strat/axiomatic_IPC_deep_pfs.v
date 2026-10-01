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
  | Arrow s s', Arrow t t' => (sent_eq s t) && (sent_eq s' t')
  | Bot, Bot => true
  | _, _ => false
  end.

Definition Axiom1 (s : Sentence) : bool :=
  match s with
  | Arrow p q => sent_eq p q
  | _ => false
  end.

Definition Axiom2 (s : Sentence) : bool :=
  match s with
  | (p --> (q --> p')) => sent_eq p p'
  | _ => false
  end.

Definition Axiom3 (s : Sentence) : bool :=
  match s with
  | ((p --> q) --> ((p' --> (q' --> r)) --> (p'' --> r'))) =>
      (sent_eq p p') && (sent_eq p' p'') && (sent_eq q q') && (sent_eq r r')
  | _ => false
  end.

Definition Axiom4 (s : Sentence) : bool :=
  match s with
  | ((p --> Bot) --> (p' --> q)) => sent_eq p p'
  | _ => false
  end.

Definition Axiom5 (s : Sentence) : bool :=
  match s with
  | ~~ ~~ p --> p' => sent_eq p p'
  | _ => false
  end.

Definition IPC_axioms : list (Sentence -> bool) := Axiom1 :: Axiom2 :: Axiom3 :: Axiom4 :: nil.

Definition CPC_axioms : list (Sentence -> bool) := Axiom5 :: IPC_axioms. (* hm. design choices. *)

Definition orb_pred := fun (P Q : Sentence -> bool) => fun (s : Sentence) => P s || Q s.

Definition is_axiom_of (system : list (Sentence -> bool)) : Sentence -> bool :=
  fold_left orb_pred system (fun (s : Sentence) => false).

Definition is_IPC_axiom := is_axiom_of IPC_axioms.
Definition is_CPC_axiom := is_axiom_of CPC_axioms. 


(*
- a proof is just a list of sentences, where each line is either an instance of the axioms or follows from a lines j,k < i by modus ponens.
- a proof is then a proof of whatever the last sentence is
*)

(* NO! DO NOT WANT THIS! NOT ALL LISTS OF SENTENCES ARE PROOFS! *)
(* Definition Pf := list Sentence. *)

(* "follows from modus ponens" means there exists lines earlier in the proof of the form |- p --> q and |- p for some p. *)
(* you could do a predicate has_valid_proof s, which would be true iff exists p, is_valid_proof p /\ last thing in p is a  *)
                                               
(* with the deep embedding I have a problem though. I can't think of a way to automatically check correctness of a fake proof in the middle of it, but I can for the shallow embedding. Fock. *)

(* Ok to add modus ponens to this you need to think about how you're going to represent modus ponens. I think it could be a tuple: ("Modus Ponens", i, j), where i and j are line numbers *)
(* Ok, but the axiom justifications are not going to be tuples, so how are we going to deal with justifications having multiple types? I want the types to potentially be indefinite too, to allow for derived rules... *)
(* ah, well we can define a system as a tuple of axioms and rules. and then we can define a justification as a sum type: either an axiom or a rule. But the thing is, not all rules will be of the same type, e.g. MP will be (MP, i, j), but substitution of prop identicals will be (PROPIDENT, j) (or even no j). Well, we could have inference rules be tuples of strings and lists of indices. These aren't C arrays! *)

Fixpoint fit_modus_ponens (ant impl consq : Sentence) : bool :=
  match impl with
  | p --> q => (sent_eq ant p) && (sent_eq consq q)
  | _ => false
  end.

Fixpoint valid_proof (p : list Sentence) : bool :=
  match p with
  | s :: p' => (IPC_axiom_check s) && (valid_proof p')
  | nil => false
  end. 

Fixpoint locate (s : Sentence) (p : list Sentence) (i : nat) : option nat :=
  match p with
  | s' :: p' => match sent_eq s s' with
                | true => Some i
                | false => locate s p'(i + 1)
                end
  | nil => None
  end. 

Fixpoint earlier_in_proof' (s : Sentence) (p : list Sentence) (i : nat) : (bool * option nat) :=
  match p with
  | s' :: p' => match sent_eq s s' with
                | true => (true, Some i)
                | false => earlier_in_proof' s p'(i + 1)
                end
  | nil => (false, None)
  end. (* i will be how many lines behind s its match is *)

Definition earlier_in_proof (s : Sentence) (p : list Sentence) (i : nat) : (bool * option nat) :=
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

  
