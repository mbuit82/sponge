(* Trying to do Martin-Lof *)
Inductive Expression : Type :=
| Emp (n : nat)
| Arrow (s : Expression) (s : Expression)
| And (s : Expression) (s : Expression)
| Or (s : Expression) (s : Expression)
| Bot.
Infix "-->" := Arrow (at level 60, right associativity).
Infix "v" := Or (at level 70, right associativity).
Infix "&" := And (at level 70, right associativity). 
Notation "~~ a" := (Arrow a Bot) (at level 75, right associativity).

Inductive T_J : Expression -> Prop :=
| Arrow_I : forall p q, (T_J p -> T_J q) -> T_J (p --> q) (* deduction lemma?? *)
| Arrow_E : forall p q, T_J (p --> q) -> T_J p -> T_J q (* modus ponens? *)
| And_I : forall p q, T_J p -> T_J q -> T_J (p & q)
| And_E_L : forall p q, T_J (p & q) -> T_J p
| And_E_R : forall p q, T_J (p & q) -> T_J q
| Or_I_L : forall p q, T_J p -> T_J (p v q)
| Or_I_R : forall p q, T_J q -> T_J (p v q).
| Or_E : forall p q, 

Inductive P_J : Expression -> Prop :=
| Bot_F : P_J Bot
| Emp_F : forall (n : nat), P_J (Emp n)
| Arrow_F : forall p q, P_J p -> (T_J p -> P_J q) -> P_J (Arrow p q)
| And_F : forall p q, P_J p -> P_J q -> P_J (p & q)
| Or_F : forall p q, P_J p -> P_J q -> P_J (p v q).





Inductive Sentence : Type :=
| Snt (n : nat)
| Arrow (s : Sentence) (s : Sentence)
| And (s : Sentence) (s : Sentence)
| Or (s : Sentence) (s : Sentence)
| Bot.

Infix "-->" := Arrow (at level 60, right associativity).
Infix "v" := Or (at level 70, right associativity).
Infix "&" := And (at level 70, right associativity). 
Notation "~~ a" := (Arrow a Bot) (at level 75, right associativity).


                                               

(* we do the smallest system we (currently anticipate we will) use: intuitionistic propositional calculus. *)
(* really, we probably won't use it, but it serves as a test case for extension. *)
Inductive J_IPC : Sentence -> Prop :=
| Axiom1 : forall p,  J_IPC (p --> p)
| Axiom2 : forall p q, J_IPC (q --> (p --> q))
| Axiom3 : forall p q r, J_IPC ((p --> q) --> ((p --> (q --> r)) --> (p --> r)))
| Axiom4 : forall p q, J_IPC ((p --> Bot) --> (p --> q))
| ModusPonens : forall p q, J_IPC p -> J_IPC (p --> q) -> J_IPC q.

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
Notation "|- a" := (J_IPC a) (at level 76, no associativity).

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

Ltac deduction_lemma_case axiom_content axiom_cons L1 L2 L3 a :=
  write L1 (|- axiom_content --> (a --> axiom_content)) Axiom2;
  write L2 (|- axiom_content) axiom_cons;
  write L3 (|- (a --> axiom_content)) (ModusPonens _ _ L2 L1);
  evident. 

Theorem Deduction_Lemma : forall a b, (J_IPC a -> J_IPC b) <-> J_IPC (a --> b) .
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
      write h2 (|- (a --> q)) (ModusPonens _ _ IHj2 L2).
      evident.
    + admit. (* I think this is case where b is just a *)
  - intros L1. apply conj.
    + 
    L2.
    write L3 (|- b) (ModusPonens _ _ L2 L1).
    evident. 





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

  
