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

(* Definition Modus_Ponens (P : Sentence -> Prop) : Prop := *)
(*   forall p q, P p -> P (p --> q) -> P q. *)
(* Hint Unfold Modus_Ponens : mp_db. *)
(* I think we want the generic predicate to be of type System -> Sentence -> Prop, where System = Sentence -> Prop *)
Definition Judgement := fun (P : Sentence -> Prop) (s : Sentence) => P s.
Notation "P |- s" := (Judgement P s) (at level 62, no associativity).
(* I think this is the best fix... *)
Axiom ModusPonens : forall P p q, P |- p -> P |- (p --> q) -> P |- q. 

Theorem inclusion : forall P P' s, P |- s -> (forall s', P s' -> P' s') -> P' |- s.
Proof.
  intros. specialize (H0 s).
  cbv in H. apply H0 in H.
  cbv. apply H.
Qed.

(* this is like an axiom schema for axiom schemas lol *)
Definition Axiom2_gen P := forall p q, P |- (p --> (q --> p)).

(* yeah, the deep embedding strategy is better lol. Might just be too much structure here *)

(* start with intuitionistic calculus *)
(* what I don't like about this is that these belong _only_ to IPC. They shouldn't. *)
Inductive IPC : Sentence -> Prop :=
| Axiom2 : forall p q, IPC |- (p --> (q --> p))
| Axiom3 : forall p q r, IPC |- ((p --> q) --> ((p --> (q --> r)) --> (p --> r)))
| AndIntro : forall p q, IPC |- (p --> q --> (p & q))
| AndL : forall p q, IPC |- ((p & q) --> p)
| AndR : forall p q, IPC |- ((p & q) --> q)
| OrL : forall p q, IPC |- (p --> (p v q))
| OrR : forall p q, IPC |- (q --> (p v q))
| OrElim : forall p q r, IPC |- ((p --> r) --> (q --> r) --> (p v q) --> r)
| ExFalso : forall p, IPC |- (Bot --> p).

Ltac write line_number judgement justification :=
  assert (line_number : judgement) by (eauto using justification with judgement_db).

Ltac evident := assumption.

Theorem Axiom1 : forall p, IPC |- (p --> p).
Proof.
  intros.
  write L1 (IPC |- ((p --> (p --> p)) --> ((p --> ((p --> p) --> p)) --> (p --> p)))) Axiom3.
  write L2 (IPC |- (p --> p --> p)) Axiom2.
  write L3 (IPC |- ((p --> ((p --> p) --> p)) --> (p --> p))) (ModusPonens _ _ _ L2 L1).
  write L4 (IPC |- (p --> ((p --> p) --> p))) Axiom2.
  write L5 (IPC |- (p --> p)) (ModusPonens _ _ _ L4 L3).
  evident.
Qed.

Theorem Bot_contradiction : forall p, IPC |- (Bot <--> p & ~~ p).
Proof.
  intros.
  write L1 (IPC |- ((Bot --> p & ~~p) --> (p & ~~ p --> Bot) --> (Bot --> p & ~~p) & (p & ~~ p --> Bot))) AndIntro.
  write L2 (IPC |- (Bot --> p & ~~ p)) ExFalso.
  write L3 (IPC |- ((p & ~~ p --> Bot) --> (Bot --> p & ~~p) & (p & ~~ p --> Bot))) (ModusPonens _ _ _ L2 L1).
  write L4 (IPC |- ((p & ~~ p --> p) --> (p & ~~ p --> (p & ~~ p --> p)))) Axiom2.
  write L5 (IPC |- (p & ~~ p --> p)) AndL.
  write L6 (IPC |- (p & ~~ p --> (p & ~~ p --> p))) (ModusPonens _ _ _ L5 L4).
  write L7 (IPC |- ((p & ~~ p --> ~~ p) --> (p & ~~ p --> (p & ~~ p --> ~~ p)))) Axiom2.
  write L8 (IPC |- (p & ~~ p --> ~~ p)) AndR.
  write L9 (IPC |- (p & ~~ p --> (p & ~~ p --> ~~ p))) (ModusPonens _ _ _ L8 L7).
  write L10 (IPC |- ((p & ~~ p --> p) --> (p & ~~ p --> ~~ p) --> (p & ~~ p --> Bot))) Axiom3.
  write L11 (IPC |- ((p & ~~ p --> ~~ p) --> (p & ~~ p --> Bot))) (ModusPonens _ _ _ L5 L10).
  write L12 (IPC |- (p & ~~ p --> Bot)) (ModusPonens _ _ _ L8 L11).
  write L13 (IPC |- (Bot <--> p & ~~ p)) (ModusPonens _ _ _ L12 L3).
  evident.
Qed.



(* DERIVED RULES *)
(* a derived inference rules. NO DEDUCTION NEEDED TO MAKE THESE. *)
Theorem J_Conj : forall a b, IPC |- a -> IPC |- b -> IPC |- (a & b).
Proof.
  intros a b L1 L2.
  write L3 (IPC |- (a --> b --> a & b)) AndIntro.
  write L4 (IPC |- (b --> a & b)) (ModusPonens _ _ _ L1 L3).
  write L5 (IPC |- (a & b)) (ModusPonens _ _ _ L2 L4).
  evident.
Qed.

Theorem J_Conj_Cond : forall a b c, IPC |- (c --> a) -> IPC |- (c --> b) -> IPC |- (c --> (a & b)).
Proof.
  intros a b c L1 L2.
  write L3 (IPC |- ((c --> a) --> (c --> a --> b --> a & b) --> c --> b --> a & b)) Axiom3.
  write L4 (IPC |- ((c --> a --> b --> a & b) --> c --> b --> a & b)) (ModusPonens _ _ _ L1 L3).
  write L5 (IPC |- ((a --> b --> a & b) --> (c --> a --> b --> a & b))) Axiom2.
  write L6 (IPC |- (a --> b --> a & b)) AndIntro.
  write L7 (IPC |- (c --> a --> b --> a & b)) (ModusPonens _ _ _ L6 L5).
  write L8 (IPC |- (c --> b --> a & b)) (ModusPonens _ _ _ L7 L4).
  write L9 (IPC |- ((c --> b) --> (c --> b --> a & b) --> c --> a & b)) Axiom3.
  write L10 (IPC |- ((c --> b --> a & b) --> c --> a & b)) (ModusPonens _ _ _ L2 L9).
  write L11 (IPC |- (c --> a & b)) (ModusPonens _ _ _ L8 L10).
  evident.
Qed.

Theorem MP_bicond : forall a b, IPC |- a -> IPC |- (a <--> b) -> IPC |- b.
Proof.
  intros a b L1 L2.
  write L3 (IPC |- ((a <--> b) --> (a --> b))) AndL.
  write L4 (IPC |- (a --> b)) (ModusPonens _ _ _ L2 L3).
  write L5 (IPC |- b) (ModusPonens _ _ _ L1 L4).
  evident.
Qed.
  
(* ideally, the proof of a --> b is automatic? NO, just use the name of a previous theorem! eh almost, would need to get rid of foralls. Well no you could it automatically if you have a hint db and you know its an instance of a prev theorem *)
Theorem antecedent_weakening : forall a b c, IPC |- (b --> c) -> IPC |- (a --> b) -> IPC |- (a --> c).
Proof.
  intros a b c L1 L2.
  write L3 (IPC |- ((a --> b) --> (a --> b --> c) --> a --> c)) Axiom3.
  write L4 (IPC |- ((a --> b --> c) --> a --> c)) (ModusPonens _ _ _ L2 L3).
  write L5 (IPC |- ((b --> c) --> a --> b --> c)) Axiom2.
  write L6 (IPC |- (a --> b --> c)) (ModusPonens _ _ _ L1 L5).
  write L7 (IPC |- (a --> c)) (ModusPonens _ _ _ L6 L4).
  evident.
Qed.

(* comment above applies here too *)
Theorem consequent_strengthening : forall a b c, IPC |- (a --> b) -> IPC |- (b --> c) -> IPC |- (a --> c).
Proof.
  intros a b c L1 L2.
  apply (antecedent_weakening _ _ _ L2 L1). (* isn't that cool? *)
Qed.

(* I want an apply tactic that takes a theorem and automatically does MP too *)
(* END DERIVED RULES *)



Theorem and_comm : forall p q, IPC |- (p & q <--> q & p).
Proof.
  intros.
  write L1 (IPC |- (p & q --> p)) AndL.
  write L2 (IPC |- (p & q --> q)) AndR.
  write L3 (IPC |- (p & q --> q & p)) (J_Conj_Cond _ _ _ L2 L1).
  write L4 (IPC |- (q & p --> q)) AndL.
  write L5 (IPC |- (q & p --> p)) AndR.
  write L6 (IPC |- (q & p --> p & q)) (J_Conj_Cond _ _ _ L5 L4).
  write L7 (IPC |- (p & q <--> q & p)) (J_Conj _ _ L3 L6).
  evident.
Qed.

Theorem Axiom4 : forall p q, IPC |- ((p --> Bot) --> p --> q).
Proof.
  intros.
  
  write L1 (IPC |- (~~ p --> p --> ~~ p & p)) AndIntro.
  write L2 (IPC |- (Bot --> q)) ExFalso.
  write L3 (IPC |- (Bot <--> p & ~~ p)) Bot_contradiction.
  write L4 (IPC |- ((Bot <--> p & ~~ p) --> (p & ~~ p --> Bot))) AndR.
  write L5 (IPC |- (p & ~~ p --> Bot)) (ModusPonens _ _ _ L3 L4).
  write L6 (IPC |- (~~ p & p <--> p & ~~ p)) (and_comm (~~p) p).
  write L7 (IPC |- ((~~ p & p <--> p & ~~ p) --> (~~ p & p --> p & ~~ p))) AndL.
  write L8 (IPC |- (~~ p & p --> p & ~~ p)) (ModusPonens _ _ _ L6 L7).
  
Admitted.

Theorem uncurrying_dl : forall p q r, IPC |- (p --> q --> r) -> IPC |- (p & q --> r).
Proof.
  intros p q r L1 .
  Admitted. 
  
Theorem uncurrying : forall p q r, IPC |- ((p --> q --> r) --> (p & q --> r)).
Proof.
  intros.
Admitted.

Theorem currying_dl : forall p q r, IPC |- (p & q --> r) -> IPC |- (p --> q --> r).
Proof.
  intros p q r L1.
  write L2 (IPC |- ((p & q --> r) --> (p & q --> r --> (q --> r)) --> p & q --> q --> r)) Axiom3.
  write L3 (IPC |- ((p & q --> r --> (q --> r)) --> p & q --> q --> r)) (ModusPonens _ _ _ L1 L2).
  write L4 (IPC |- (r --> q --> r)) Axiom2.
  write L5 (IPC |- ((r --> q --> r) --> (p & q --> r --> q --> r))) Axiom2.
  write L6 (IPC |- (p & q --> r --> q --> r)) (ModusPonens _ _ _ L4 L5).
  write L7 (IPC |- (p & q --> q --> r)) (ModusPonens _ _ _ L6 L3).
Admitted.

Theorem currying : forall p q r, IPC |- ((p & q --> r) --> (p --> q --> r)).
Proof.
  intros.
Admitted.

Theorem object_MP : forall p q, IPC |- (p --> (p --> q) --> q).
Proof.
  intros.
  (* this  proof would go really easily after doing switch_func_args *)
  (* and switch_func_args would go really easily after doing currying *)
  (* and currying is also what double_negation_intro depends on *)
Admitted.

Theorem double_negation_intro : forall p, IPC |- (p --> ~~ ~~ p).
Proof.
  intros.
  write L1 (IPC |- ((p --> Bot) --> p --> Bot)) Axiom1.
  write L2 (IPC |- (((p --> Bot) --> p --> Bot) --> (p --> Bot) & p --> Bot)) uncurrying.
  write L3 (IPC |- ((p --> Bot) & p --> Bot)) (ModusPonens _ _ _ L1 L2).
  write L4 (IPC |- (p & ~~ p <--> ~~ p & p)) and_comm.
  write L5 (IPC |- ((p & ~~ p <--> ~~ p & p) --> p & ~~ p --> ~~ p & p)) AndL.
  write L6 (IPC |- (p & ~~ p --> ~~ p & p)) (ModusPonens _ _ _ L4 L5).
  write L7 (IPC |- (p & ~~ p --> Bot)) (antecedent_weakening _ _ _ L3 L6).
  write L8 (IPC |- ((p & ~~ p --> Bot) --> (p --> ~~ p --> Bot))) currying.
  write L9 (IPC |- (p --> ~~ p --> Bot)) (ModusPonens _ _ _ L7 L8).
  evident.
Qed.

Theorem idk : forall p q r, IPC |- ((p --> r) --> (q --> p) --> (q --> r)).
Proof.
Admitted.

(* Theorem switch_func_args_3_deductions : forall p q r, IPC |- ((p --> q --> r) --> (q --> p --> r)). *)
(* Proof. *)
(*   intros. *)
(*   write L1 (IPC |- ((p --> q --> r) --> p & q --> r)) uncurrying. *)
(*   write L2 (IPC |- (p & q --> q & p)) *)
  
(*   use IPC_deduction L1. *)
(*   use IPC_deduction L2. *)
(*   use IPC_deduction L3. *)
(*   write L4 (IPC |- (q --> r)) (ModusPonens _ _ _ L3 L1). *)
(*   write L5 (IPC |- r) (ModusPonens _ _ _ L2 L4). *)
(*   evident. *)
(* Qed. *)

(* Theorem switch_func_args_2_deductions : forall p q r, IPC |- ((p --> q --> r) --> (q --> p --> r)). *)
(* Proof. *)
(*   intros. *)
(*   use IPC_deduction L1. *)
(*   use IPC_deduction L2. *)
(*   write L3 (IPC |- (q --> p --> q)) Axiom2. *)
(*   write L4 (IPC |- (p --> q)) (ModusPonens _ _ _ L2 L3). *)
(*   write L5 (IPC |- ((p --> q) --> (p --> q --> r) --> (p --> r))) Axiom3. *)
(*   write L6 (IPC |- ((p --> q --> r) --> (p --> r))) (ModusPonens _ _ _ L4 L5). *)
(*   write L7 (IPC |- (p --> r)) (ModusPonens _ _ _ L1 L6). *)
(*   evident. *)
(* Qed. *)

(* Theorem switch_func_args_1_deduction : forall p q r, IPC |- ((p --> q --> r) --> (q --> p --> r)). *)
(* Proof. *)
(*   intros. *)
(*   use IPC_deduction L1. *)
(*   write L2 (IPC |- (q --> q)) Axiom1. *)
(*   write L3 (IPC |- ((q --> p --> q) --> q --> (q --> p --> q))) Axiom2. *)
(*   write L4 (IPC |- (q --> p --> q)) Axiom2. *)
(*   write L5 (IPC |- (q --> q --> p --> q)) (ModusPonens _ _ _ L4 L3). *)
  
  
(*   Print IPC |-. *)
(*   write L2 (IPC |- ((q --> (p --> q --> r)) --> (q --> (p --> q --> r) --> (p --> r)) --> (q --> p --> r))) Axiom3. *)
(*   write L3 (IPC |- ((p --> q --> r) --> q --> (p --> q --> r))) Axiom2. *)
(*   write L4 (IPC |- (q --> (p --> q --> r))) (ModusPonens _ _ _ L1 L3). *)
(*   write L5 (IPC |- ((q --> (p --> q --> r) --> p --> r) --> q --> p --> r)) (ModusPonens _ _ _ L4 L2). *)
  

  
  (* write L1 (IPC |- ((p --> q --> r) --> (p --> q --> r))) Axiom1. *)
  (* write L2 (IPC |- (p --> p)) Axiom1. *)
  (* write L3 (IPC |- (q --> q)) Axiom1. *)
  (* Print IPC |-. *)
  
  (* write L1 (IPC |- ((p --> q --> r) --> (q --> (p --> q --> r)))) Axiom2. *)
  (* write L2 (IPC |- *)
  (*             Print IPC |-. *)
  (*           Admitted.  *)

            (* what if you make deduction not extensible? Like, by design. I never once used deduction in my modal logic homework. That't not what I want my system to be for. But it sure as hell is nice for getting things set up nicely. The sort of thinking that deduction is doesn't really seem as common for modal logic proofs. *)

            (* the funny thing is, I do want substitution of logical identicals lmfao. And that would actually go through super easily in practice by deduction.
               what am I even doing this for? Like, that's not clear to me. Not the meta-level why, I got that. The object-level why of what sort of proofs I want to be doing, what sort of reasoning I'm trying to isolate.

               I think the ideal version of the tool lets the user choose whether glossy reasoning is allowed for a certain proof. Wow, this is hard. What should it take to turn glossy reasoning on? Damn, this is hard lmfao. Design choices. 
             *)

(* Theorem triple_negation_elim : forall p, IPC |- (~~ ~~ ~~ p --> ~~ p). *)
(* Proof. *)
(*   intros. *)
(*   use IPC_deduction L1. *)
(*   use IPC_deduction L2. *)
(*   write L3 (IPC |- ((~~ ~~ p --> Bot) --> (~~ ~~ p --> ~~ p))) Axiom4. *)
(*   write L4 (IPC |- (~~ ~~ p --> ~~ p)) (ModusPonens _ _ _ L1 L3). *)
(*   write L5 (IPC |- (p --> ~~ ~~ p)) double_negation_intro. (* AWESOME! you can use proved theorems! *) *)
(*   write L6 (IPC |- *)
(*               ~~ ~~ p) (ModusPonens _ _ _ L2 L5). *)
(*   write L7 (IPC |- ~~ p) (ModusPonens _ _ _ L6 L4). *)
(*   write L8 (IPC |- Bot) (ModusPonens _ _ _ L2 L7). *)
(*   evident. *)
(* Qed. *)

Inductive J_CPC : Sentence -> Prop :=
| IPC_in_CPC : forall p, IPC p -> J_CPC p
| DNE : forall p, J_CPC |- (~~ ~~ p --> p). (* consider changing this name *)
(* Hint Resolve IPC_in_CPC : judgement_db. *)
(* Hint Resolve IPC_in_CPC : mp_db. *)

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

