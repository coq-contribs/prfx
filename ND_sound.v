(** Proof Reflection in Coq ; ND_sound.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export ND.
Require Export eval_subst_lems.

Set Implicit Arguments.

Section Soundness_of_ND.

Variable A : Set.
Variable l1 l2 : list nat.
Variable FUN : fun_piT A l1.
Variable REL : rel_piT A l2.

Let P := prf l1 l2.
Let F := frm l1 l2.
Let T := trm l1.
Let Ts := trms l1.
Let E := eval_frm' FUN REL.
Let Etrm := eval_trm FUN.
Let Ecxt := eval_cxt' FUN REL.

Theorem ND_sound :
 forall (G : list F) (d : P) (p : F),
 ND G d p -> forall VAR : nat -> A, Ecxt VAR G -> E VAR p.
Proof.
intros G d p H.
elim H; clear H G d p.

(* top_intro *)
intros G V H. exact I.

(* hyp O *)
intros G p V H. exact (proj1 H).

(* hyp (S i) *)
intros G p q i Hi IH V H.
apply IH.
exact (proj2 H).

(* bot_elim *)
intros G d p Hd IHd V H.
elim (IHd V H).

(* imp_intro *)
intros G d p q H IH V HG.
simpl in |- *.
intro Hp.
exact (IH V (conj Hp HG)).

(* imp_elim *)
intros G d e p q Hd IHd He IHe V HG.
exact (IHd V HG (IHe V HG)).

(* cnj_intro *)
intros G d e p q Hd IHd He IHe V HG.
exact (conj (IHd V HG) (IHe V HG)).

(* cnj_elim1 *)
intros G d p q Hd IHd V HG.
elim (IHd V HG).
exact (fun H _ => H).

(* cnj_elim2 *)
intros G d p q Hd IHd V HG.
elim (IHd V HG).
exact (fun _ H => H).

(* dsj_intro1 *)
intros G d p q Hd IHd V HG.
exact (or_introl _ (IHd V HG)).

(* dsj_intro2 *)
intros G d p q Hd IHd V HG.
exact (or_intror _ (IHd V HG)).

(* dsj_elim *)
intros G d e f p q r Hd IHd He IHe Hf IHf V HG.
elim (IHd V HG).
exact (fun Hp => IHe V (conj Hp HG)).
exact (fun Hq => IHf V (conj Hq HG)).

(* uvq_intro *)
intros G d p Hd IHd V HG.
simpl in |- *. intro x.
apply IHd.
unfold Ecxt in |- *.
apply thinning_eval_cxt_O.
exact HG.

(* uvq_elim *)
intros G d t p Hd IHd V HG.
unfold E in |- *.
apply eval_subst_frm_ok2.
simpl in |- *. simpl in IHd.
apply IHd.
exact HG.

(* exq_intro *)
intros G d t p Hd IHd V HG.
split with (Etrm V t).
replace (insertVAR_O (Etrm V t) V) with (insertVAR (Etrm V t) V 0).
unfold E in |- *.
unfold Etrm in |- *.
pattern V at 1 in |- *.
replace V with (shiftVAR V 0).
apply eval_subst_frm_ok1.
apply IHd.
exact HG.
reflexivity.
reflexivity.

(* exq_elim *)
intros G d e p q Hd IHd He IHe V HG.
elim (IHd V HG).
intros x Hp.
unfold E in |- *.
apply
 (thinning_eval_frm2 FUN REL q x V 0).
apply IHe.
split.
exact Hp.
unfold Ecxt in |- *.
simpl in |- *.
apply thinning_eval_cxt_O.
exact HG.

Qed.

End Soundness_of_ND.

