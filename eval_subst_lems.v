(** Proof Reflection in Coq ; eval_subst_lems.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export subst.
Require Export eval_lift_lems.

Set Implicit Arguments.

Section eval_subst_lemmas.

Variable A : Set.
Variable l1 l2 : list nat.
Variable FUN : fun_piT A l1.
Variable REL : rel_piT A l2.
Let P := prf l1 l2.
Let F := frm l1 l2.
Let T := trm l1.
Let Ts := trms l1.
Let C := list F.
Let E := eval_frm' FUN REL.
Let Etrm := eval_trm FUN.
Let Ecxt := eval_cxt' FUN REL.

Lemma eval_subst_var_ok :
 forall (n i : nat) (VAR : nat -> A) (t : T),
 Etrm VAR (subst_var n i t) = insertVAR (Etrm (shiftVAR VAR n) t) VAR n i.
Proof.
simple induction n.
simple destruct i; reflexivity.
intros n' IH.
simple destruct i.
reflexivity.
intros i' V t.
simpl in |- *.
unfold Etrm in |- *.
rewrite (shiftVAR_lift_trm_O FUN V (subst_var n' i' t)).
exact (IH i' (fun p => V (S p)) t).
Qed.

Lemma eval_subst_trm_ok :
 forall (n : nat) (VAR : nat -> A) (t u : T),
 Etrm VAR (subst_trm n t u) =
 Etrm (insertVAR (Etrm (shiftVAR VAR n) u) VAR n) t.
Proof.
intros n V t u.
move t after u.
induction t.
simpl in |- *.
apply eval_subst_var_ok.
simpl in |- *.
rewrite mapn_mapn.
set (f := fun t => Etrm V (subst_trm n t u)) in *.
set (g := Etrm (insertVAR (Etrm (shiftVAR V n) u) V n)) in *.
rewrite (mapn_inn f g l H); reflexivity.
Qed.

Lemma eval_subst_trms_ok :
 forall (n : nat) (VAR : nat -> A) (k : nat) (l : Ts k) (u : T),
 eval_trms FUN VAR (mapn (fun t => subst_trm n t u) l) =
 eval_trms FUN (insertVAR (Etrm (shiftVAR VAR n) u) VAR n) l.
Proof.
intros n V k l u.
induction l; simpl in |- *.
reflexivity.
rewrite eval_subst_trm_ok; rewrite IHl; reflexivity.
Qed.

Lemma eval_subst_frm_ok :
 forall (p : F) (n : nat) (VAR : nat -> A) (u : T),
 E VAR (subst_frm n p u) <-> E (insertVAR (Etrm (shiftVAR VAR n) u) VAR n) p.
Proof.
simple induction p; clear p; simpl in |- *.
intros; apply piffp.
intros; apply piffp.
intros i l n V u.
rewrite (eval_subst_trms_ok n V l u).
apply piffp.
intros p1 IH1 p2 IH2 n V u.
elim (IH1 n V u); intros IH1a IH1b.
elim (IH2 n V u); intros IH2a IH2b.
split; auto.     
intros p1 IH1 p2 IH2 n V u.
elim (IH1 n V u); intros IH1a IH1b.
elim (IH2 n V u); intros IH2a IH2b.
split; intro H; elim H; split; auto.
intros p1 IH1 p2 IH2 n V u.
elim (IH1 n V u); intros IH1a IH1b.
elim (IH2 n V u); intros IH2a IH2b.
split; intro H; elim H; auto.
intros p IH n V u.
split; intros H x; elim (IH (S n) (insertVAR_O x V) u); intros IHa IHb;
 unfold Etrm in |- *;
 elim
  (VARexteq_eval_frm FUN REL p _ _
     (insVARswap x (eval_trm FUN (shiftVAR (insertVAR_O x V) (S n)) u) n V));
 intros H1 H2.
rewrite <- (VARexteq_eval_trm FUN _ _ (insVAR_shift x n V)).
apply H2.
apply IHa. 
apply H.
apply IHb.
apply H1.
rewrite (VARexteq_eval_trm FUN _ _ (insVAR_shift x n V)). 
apply H.
(*exq*)
intros p IH n V u.
split; intro H; elim H; intros x H0; elim (IH (S n) (insertVAR_O x V) u);
 intros IHa IHb; unfold Etrm in |- *;
 elim
  (VARexteq_eval_frm FUN REL p _ _ 
     (insVARswap x (eval_trm FUN (shiftVAR (insertVAR_O x V) (S n)) u) n V));
 intros H1 H2; exists x. 
rewrite <- (VARexteq_eval_trm FUN _ _ (insVAR_shift x n V)). 
apply H2. 
apply IHa.  
exact H0. 
apply IHb. 
apply H1. 
rewrite (VARexteq_eval_trm FUN _ _ (insVAR_shift x n V)).  
exact H0.
Qed.

Lemma eval_subst_frm_ok1 :
 forall (p : F) (n : nat) (VAR : nat -> A) (t : T),
 E VAR (subst_frm n p t) -> E (insertVAR (Etrm (shiftVAR VAR n) t) VAR n) p.
Proof fun p n V t => proj1 (eval_subst_frm_ok p n V t).

Lemma eval_subst_frm_ok2 :
 forall (p : F) (n : nat) (VAR : nat -> A) (t : T),
 E (insertVAR (Etrm (shiftVAR VAR n) t) VAR n) p -> E VAR (subst_frm n p t).
Proof fun p n V t => proj2 (eval_subst_frm_ok p n V t). 


End eval_subst_lemmas.
