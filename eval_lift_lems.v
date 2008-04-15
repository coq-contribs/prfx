(** Proof Reflection in Coq ; eval_lift_lems.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export eval.
Require Export lift.

Set Implicit Arguments.

Section eval_lift_lemmas.

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

Lemma insVARswap :
 forall (x y : A) (n : nat) (VAR : nat -> A) (m : nat),
 insertVAR_O x (insertVAR y VAR n) m =
 insertVAR y (insertVAR_O x VAR) (S n) m.
Proof.
simple destruct n; simple destruct m.
reflexivity.
intro m'. case m'; reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma insVAR_shift :
 forall (x : A) (n : nat) (V : nat -> A) (i : nat),
 shiftVAR (insertVAR_O x V) (S n) i = shiftVAR V n i.
Proof.
simple destruct n; reflexivity.
Qed.

Lemma shiftVAR_lift_trm_O :
 forall (VAR : nat -> A) (t : T),
 Etrm VAR (lift_trm 0 t) = Etrm (fun n => VAR (S n)) t.
Proof.
fix 2.
destruct t.
reflexivity.
simpl in |- *.
rewrite mapn_mapn.
assert
 (h0 :
  mapn (fun t : T => Etrm VAR (lift_trm 0 t)) l =
  mapn (Etrm (fun n : nat => VAR (S n))) l).
induction l.
reflexivity.
simpl in |- *; rewrite IHl; rewrite shiftVAR_lift_trm_O; reflexivity.
apply (f_equal (A:=listn A (select i)) (B:=A)).
exact h0.
Qed.

Lemma shiftVAR_lift_trms_O :
 forall (VAR : nat -> A) (k : nat) (l : Ts k),
 eval_trms FUN VAR (lift_trms 0 l) = eval_trms FUN (fun n => VAR (S n)) l.
Proof.
intros V k l.
induction l; simpl in |- *.
reflexivity.
rewrite shiftVAR_lift_trm_O; rewrite IHl; reflexivity.
Qed.

Lemma VARexteq_eval_trm :
 forall VAR VAR' : nat -> A,
 (forall n : nat, VAR n = VAR' n) -> forall t : T, Etrm VAR t = Etrm VAR' t. 
Proof. 
intros V V' h.
induction t.
exact (h n).
simpl in |- *.
rewrite mapn_inn with (1:=H).
reflexivity.
Qed.

Lemma VARexteq_eval_trms :
 forall VAR VAR' : nat -> A,
 (forall n : nat, VAR n = VAR' n) ->
 forall (k : nat) (l : Ts k), eval_trms FUN VAR l = eval_trms FUN VAR' l.
Proof.
intros V V' h k l.
induction l; simpl in |- *.
reflexivity.
rewrite VARexteq_eval_trm with (1 := h); rewrite IHl; reflexivity.
Qed.

Definition piffp (p : Prop) : p <-> p := conj (fun h => h) (fun h => h).

Lemma VARexteq_eval_frm :
 forall (p : F) (VAR VAR' : nat -> A),
 (forall n : nat, VAR n = VAR' n) -> (E VAR p <-> E VAR' p).
Proof.
simple induction p; clear p.
intros. apply piffp.
intros. apply piffp.
intros i l V V' H.
simpl in |- *.
rewrite VARexteq_eval_trms with (1:=H).
apply piffp.
intros p IHp q IHq V V' H.
elim (IHq V V' H); elim (IHp V V' H); intros IHp1 IHp2 IHq1 IHq2.
simpl in |- *; split; intros H0 H1.
exact (IHq1 (H0 (IHp2 H1))).
exact (IHq2 (H0 (IHp1 H1))).
intros p IHp q IHq V V' H.
elim (IHq V V' H); elim (IHp V V' H); intros IHp1 IHp2 IHq1 IHq2.
split; intro H0; elim H0; intros H1 H2; split.
exact (IHp1 H1).
exact (IHq1 H2).
exact (IHp2 H1).
exact (IHq2 H2).
intros p IHp q IHq V V' H.
elim (IHq V V' H); elim (IHp V V' H); intros IHp1 IHp2 IHq1 IHq2.
split; intro H0; elim H0; intro H1.
left. exact (IHp1 H1).
right. exact (IHq1 H1).
left. exact (IHp2 H1).
right. exact (IHq2 H1).
intros p IH V V' H. simpl in |- *.
split; intros H0 x.
elim (IH (insertVAR_O x V) (insertVAR_O x V'));
 [ intros IH1 IH2
 | simple destruct n; [ reflexivity | intro n'; simpl in |- *; apply H ] ].
exact (IH1 (H0 x)).
elim (IH (insertVAR_O x V) (insertVAR_O x V'));
 [ intros IH1 IH2
 | simple destruct n; [ reflexivity | intro n'; simpl in |- *; apply H ] ].
exact (IH2 (H0 x)).
intros p IH V V' H. simpl in |- *.
split; intros H0; elim H0; intros x H1; exists x.
elim (IH (insertVAR_O x V) (insertVAR_O x V'));
 [ intros IH1 IH2
 | simple destruct n; [ reflexivity | intro n'; simpl in |- *; apply H ] ].
exact (IH1 H1).
elim (IH (insertVAR_O x V) (insertVAR_O x V'));
 [ intros IH1 IH2
 | simple destruct n; [ reflexivity | intro n'; simpl in |- *; apply H ] ].
exact (IH2 H1).
Qed.

Lemma thinning_eval_var :
 forall (n i : nat) (x : A) (VAR : nat -> A),
 VAR i = insertVAR x VAR n (lift n i).
Proof.
simple induction n.
reflexivity.
intros n' IH i x VAR. case i.
reflexivity.
intro i'. exact (IH i' x (fun p => VAR (S p))).
Qed.

Lemma thinning_eval_trm :
 forall (x : A) (VAR : nat -> A) (n : nat) (t : T),
 Etrm VAR t = Etrm (insertVAR x VAR n) (lift_trm n t).
Proof.
intros x V n.
induction t.
exact (thinning_eval_var n n0 x V).
simpl in |- *.
rewrite mapn_mapn.
set (g := fun t => Etrm (insertVAR x V n) (lift_trm n t)) in *.
rewrite (mapn_inn (Etrm V) g l H).
reflexivity.
Qed.

Lemma thinning_eval_trms :
 forall (x : A) (k : nat) (l : Ts k) (n : nat) (VAR : nat -> A),
 eval_trms FUN VAR l = eval_trms FUN (insertVAR x VAR n) (lift_trms n l).
Proof.
intros x k l n V.
induction l; simpl in |- *.
reflexivity.
rewrite <- thinning_eval_trm; rewrite <- IHl; reflexivity.
Qed.

Lemma thinning_eval_frm :
 forall (p : F) (x : A) (VAR : nat -> A) (n : nat),
 E VAR p <-> E (insertVAR x VAR n) (lift_frm n p).
Proof.
simple induction p; clear p; simpl in |- *.
(*top*) intros. apply piffp.
(*bot*) intros. apply piffp.
(*rel i l*) intros i l x VAR n.
rewrite (thinning_eval_trms x l n VAR).
apply piffp.
(*imp p q*) intros p IHp q IHq x VAR n.
elim (IHp x VAR n); intros.
elim (IHq x VAR n); intros.
split; intros; auto.
(*cnj p q*) intros p IHp q IHq x VAR n.
elim (IHp x VAR n); intros.
elim (IHq x VAR n); intros.
split; intro H3; elim H3; split; intros; auto.
(*dsj p q*) intros p IHp q IHq x VAR n.
elim (IHp x VAR n); intros.
elim (IHq x VAR n); intros.
split; intro H3; elim H3; auto.
(*uvq p*) intros p IHp x VAR n.
split; intros H y; elim (IHp x (insertVAR_O y VAR) (S n)); intros IH1 IH2;
 elim
  (VARexteq_eval_frm
     (lift_frm (S n) p)
     (insertVAR_O y (insertVAR x VAR n))
     (insertVAR x (insertVAR_O y VAR)(S n))
     (insVARswap y x n VAR)); intros H0 H1.
apply H1. apply IH1. apply H.
apply IH2. apply H0. apply H.
(*exq p*) intros p IHp x VAR n.
split; intro H; elim H; intros y H0; exists y;
 elim (IHp x (insertVAR_O y VAR) (S n)); intros IH1 IH2;
 elim
  (VARexteq_eval_frm
     (lift_frm (S n) p)
     (insertVAR_O y (insertVAR x VAR n))
     (insertVAR x (insertVAR_O y VAR)(S n))
     (insVARswap y x n VAR)); intros H1 H2.
apply H2. apply IH1. exact H0.
apply IH2. apply H1. exact H0.
Qed.

Lemma thinning_eval_frm1 :
 forall (p : F) (x : A) (VAR : nat -> A) (n : nat),
 E VAR p -> E (insertVAR x VAR n) (lift_frm n p).
Proof fun p x V n => proj1 (thinning_eval_frm p x V n).

Lemma thinning_eval_frm2 :
 forall (p : F) (x : A) (VAR : nat -> A) (n : nat),
 E (insertVAR x VAR n) (lift_frm n p) -> E VAR p.
Proof fun p x V n => proj2 (thinning_eval_frm p x V n).

Lemma thinning_eval_cxt_O :
 forall (x : A) (G : C) (VAR : nat -> A),
 Ecxt VAR G -> Ecxt (insertVAR_O x VAR) (lift_cxt 0 G).
Proof.
simple induction G.
trivial.
intros p G' IH V H.
elim H.
intros H0 H1.
split.
exact (thinning_eval_frm1 p x V 0 H0).
exact (IH V H1).
Qed.

End eval_lift_lemmas.





