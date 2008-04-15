(** Proof Reflection in Coq ; subst.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export lift.

Set Implicit Arguments.

Section substitution.

Variable l1 l2 : list nat.

Let T := trm l1.
Let Ts := trms l1.
Let F := frm l1 l2.
Let P := prf l1 l2.
Let C := list F.

Section var_substitution.

Fixpoint subst_var (n i : nat) (u : T) {struct i} : T :=
  match n, i with
  | O, O => u
  | O, S i' => var _ i'
  | S n', O => var _ 0
  | S n', S i' => lift_trm 0 (subst_var n' i' u)
  end.

(** The last [n] bound variables are not changed in the substitution. The term [u]
is lifted so that it matches the depth of the position it is placed in. Higher
indices not substited are decremented, since substitution removes one of the
original variables in [t]. *)

Fixpoint subst_trm (n : nat) (t u : T) {struct t} : T :=
  match t with
  | var i => subst_var n i u
  | fun_ i l => fun_ i (mapn (fun t => subst_trm n t u) l)
  end.

Definition subst_trms (n z : nat) (l : Ts z) (u : T) :=
  mapn (fun t => subst_trm n t u) l.

Definition subst_frm (n : nat) (p : F) (u : T) : F :=
  map_frm_var (fun m t => subst_trm m t u) n p.

Definition subst_cxt (n : nat) (G : C) (t : T) :=
  map (fun p => subst_frm n p t) G.

Definition subst_var_prf (n : nat) (d : P) (u : T) : P :=
  map_prf_var (fun m t => subst_trm m t u) n d.

End var_substitution.

Section hyp_substitution.

Fixpoint subst_hyp (n i : nat) (h : P) {struct i} : P :=
  match n, i with
  | O, O => h
  | O, S i' => hyp _ _ i'
  | S n', O => hyp _ _ 0
  | S n', S i' => lift_hyp_prf 0 (subst_hyp n' i' h)
  end.

Fixpoint subst_hyp_prf (n : nat) (d h : P) {struct d} : P :=
  match d with
  | top_intro => top_intro _ _
  | hyp i => subst_hyp n i h
  | bot_elim e p => bot_elim (subst_hyp_prf n e h) p
  | imp_intro p e => imp_intro p (subst_hyp_prf (S n) e h)
  | imp_elim e f => imp_elim (subst_hyp_prf n e h) (subst_hyp_prf n f h)
  | cnj_intro e f => cnj_intro (subst_hyp_prf n e h) (subst_hyp_prf n f h)
  | cnj_elim1 e => cnj_elim1 (subst_hyp_prf n e h)
  | cnj_elim2 e => cnj_elim2 (subst_hyp_prf n e h)
  | dsj_intro1 p e => dsj_intro1 p (subst_hyp_prf n e h)
  | dsj_intro2 p e => dsj_intro2 p (subst_hyp_prf n e h)
  | dsj_elim e f g =>
      dsj_elim (subst_hyp_prf n e h) (subst_hyp_prf (S n) f h)
        (subst_hyp_prf (S n) g h)
  | uvq_intro e => uvq_intro (subst_hyp_prf n e (lift_var_prf 0 h))
  | uvq_elim t e => uvq_elim t (subst_hyp_prf n e h)
  | exq_intro p t e => exq_intro p t (subst_hyp_prf n e h)
  | exq_elim e f =>
      exq_elim (subst_hyp_prf n e h)
        (subst_hyp_prf (S n) f (lift_var_prf 0 h))
  end.

End hyp_substitution.

End substitution.


