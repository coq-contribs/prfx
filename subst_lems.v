(** Proof Reflection in Coq ; subst_lems.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export lift_lems.

Set Implicit Arguments.

Section substitution_lemmas.

Variable l1 l2 : list nat.

Let P := prf l1 l2.
Let F := frm l1 l2.
Let T := trm l1.
Let Ts := trms l1.
Let C := list F.

Lemma simpl_subst_var :
 forall (i n : nat) (t : T), subst_var n (lift n i) t = var _ i.
Proof.
simple induction i; simpl in |- *.
simple destruct n; reflexivity.
intros i' IH n t.
case n.
reflexivity.
intro n'. simpl in |- *.
rewrite (IH n' t).
case i'; reflexivity.
Qed.

Lemma simpl_subst_trm :
 forall (n : nat) (t u : T), subst_trm n (lift_trm n t) u = t.
Proof.
intros n t u.
move t after u. (*!*)
induction t.
simpl in |- *; apply simpl_subst_var.
simpl in |- *.
rewrite mapn_mapn.
set (f := (fun x : trm l1 => subst_trm n (lift_trm n x) u)).
pattern l at 2 in |- *.
rewrite <- (mapn_id (A:=T) (n:=select i) l).
set (g := fun t : T => t) in *.
rewrite (mapn_inn f g l H).
reflexivity.
Qed.

Lemma simpl_subst_trms :
 forall (n z : nat) (l : Ts z) (u : T),
 mapn (fun t => subst_trm n t u) (mapn (lift_trm n) l) = l.
Proof.
intros n z l u.
induction l; simpl in |- *.
reflexivity.
rewrite simpl_subst_trm; rewrite IHl; reflexivity.
Qed.

Lemma simpl_subst_frm :
 forall (p : F) (n : nat) (t : T), subst_frm n (lift_frm n p) t = p.
Proof.
simple induction p; clear p; simpl in |- *.
reflexivity.
reflexivity.
intros i l n t.
rewrite simpl_subst_trms.
reflexivity.
intros p IHp q IHq n t.
rewrite (IHp n t).
rewrite (IHq n t).
reflexivity.
intros p IHp q IHq n t.
rewrite (IHp n t).
rewrite (IHq n t).
reflexivity.
intros p IHp q IHq n t.
rewrite (IHp n t).
rewrite (IHq n t).
reflexivity.
intros p IHp n t.
rewrite (IHp (S n) t).
reflexivity.
intros p IHp n t.
rewrite (IHp (S n) t).
reflexivity.
Qed.

Lemma commute_lift_subst_var :
 forall (i m n : nat) (t : T),
 m <= n -> lift_trm m (subst_var n i t) = subst_var (S n) (lift m i) t.
Proof.
simple induction i.
simple destruct m.
simple destruct n; reflexivity.
intros m' n t.
case n.
intro H. inversion H.
reflexivity.
intros i' IH m n t.
case m.
intro. case n; reflexivity.
intro m'.
case n.
intro H. inversion H.
intros n' H.
simpl in |- *.
rewrite <- (IH m' n' t).
symmetry  in |- *.
apply permute_lift_trm.
exact (le_O_n m').
exact (le_S_n m' n' H).
Qed.

Lemma commute_lift_subst_trm :
 forall (m n : nat) (t u : T),
 m <= n -> lift_trm m (subst_trm n t u) = subst_trm (S n) (lift_trm m t) u.
Proof.
intros m n t u H.
move t after H.
induction t.
simpl in |- *; rewrite (commute_lift_subst_var n0 u H); reflexivity.
simpl in |- *.
rewrite mapn_mapn.
rewrite mapn_mapn.
set (f := fun x : trm l1 => lift_trm m (subst_trm n x u)).
set (g := fun x : trm l1 => subst_trm (S n) (lift_trm m x) u).
rewrite (mapn_inn f g l H0).
reflexivity.
Qed.

Lemma commute_lift_subst_trms :
 forall (m n z : nat) (l : Ts z) (u : T),
 m <= n ->
 mapn (lift_trm m) (mapn (fun t => subst_trm n t u) l) =
 mapn (fun t => subst_trm (S n) t u) (mapn (lift_trm m) l).
Proof.
intros m n z l u h.
induction l; simpl in |- *.
reflexivity.
rewrite commute_lift_subst_trm with (1 := h); rewrite IHl; reflexivity.
Qed.

Lemma commute_lift_subst_frm :
 forall (p : F) (m n : nat) (t : T),
 m <= n -> lift_frm m (subst_frm n p t) = subst_frm (S n) (lift_frm m p) t.
Proof.
simple induction p; clear p; simpl in |- *.
reflexivity.
reflexivity.
intros i l m n t H.
rewrite commute_lift_subst_trms.
reflexivity.
exact H.
intros p IHp q IHq m n t H.
rewrite (IHp m n t H).
rewrite (IHq m n t H).
reflexivity.
intros p IHp q IHq m n t H.
rewrite (IHp m n t H).
rewrite (IHq m n t H).
reflexivity.
intros p IHp q IHq m n t H.
rewrite (IHp m n t H).
rewrite (IHq m n t H).
reflexivity.
intros p IHp m n t H.
rewrite (IHp (S m) (S n) t (le_n_S m n H)).
reflexivity.
intros p IHp m n t H.
rewrite (IHp (S m) (S n) t (le_n_S m n H)).
reflexivity.
Qed.

Lemma commute_lift_subst_cxt :
 forall (G : C) (m n : nat) (t : T),
 m <= n -> lift_cxt m (subst_cxt n G t) = subst_cxt (S n) (lift_cxt m G) t.
Proof.
intros G m n t H.
unfold lift_cxt, subst_cxt in |- *.
rewrite map_map.
rewrite map_map.
apply map_feeg.
intro p.
apply commute_lift_subst_frm.
exact H.
Qed.

Lemma distr_subst_var :
 forall (i m k : nat) (t t' : T),
 subst_trm (m + k) (subst_var m i t) t' =
 subst_trm m (subst_var (S (m + k)) i t') (subst_trm k t t').
Proof.
simple induction i.
simple destruct m; reflexivity.
intros i' IH.
simple destruct m; simpl in |- *.
intros k t t'.
rewrite (simpl_subst_trm 0 (subst_var k i' t') (subst_trm k t t')).
reflexivity.
intros m' k t t'.
rewrite <- (commute_lift_subst_trm (subst_var m' i' t) t' (le_O_n (m' + k))).
rewrite <-
 (commute_lift_subst_trm (subst_var (S (m' + k)) i' t') 
    (subst_trm k t t') (le_O_n m')).
rewrite (IH m' k t t').
reflexivity.
Qed.

Lemma distr_subst_trm :
 forall (t u u' : T) (m k : nat),
 subst_trm (m + k) (subst_trm m t u) u' =
 subst_trm m (subst_trm (S (m + k)) t u') (subst_trm k u u').
Proof.
intros t u u' m k.
move t after k. (*!*)
induction t.
simpl in |- *; rewrite distr_subst_var; reflexivity.
simpl in |- *.
rewrite mapn_mapn.
rewrite mapn_mapn.
set (f := fun t : trm l1 => subst_trm (m + k) (subst_trm m t u) u') in *.
set
 (g :=
  fun t : trm l1 => subst_trm m (subst_trm (S (m + k)) t u') (subst_trm k u u'))
 in *.
rewrite (mapn_inn f g l H).
reflexivity.
Qed.

Lemma distr_subst_trms :
 forall (z : nat) (l : Ts z) (u u' : T) (m k : nat),
 mapn (fun t => subst_trm (m + k) t u') (mapn (fun t => subst_trm m t u) l) =
 mapn (fun t => subst_trm m t (subst_trm k u u'))
   (mapn (fun t => subst_trm (S (m + k)) t u') l).
Proof.
intros z l u u' m k.
induction l; simpl in |- *.
reflexivity.
rewrite distr_subst_trm; rewrite IHl; reflexivity.
Qed.

Lemma distr_subst_frm :
 forall (p : F) (t t' : T) (m k : nat),
 subst_frm (m + k) (subst_frm m p t) t' =
 subst_frm m (subst_frm (S (m + k)) p t') (subst_trm k t t').
Proof.
simple induction p; clear p; simpl in |- *.
reflexivity.
reflexivity.
intros i l t t' m k.
rewrite distr_subst_trms.
reflexivity.
intros p IHp q IHq t t' m k.
rewrite (IHp t t' m k).
rewrite (IHq t t' m k).
reflexivity.
intros p IHp q IHq t t' m k.
rewrite (IHp t t' m k).
rewrite (IHq t t' m k).
reflexivity.
intros p IHp q IHq t t' m k.
rewrite (IHp t t' m k).
rewrite (IHq t t' m k).
reflexivity.
intros p IHp t t' m k.
replace (S (m + k)) with (S m + k).
rewrite (IHp t t' (S m) k).
reflexivity.
reflexivity.
intros p IHp t t' m k.
replace (S (m + k)) with (S m + k).
rewrite (IHp t t' (S m) k).
reflexivity.
reflexivity.
Qed.

(* *)
Let v := var l1.

Lemma subst_var_id : forall n i : nat, subst_var n (lift (S n) i) (v 0) = v i.
Proof.
induction n.
destruct i as [| n]; reflexivity.
destruct i as [| n0].
reflexivity.
rename n0 into i.
assert (e : lift (S (S n)) (S i) = S (lift (S n) i)).
reflexivity.
rewrite e.
assert
 (e' :
  subst_var (S n) (S (lift (S n) i)) (v 0) =
  lift_trm 0 (subst_var n (lift (S n) i) (v 0))).
reflexivity.
rewrite e'.
rewrite IHn; reflexivity.
Qed.

Lemma subst_trm_id :
 forall (n : nat) (t : T), subst_trm n (lift_trm (S n) t) (v 0) = t.
Proof.
induction t.
exact (subst_var_id n n0).
simpl in |- *.
rewrite mapn_mapn.
set (f := fun t : trm l1 => subst_trm n (lift_trm (S n) t) (v 0)) in *.
pattern l at 2 in |- *.
rewrite <- (mapn_id (A:=T) (n:=select i) l).
set (g := fun t : trm l1 => t) in *.
rewrite (mapn_inn f g l H).
reflexivity.
Qed.

Lemma subst_trms_id :
 forall (n z : nat) (l : Ts z),
 mapn (fun t => subst_trm n t (v 0)) (mapn (lift_trm (S n)) l) = l.
Proof.
intros n z l.
induction l; simpl in |- *.
reflexivity.
rewrite subst_trm_id; rewrite IHl; reflexivity.
Qed.

Lemma subst_frm_id :
 forall (p : F) (n : nat), subst_frm n (lift_frm (S n) p) (v 0) = p.
Proof.
simple induction p; clear p; simpl in |- *.
reflexivity.
reflexivity.
intros i l n.
rewrite subst_trms_id.
reflexivity.
intros p IHp q IHq n.
rewrite (IHp n).
rewrite (IHq n).
reflexivity.
intros p IHp q IHq n.
rewrite (IHp n).
rewrite (IHq n).
reflexivity.
intros p IHp q IHq n.
rewrite (IHp n).
rewrite (IHq n).
reflexivity.
intros p IHp n.
rewrite (IHp (S n)).
reflexivity.
intros p IHp n.
rewrite (IHp (S n)).
reflexivity.
Qed.


End substitution_lemmas.

