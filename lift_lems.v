(** Proof Reflection in Coq ; lift_lems.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export lift.
Require Export subst.

Set Implicit Arguments.

Section lifting_lemmas.

Variable l1 l2 : list nat.

Let P := prf l1 l2.
Let F := frm l1 l2.
Let T := trm l1.
Let Ts := trms l1.
Let C := list F.

Lemma permute_lift_var :
 forall n m i : nat, m <= n -> lift m (lift n i) = lift (S n) (lift m i).
Proof.
simple induction n.
(* n=0 *)
intros m i.
case m.
reflexivity.
intros m' H.
inversion H.
(* n=Sn' *)
intros n' IH m i.
case m.
(* m=0 *)
reflexivity.
(* m=Sm' *)
intros m' H.
case i.
reflexivity.
intro i'.
simpl in |- *. apply eq_S.
rewrite (IH m' i').
case (lift m' i'); reflexivity.
inversion H.
exact (le_n n').
apply le_Sn_le.
exact H1.
Qed.

Lemma permute_lift_trm :
 forall (t : T) (n m : nat),
 m <= n -> lift_trm m (lift_trm n t) = lift_trm (S n) (lift_trm m t).
Proof.
intros t n m H.
move t after H. (*!*)
induction t.
simpl in |- *; rewrite permute_lift_var with (1 := H); reflexivity.
simpl in |- *.
rewrite mapn_mapn.
rewrite mapn_mapn.
set (f := (fun x : trm l1 => lift_trm m (lift_trm n x))).
set (g := (fun x : trm l1 => lift_trm (S n) (lift_trm m x))).
rewrite (mapn_inn f g l H0).
reflexivity.
Qed.

Lemma permute_lift_trms :
 forall (z : nat) (l : Ts z) (n m : nat),
 m <= n ->
 mapn (lift_trm m) (mapn (lift_trm n) l) =
 mapn (lift_trm (S n)) (mapn (lift_trm m) l).
Proof.
intros z l n m h.
induction l; simpl in |- *.
reflexivity.
rewrite permute_lift_trm with (1 := h); rewrite IHl; reflexivity.
Qed.

Lemma permute_lift_frm :
 forall (p : F) (n m : nat),
 m <= n -> lift_frm m (lift_frm n p) = lift_frm (S n) (lift_frm m p).
Proof.
simple induction p; clear p; simpl in |- *.
reflexivity.
reflexivity.
intros i l n m h.
rewrite (permute_lift_trms l h).
reflexivity.
intros p IHp q IHq n m H.
rewrite (IHp n m H).
rewrite (IHq n m H).
reflexivity.
intros p IHp q IHq n m H.
rewrite (IHp n m H).
rewrite (IHq n m H).
reflexivity.
intros p IHp q IHq n m H.
rewrite (IHp n m H).
rewrite (IHq n m H).
reflexivity.
intros p IHp n m H.
rewrite (IHp (S n) (S m)).
reflexivity.
apply le_n_S.
exact H.
intros p IHp n m H.
rewrite (IHp (S n) (S m)).
reflexivity.
apply le_n_S.
exact H.
Qed.

Lemma permute_lift_cxt :
 forall (G : C) (n m : nat),
 m <= n -> lift_cxt m (lift_cxt n G) = lift_cxt (S n) (lift_cxt m G).
Proof.
intros G n m H.
unfold lift_cxt in |- *.
rewrite (map_map (lift_frm n) (lift_frm m) G).
rewrite (map_map (lift_frm m) (lift_frm (S n)) G).
apply map_feeg.
exact (fun p => permute_lift_frm p H).
Qed.

Lemma distr_lift_subst_var :
 forall (i m k : nat) (t : T),
 lift_trm (m + k) (subst_var m i t) =
 subst_var m (lift (S (m + k)) i) (lift_trm k t).
Proof.
simple induction i.
intros m k t.
case m; reflexivity.
intros i' IH m k t.
case m.
reflexivity.
intro m'.
simpl in |- *.
rewrite <- (permute_lift_trm (subst_var m' i' t) (le_O_n (m' + k))).
rewrite (IH m' k t).
reflexivity.
Qed.

Lemma distr_lift_subst_trm :
 forall (t : T) (m k : nat) (u : T),
 lift_trm (m + k) (subst_trm m t u) =
 subst_trm m (lift_trm (S (m + k)) t) (lift_trm k u).
Proof.
intros t m k u.
move t after u. (*!*)
induction t.
simpl in |- *; rewrite (distr_lift_subst_var n m k u); reflexivity.
simpl in |- *.
rewrite mapn_mapn.
rewrite mapn_mapn.
set (f := fun t => lift_trm (m + k) (subst_trm m t u)) in *.
set (g := fun t => subst_trm m (lift_trm (S (m + k)) t) (lift_trm k u)) in *.
rewrite (mapn_inn f g l H).
reflexivity.
Qed.

Lemma distr_lift_subst_trms :
 forall (z : nat) (l : Ts z) (m k : nat) (u : T),
 mapn (lift_trm (m + k)) (mapn (fun t => subst_trm m t u) l) =
 mapn (fun t => subst_trm m t (lift_trm k u)) (mapn (lift_trm (S (m + k))) l).
Proof.
intros z l m k u.
induction l; simpl in |- *.
reflexivity.
rewrite distr_lift_subst_trm; rewrite IHl; reflexivity.
Qed.

Lemma distr_lift_subst_frm :
 forall (p : F) (t : T) (m k : nat),
 lift_frm (m + k) (subst_frm m p t) =
 subst_frm m (lift_frm (S (m + k)) p) (lift_trm k t).
Proof.
simple induction p; clear p; simpl in |- *.
reflexivity.
reflexivity.
intros i l t m k.
rewrite (distr_lift_subst_trms l m k t).
reflexivity.
intros p IHp q IHq t m k.
rewrite (IHp t m k).
rewrite (IHq t m k).
reflexivity.
intros p IHp q IHq t m k.
rewrite (IHp t m k).
rewrite (IHq t m k).
reflexivity.
intros p IHp q IHq t m k.
rewrite (IHp t m k).
rewrite (IHq t m k).
reflexivity.
intros p IH t m k.
replace (S (m + k)) with (S m + k).
rewrite (IH t (S m) k).
reflexivity.
reflexivity.
intros p IH t m k.
replace (S (m + k)) with (S m + k).
rewrite (IH t (S m) k).
reflexivity.
reflexivity.
Qed.

Lemma plusO : forall n : nat, 0 + n = n.
Proof.
simple destruct n; reflexivity.
Qed.

Lemma distr_lift_substO_frm :
 forall (p : F) (t : T) (n : nat),
 lift_frm n (subst_frm 0 p t) = subst_frm 0 (lift_frm (S n) p) (lift_trm n t).
Proof.
intros p t n.
pattern n at 1 in |- *.
rewrite <- (plusO n).
exact (distr_lift_subst_frm p t 0 n).
Qed.

Lemma lift_proj_simpl :
 forall n i : nat, nat_eqb n i = false -> lift n (proj n i) = i.
Proof.
induction n; [ destruct i as [| n] | destruct i as [| n0] ].
intro h; inversion h.
reflexivity.
reflexivity.
simpl in |- *.
intro h.
rewrite IHn with (1 := h).
reflexivity.
Qed.

Lemma lift_proj_trm_simpl :
 forall (n : nat) (t : T),
 free_inb_trm n t = false -> lift_trm n (proj_trm n t) = t.
Proof.
induction t; simpl in |- *.
intro h.
rewrite (lift_proj_simpl n n0 h); reflexivity.
intro H0.
rewrite mapn_mapn.
set (f := fun x : trm l1 => lift_trm n (proj_trm n x)) in *.
pattern l at 2 in |- *; rewrite <- (mapn_id l).
set (g := fun x : trm l1 => x) in *.
rewrite (mapn_inn f g l).
reflexivity.
intros x H1.
exact (H x H1 (mapnb_orb_false _ l H0 x H1)).
Qed.

Lemma lift_proj_trms_simpl :
 forall (n k : nat) (l : Ts k),
 free_inb_trms n l = false -> mapn (lift_trm n) (mapn (proj_trm n) l) = l.
Proof.
unfold free_inb_trms, mapn_orb in |- *.
intros n k l h.
induction l; simpl in |- *.
reflexivity.
simpl in h; elim orb_false_elim with (1 := h); intros h0 h1.
rewrite lift_proj_trm_simpl with (1 := h0); rewrite IHl with (1 := h1);
 reflexivity.
Qed.

Lemma lift_proj_frm_simpl :
 forall (p : F) (n : nat),
 free_inb_frm n p = false -> lift_frm n (proj_frm n p) = p.
Proof.
induction p; simpl in |- *; intros n h.
reflexivity.
reflexivity.
rewrite lift_proj_trms_simpl with (1 := h); reflexivity.
elim orb_false_elim with (1 := h); intros h1 h2.
rewrite (IHp1 n h1); rewrite (IHp2 n h2); reflexivity.
elim orb_false_elim with (1 := h); intros h1 h2.
rewrite (IHp1 n h1); rewrite (IHp2 n h2); reflexivity.
elim orb_false_elim with (1 := h); intros h1 h2.
rewrite (IHp1 n h1); rewrite (IHp2 n h2); reflexivity.
rewrite (IHp (S n) h); reflexivity.
rewrite (IHp (S n) h); reflexivity.
Qed.

Lemma proj_lift_simpl : forall n i : nat, proj n (lift n i) = i.
Proof.
induction n.
reflexivity.
destruct i as [| n0].
reflexivity.
simpl in |- *; rewrite IHn; reflexivity.
Qed.

Lemma proj_lift_trm_simpl :
 forall (n : nat) (t : T), proj_trm n (lift_trm n t) = t.
Proof.
induction t; simpl in |- *.
rewrite proj_lift_simpl; reflexivity.
simpl in |- *.
rewrite mapn_mapn.
set (f := fun x : trm l1 => proj_trm n (lift_trm n x)) in *.
pattern l at 2 in |- *; rewrite <- (mapn_id l).
set (g := fun x : trm l1 => x) in *.
rewrite (mapn_inn f g l H).
reflexivity.
Qed.

Lemma proj_lift_trms_simpl :
 forall (n k : nat) (l : Ts k), mapn (proj_trm n) (mapn (lift_trm n) l) = l.
Proof.
induction l; simpl in |- *.
reflexivity.
rewrite proj_lift_trm_simpl; rewrite IHl; reflexivity.
Qed.

Lemma proj_lift_frm_simpl :
 forall (p : F) (n : nat), proj_frm n (lift_frm n p) = p.
Proof.
induction p; simpl in |- *; intro n.
reflexivity.
reflexivity.
rewrite proj_lift_trms_simpl; reflexivity.
rewrite IHp1; rewrite IHp2; reflexivity.
rewrite IHp1; rewrite IHp2; reflexivity.
rewrite IHp1; rewrite IHp2; reflexivity.
rewrite IHp; reflexivity.
rewrite IHp; reflexivity.
Qed.

Lemma not_free_lift : forall n m : nat, nat_eqb n (lift n m) = false.
Proof.
induction n.
reflexivity.
destruct m as [| n0].
reflexivity.
simpl in |- *; apply IHn.
Qed.

Lemma not_free_lift_trm :
 forall (n : nat) (t : T), free_inb_trm n (lift_trm n t) = false.
Proof.
intros n t.
apply
 (trm_ind' (l1:=l1) (fun t => free_inb_trm n (lift_trm n t) = false)
    (fun (k : nat) (l : Ts k) => free_inb_trms n (lift_trms n l) = false));
 clear t; simpl in |- *.
intro i; apply not_free_lift.
intros i l h; exact h.
reflexivity.
intros k t h l h0.
unfold free_inb_trms, mapn_orb in |- *; simpl in |- *.
apply orb_false_intro.
exact h.
exact h0.
Qed.

Lemma not_free_lift_trms :
 forall (n k : nat) (l : Ts k), free_inb_trms n (mapn (lift_trm n) l) = false.
Proof.
induction l.
reflexivity.
unfold free_inb_trms, mapn_orb in |- *; simpl in |- *.
apply orb_false_intro.
apply not_free_lift_trm.
exact IHl.
Qed.

Lemma not_free_lift_frm :
 forall (p : F) (n : nat), free_inb_frm n (lift_frm n p) = false.
Proof.
induction p; simpl in |- *; intro n.
reflexivity.
reflexivity.
apply not_free_lift_trms.
apply orb_false_intro.
apply IHp1.
apply IHp2.
apply orb_false_intro.
apply IHp1.
apply IHp2.
apply orb_false_intro.
apply IHp1.
apply IHp2.
apply IHp.
apply IHp.
Qed.

End lifting_lemmas.
