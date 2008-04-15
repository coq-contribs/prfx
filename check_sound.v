(** Proof Reflection in Coq ; check_sound.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export check.
Require Export ND.
Require Export lift_lems.

Set Implicit Arguments.

Section soundcheck.

Variable l1 l2 : list nat.

Let T := trm l1.
Let Ts := trms l1.
Let F := frm l1 l2.
Let P := prf l1 l2.

Remark andb_intro :
 forall b b' : bool, b = true -> b' = true -> b && b' = true.
Proof.
intros b b' H H'. rewrite H. rewrite H'. reflexivity.
Qed.

Lemma trm_eqb_refl : forall t : T, trm_eqb t t = true.
Proof.
fix 1.
destruct t.
simpl in |- *; rewrite nat_eqb_refl; reflexivity.
simpl in |- *.
rewrite index_eqb_refl.
induction l.
reflexivity.
simpl in |- *.
rewrite trm_eqb_refl.
rewrite IHl.
reflexivity.
Qed.

Lemma trms_eqb_refl : forall (n : nat) (l : Ts n), trms_eqb l l = true.
Proof.
intros n l.
induction l; simpl in |- *.
reflexivity.
rewrite trm_eqb_refl; rewrite IHl; reflexivity.
Qed.

Lemma frm_eqb_refl : forall p : F, frm_eqb p p = true.
Proof.
simple induction p.
reflexivity.
reflexivity.
intros i l.
exact (andb_intro (index_eqb_refl l2 i) (trms_eqb_refl l)).
intros. simpl in |- *. apply andb_intro; assumption.
intros. simpl in |- *. apply andb_intro; assumption.
intros. simpl in |- *. apply andb_intro; assumption.
intros. assumption.
intros. assumption.
Qed.

Lemma trm_eqb_dec : forall t1 t2 : T, trm_eqb t1 t2 = true -> t1 = t2.
Proof.
intros t1 t2 H.
apply
 (trm_ind' (l1:=l1)
    (fun t1 => forall t2 : T, trm_eqb t1 t2 = true -> t1 = t2)
    (fun n l => forall l0 : Ts n, trms_eqb l l0 = true -> l = l0))
  with (5 := H); clear H t1 t2.
destruct t2.
simpl in |- *; intro h.
rewrite nat_eqb_dec with (1 := h); reflexivity.
intro h; discriminate h.
intros i l h.
destruct t2.
intro h0; discriminate h0.
simpl in |- *.
intro h0.
elim andb_prop with (1 := h0).
intro h1.
assert (h2 := index_eqb_dec l1 i i0 h1).
generalize l0.
clear l0 h0.
dependent rewrite <- h2.
intros l0 h3.
rewrite (h l0 h3); reflexivity.
simpl in |- *.
intros l0 h.
rewrite (eq_niln l0).
reflexivity.
intros n t1 H l H0 w.
elim (eq_consn w).
intros t2 H1.
elim H1.
intros w' H2.
rewrite H2.
simpl in |- *; intro H3.
elim andb_prop with (1 := H3).
intros H4 H5.
rewrite (H t2 H4).
rewrite (H0 w' H5).
reflexivity.
Qed.

Lemma trms_eqb_dec :
 forall (n : nat) (l l0 : Ts n), trms_eqb l l0 = true -> l = l0.
Proof.
simple induction l.
intros w H.
symmetry  in |- *.
rewrite (eq_niln w).
reflexivity.
intros n' t1 l' IH w.
elim (eq_consn w).
intros t2 H.
elim H.
intros w' H0.
rewrite H0.
intro H1.
elim (andb_prop _ _ H1).
simpl in |- *.
intros H2 H3.
rewrite (trm_eqb_dec t1 t2 H2).
rewrite (IH w' H3).
reflexivity.
Qed.

Lemma frm_eqb_dec : forall p q : F, frm_eqb p q = true -> p = q.
Proof.
simple induction p; simple destruct q; auto; try (intros; discriminate);
 clear p q; simpl in |- *.
intros j w H.
elim (andb_prop _ _ H).
intros H1 H2.
cut (i = j).
intro c.
generalize w H2.
clear H2 H1 H w.
dependent rewrite <- c.
intros w H2.
rewrite (trms_eqb_dec t w H2).
reflexivity.
exact (index_eqb_dec l2 i j H1).
intros p q H1.
elim (andb_prop _ _ H1).
intros H2 H3.
rewrite (H p H2).
rewrite (H0 q H3).
reflexivity.
intros p q H1.
elim (andb_prop _ _ H1).
intros H2 H3.
rewrite (H p H2).
rewrite (H0 q H3).
reflexivity.
intros p q H1.
elim (andb_prop _ _ H1).
intros H2 H3.
rewrite (H p H2).
rewrite (H0 q H3).
reflexivity.
intros p H0.
rewrite (H p H0).
reflexivity.
intros p H0.
rewrite (H p H0).
reflexivity.
Qed.


Lemma ND_hyp_nth :
 forall (n : nat) (G : list F) (p : F),
 opt_nth n G = val p -> ND G (hyp _ _ n) p.
Proof.
simple induction n; simple destruct G.
intros. discriminate.
intros p g q H.
injection H; intro H0; rewrite H0.
apply (ND_hypO g).
intros. discriminate.
intros p g q H0.
exact (ND_hypS p (H g q H0)).
Qed.

(* check is sound w.r.t. ND *)

Lemma check2ND :
 forall (d : P) (G : list F) (p : F), check G d = val p -> ND G d p.
Proof.
simple induction d; clear d.

(* top_intro *)
intros G p H.
inversion_clear H.
simpl in |- *.
apply ND_top_intro.

(* hyp *)
exact ND_hyp_nth.

(* bot_elim *)
intros d IHd p G p'.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intro q.
case q; try (intros; discriminate).
intros Hd H.
inversion_clear H.
exact (ND_bot_elim p' (IHd G (bot _ _) Hd)).

(* imp_intro *)
intros p d IHd G p2q.
simpl in |- *.
cut (check (p :: G) d = check (p :: G) d);
 [ pattern (check (p :: G) d) at -1 in |- *; case (check (p :: G) d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros q Hd H.
inversion_clear H.
apply ND_imp_intro.
apply IHd.
exact Hd.

(* imp_elim *)
intros d IHd e IHe G q.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intro r. case r; try (intros; discriminate).
(* r = (Imp p q') *)
intros p q' Hd.
cut (check G e = check G e);
 [ pattern (check G e) at -1 in |- *; case (check G e);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros p' He.
cut (frm_eqb p p' = frm_eqb p p');
 [ pattern (frm_eqb p p') at -1 in |- *; case (frm_eqb p p');
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros H H0.
injection H0.
intro H1.
rewrite <- H1.
apply ND_imp_elim with (2 := IHe G p' He).
rewrite <- (frm_eqb_dec p p' H).
exact (IHd G (imp p q') Hd).

(* cnj_intro *)
intros d IHd e IHe G pandq.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros p Hd.
cut (check G e = check G e);
 [ pattern (check G e) at -1 in |- *; case (check G e);
    [ idtac | intros; discriminate ]
 | reflexivity ].
simpl in |- *.
intros q He H.
injection H.
intro H0.
rewrite <- H0.
exact (ND_cnj_intro (IHd G p Hd) (IHe G q He)).

(* cnj_elim1 *)
intros d IHd G p.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intro pandq.
case pandq; try (intros; discriminate).
intros p' q Hd H.
injection H.
intro H0.
rewrite <- H0.
exact (ND_cnj_elim1 (IHd G (cnj p' q) Hd)).

(* cnj_elim2 *)
intros d IHd G q.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intro pandq.
case pandq; try (intros; discriminate).
intros p q' Hd H.
injection H.
intro H0.
rewrite <- H0.
exact (ND_cnj_elim2 (IHd G (cnj p q') Hd)).

(* dsj_intro1 *)
intros q d IHd G porq.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros p Hd H.
inversion H.
exact (ND_dsj_intro1 q (IHd G p Hd)).

(* dsj_intro2 *)
intros p d IHd G porq.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros q Hd H.
inversion H.
exact (ND_dsj_intro2 p (IHd G q Hd)).

(* dsj_elim *)
intros d IHd e IHe f IHf G c.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intro porq.
case porq; try (intros; discriminate).
intros p q Hd.
cut (check (p :: G) e = check (p :: G) e);
 [ pattern (check (p :: G) e) at -1 in |- *; case (check (p :: G) e);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros c1 He.
cut (check (q :: G) f = check (q :: G) f);
 [ pattern (check (q :: G) f) at -1 in |- *; case (check (q :: G) f);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros c2 Hf.
cut (frm_eqb c1 c2 = frm_eqb c1 c2);
 [ pattern (frm_eqb c1 c2) at -1 in |- *; case (frm_eqb c1 c2);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros H H0; injection H0; intro H1.
rewrite <- (frm_eqb_dec c1 c2 H) in Hf.
rewrite <- H1.
exact
 (ND_dsj_elim (IHd G (dsj p q) Hd) (IHe (p :: G) c1 He) (IHf (q :: G) c1 Hf)).

(* uvq_intro *)
intros d IHd G allp.
simpl in |- *.
cut (check (lift_cxt 0 G) d = check (lift_cxt 0 G) d);
 [ pattern (check (lift_cxt 0 G) d) at -1 in |- *;
    case (check (lift_cxt 0 G) d); [ idtac | intros; discriminate ]
 | reflexivity ].
intros p Hd H.
inversion_clear H.
apply ND_uvq_intro with (1:=IHd (lift_cxt 0 G) p Hd).
(* uvq_elim *)
intros t d IHd G p.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intro allp.
case allp; try (intros; discriminate).
intros p' Hd H.
inversion_clear H.
exact (ND_uvq_elim t (IHd G (uvq p') Hd)).

(* exq_intro *)
intros p t d IHd G exp.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].
intros p' Hd.
cut (frm_eqb (subst_frm 0 p t) p' = frm_eqb (subst_frm 0 p t) p');
 [ pattern (frm_eqb (subst_frm 0 p t) p') at -1 in |- *;
    case (frm_eqb (subst_frm 0 p t) p'); [ idtac | intros; discriminate ]
 | reflexivity ].
intros H H0.
inversion_clear H0.
rewrite <- (frm_eqb_dec (subst_frm 0 p t) p' H) in Hd.
apply ND_exq_intro with (1:=IHd G (subst_frm 0 p t) Hd).

(* exq_elim *)
intros d IHd e IHe G p.
simpl in |- *.
cut (check G d = check G d);
 [ pattern (check G d) at -1 in |- *; case (check G d);
    [ idtac | intros; discriminate ]
 | reflexivity ].

intro p''.
case p''; try (intros; discriminate).
intros q Hd.
cut (check (q :: lift_cxt 0 G) e = check (q :: lift_cxt 0 G) e);
 [ pattern (check (q :: lift_cxt 0 G) e) at -1 in |- *;
    case (check (q :: lift_cxt 0 G) e); [ idtac | intros; discriminate ]
 | reflexivity ].
clear p''.
intros p'' He.
cut (free_inb_frm 0 p'' = free_inb_frm 0 p'');
 [ pattern (free_inb_frm 0 p'') at -1 in |- *; case (free_inb_frm 0 p'')
 | reflexivity ].
intros h h0; discriminate h0.
intros h h0.
injection h0; intro h1.
rewrite <- h1.
rewrite <- (lift_proj_frm_simpl p'' 0 h) in He.
apply ND_exq_elim with
  (1:=IHd G (exq q) Hd)
  (2:=IHe (q :: lift_cxt 0 G) (lift_frm 0 (proj_frm 0 p'')) He).

Qed.


(* check is complete w.r.t. ND *)

Lemma ND2check :
 forall (d : P) (G : list F) (p : F), ND G d p -> check G d = val p.
Proof.
intros d G p H.
elim H; clear H d G p; simpl in |- *.

(* top_intro *)
reflexivity.

(* hypO *)
reflexivity.

(* hypS *)
trivial.

(* bot_elim *)
intros G d p Hd IHd.
rewrite IHd.
reflexivity.

(* imp_intro *)
intros G d p q Hd IHd.
rewrite IHd.
reflexivity.

(* imp_elim *)
intros G d e p q Hd IHd He IHe.
rewrite IHd.
rewrite IHe.
rewrite (frm_eqb_refl p).
reflexivity.

(* cnj_intro *)
intros G d e p q Hd IHd He IHe.
rewrite IHd.
rewrite IHe.
reflexivity.

(* cnj_elim1 *)
intros G d p q Hd IHd.
rewrite IHd.
reflexivity.

(* cnj_elim2 *)
intros G d p q Hd IHd.
rewrite IHd.
reflexivity.

(* dsj_intro1 *)
intros G d p q Hd IHd.
rewrite IHd.
reflexivity.

(* dsj_intro2 *)
intros G d p q Hd IHd.
rewrite IHd.
reflexivity.

(* dsj_elim *)
intros G d e f p q r Hd IHd He IHe Hf IHf.
rewrite IHd.
rewrite IHe.
rewrite IHf.
rewrite (frm_eqb_refl r).
reflexivity.

(* uvq_intro *)
intros G d p Hd IHd.
rewrite IHd.
reflexivity.

(* uvq_elim *)
intros G d t p Hd IHd.
rewrite IHd.
reflexivity.

(* exq_intro *)
intros G d t p Hd IHd.
rewrite IHd.
rewrite (frm_eqb_refl (subst_frm 0 p t)).
reflexivity.

(* exq_elim *)
intros G d e p q Hd IHd He IHe.
rewrite IHd.
rewrite IHe.
rewrite not_free_lift_frm.
rewrite proj_lift_frm_simpl; reflexivity.

Qed.


End soundcheck.

