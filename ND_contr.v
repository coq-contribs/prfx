(** Proof Reflection in Coq ; ND_contr.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export ND.
Require Export inv_lems.
Require Export contr.

Set Implicit Arguments.

Section ND_contraction_rule.

Variable l1 l2 : list nat.

Let P := prf l1 l2.

Lemma ND_contr_hyp :
 forall (G G' : list (frm l1 l2)) (i : nat) (p q : frm l1 l2),
 ND (G' ++ p :: p :: G) (hyp _ _ i) q ->
 ND (G' ++ p :: G) (hyp _ _ (contr (length G') i)) q.
Proof.
simple induction G'.
simple destruct i.
simpl in |- *.
intros.
rewrite (hypO_inv H).
apply ND_hypO.
intros.
exact (hypS_inv H).
intros a g IH i p q.
case i; simpl in |- *.
intro.
rewrite (hypO_inv H).
apply ND_hypO.
intros i' H.
apply ND_hypS.
apply IH.
exact (hypS_inv H).
Qed.

Lemma ND_contr :
 forall (d : P) (G G' : list (frm l1 l2)) (p q : frm l1 l2),
 ND (G' ++ p :: p :: G) d q -> ND (G' ++ p :: G) (contr_hyp (length G') d) q.
Proof.
unfold contr_hyp in |- *.
induction d; simpl in |- *; intros G G' p q H.
(*top*)
rewrite (top_inv H).
apply ND_top_intro.
(*hyp*)
apply ND_contr_hyp.
exact H.
(*bot_elim*)
elim (bot_inv H).
intros.
rewrite <- H0.
apply ND_bot_elim.
apply IHd.
exact H1.
(*imp_intro*)
elim (imp_intro_inv H).
intros.
elim H0.
intros.
rewrite H1.
apply ND_imp_intro.
exact (IHd G (f :: G') p x H2).
(*imp_elim*)
elim (imp_elim_inv H).
intros.
elim H0.
intros.
cut (ND (G' ++ p :: G) (map_prf_hyp contr (length G') d1) (imp x q)).
intro c1.
cut (ND (G' ++ p :: G) (map_prf_hyp contr (length G') d2) x).
intro c2.
exact (ND_imp_elim c1 c2).
apply IHd2.
exact H2.
apply IHd1.
exact H1.
(*cnj_intro*)
elim (cnj_intro_inv H).
intros.
elim H0.
intros.
elim H1.
intros.
elim H3.
intros.
rewrite H2.
apply ND_cnj_intro.
apply IHd1.
exact H4.
apply IHd2.
exact H5.
(*cnj_elim1*)
elim (cnj_elim1_inv H).
intros.
cut (ND (G' ++ p :: G) (map_prf_hyp contr (length G') d) (cnj q x)).
intro c.
exact (ND_cnj_elim1 c).
apply IHd.
exact H0.
(*cnj_elim2*)
elim (cnj_elim2_inv H).
intros.
cut (ND (G' ++ p :: G) (map_prf_hyp contr (length G') d) (cnj x q)).
intro c.
exact (ND_cnj_elim2 c).
apply IHd.
exact H0.
(*dsj_intro1*)
elim (dsj_intro1_inv H).
intros.
elim H0.
intros.
rewrite H1.
apply ND_dsj_intro1.
apply IHd.
exact H2.
(*dsj_intro2*)
elim (dsj_intro2_inv H).
intros.
elim H0.
intros.
rewrite H1.
apply ND_dsj_intro2.
apply IHd.
exact H2.
(*dsj_elim*)
elim (dsj_elim_inv H); intros.
elim H0; clear H0; intros.
elim H0; clear H0; intros.
elim H1; clear H1; intros.
assert (c1 := IHd1 G G' p (dsj x x0) H0).
assert (c2 := IHd2 G (x :: G') p q H1).
assert (c3 := IHd3 G (x0 :: G') p q H2).
exact (ND_dsj_elim c1 c2 c3).
(*uvq_intro*)
elim (uvq_intro_inv H); intros.
elim H0; clear H0; intros.
rewrite H0.
apply ND_uvq_intro.
replace (length G') with (length (lift_cxt 0 G')).
unfold lift_cxt in |- *.
simpl in |- *.
rewrite map_app.
simpl in |- *.
apply IHd.
replace (lift_frm 0 p :: lift_frm 0 p :: map (lift_frm 0) G) with
 (map (lift_frm 0) (p :: p :: G)).
cut (ND (map (lift_frm 0) G' ++ map (lift_frm 0) (p :: p :: G)) d x).
exact (fun c => c).
rewrite <- map_app.
exact H1.
reflexivity.
unfold lift_cxt in |- *.
symmetry  in |- *.
apply length_map.
(*uvq_elim*)
elim (uvq_elim_inv H); intros.
elim H0; clear H0; intros.
rewrite H0.
apply ND_uvq_elim.
apply IHd.
exact H1.
(*exq_intro*)
elim (exq_intro_inv H); intros.
rewrite H0.
apply ND_exq_intro.
apply IHd.
exact H1.
(*exq_elim*)
elim (exq_elim_inv H); intros.
elim H0; clear H0; intros.
assert (c1 : ND (G' ++ p :: G) (map_prf_hyp contr (length G') d1) (exq x)).
apply IHd1.
exact H0.
assert
 (c2 :
  ND (x :: lift_cxt 0 (G' ++ p :: G)) (map_prf_hyp contr (S (length G')) d2)
    (lift_frm 0 q)).
replace (length G') with (length (lift_cxt 0 G')).
unfold lift_cxt in |- *.
rewrite map_app.
apply
 (IHd2 (lift_cxt 0 G) (x :: lift_cxt 0 G') (lift_frm 0 p) (lift_frm 0 q)).
simpl in |- *.
cut
 (ND (x :: lift_cxt 0 G' ++ map (lift_frm 0) (p :: p :: G)) d2 (lift_frm 0 q)).
exact (fun c => c).
unfold lift_cxt in |- *.
rewrite <- map_app.
exact H1.
unfold lift_cxt in |- *.
symmetry  in |- *.
apply length_map.
apply ND_exq_elim with (1:=c1) (2:=c2).
Qed.

End ND_contraction_rule.

