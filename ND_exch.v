(** Proof Reflection in Coq ; ND_exch.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export ND_subst_lems.
Require Export exch.

Set Implicit Arguments.

Section ND_exchange_rule.

Variable l1 l2 : list nat.

Let T := trm l1.
Let F := frm l1 l2.
Let X := list F.
Let P := prf l1 l2.

Lemma ND_exch_hyp :
 forall (G G' : X) (i : nat) (A B C : F),
 ND (G' ++ B :: A :: G) (hyp _ _ i) C ->
 ND (G' ++ A :: B :: G) (hyp _ _ (exch (length G') i)) C.
Proof.
simple induction G'.
simpl in |- *.
simple destruct i.
simpl in |- *.
intros.
unfold F in |- *. (* ??? *)
apply ND_hypS.
rewrite (hypO_inv H).
apply ND_hypO.
intros i' A B C.
case i'.
simpl in |- *.
intro.
rewrite (hypO_inv (hypS_inv H)).
unfold F in |- *.
apply ND_hypO.
intros i'' H.
simpl in |- *.
unfold F in |- *.
apply ND_hypS.
apply ND_hypS.
exact (hypS_inv (hypS_inv H)).
intros D g' IH i A B C.
simpl in |- *.
case i.
simpl in |- *.
intro.
rewrite (hypO_inv H).
unfold F in |- *.
apply ND_hypO.
intros i' H.
unfold F in |- *.
simpl in |- *.
apply ND_hypS.
apply IH.
exact (hypS_inv H).
Qed.

Lemma ND_exch :
 forall (d : P) (G G' : X) (A B C : F),
 ND (G' ++ B :: A :: G) d C ->
 ND (G' ++ A :: B :: G) (exch_hyp (length G') d) C.
Proof. (*many script lines, due to avoidance of Inversion tactic *)
unfold exch_hyp in |- *.
simple induction d; simpl in |- *; intros.
(*top_intro*)
rewrite (top_inv H).
apply ND_top_intro.
(*hyp*)
apply ND_exch_hyp with (1:=H).
(*bot_elim*)
elim (bot_inv H0).
intros.
rewrite H1.
apply ND_bot_elim.
apply H.
exact H2.
(*imp_intro*)
elim (imp_intro_inv H0).
intros.
elim H1.
intros.
rewrite H2.
apply ND_imp_intro.
simpl in |- *.
exact (H G (f :: G') A B x H3).
(*imp_elim*)
elim (imp_elim_inv H1).
intros.
elim H2.
intros.
cut (ND (G' ++ A :: B :: G) (map_prf_hyp exch (length G') p) (imp x C)).
intro c1.
cut (ND (G' ++ A :: B :: G) (map_prf_hyp exch (length G') p0) x).
intro c2.
exact (ND_imp_elim c1 c2).
apply H0.
exact H4.
apply H.
exact H3.
(*cnj_intro*)
elim (cnj_intro_inv H1).
intros.
elim H2.
intros.
elim H3.
intros.
elim H5.
intros.
rewrite H4.
apply ND_cnj_intro.
apply H.
exact H6.
apply H0.
exact H7.
(*cnj_elim1*)
elim (cnj_elim1_inv H0).
intros.
cut (ND (G' ++ A :: B :: G) (map_prf_hyp exch (length G') p) (cnj C x)).
intro c.
exact (ND_cnj_elim1 c).
apply H.
exact H1.
(*cnj_elim2*)
elim (cnj_elim2_inv H0).
intros.
cut (ND (G' ++ A :: B :: G) (map_prf_hyp exch (length G') p) (cnj x C)).
intro c.
exact (ND_cnj_elim2 c).
apply H.
exact H1.
(*dsj_intro1*)
elim (dsj_intro1_inv H0).
intros.
elim H1.
intros.
rewrite H2.
apply ND_dsj_intro1.
apply H.
exact H3.
(*dsj_intro2*)
elim (dsj_intro2_inv H0).
intros.
elim H1.
intros.
rewrite H2.
apply ND_dsj_intro2.
apply H.
exact H3.
(*dsj_elim*)
elim (dsj_elim_inv H2); intros r1 H3.
elim H3; clear H3; intros r2 H3; elim H3; clear H3; intros H3 H4; elim H4;
 clear H4; intros H4 H5.
assert (c1 := H G G' A B (dsj r1 r2) H3).
assert (c2 := H0 G (r1 :: G') A B C H4).
assert (c3 := H1 G (r2 :: G') A B C H5).
exact (ND_dsj_elim c1 c2 c3).
(*uvq_intro*)
elim (uvq_intro_inv H0).
intros.
elim H1.
clear H1.
intros.
rewrite H1.
apply ND_uvq_intro.
replace (length G') with (length (lift_cxt 0 G')).
unfold lift_cxt in |- *.
simpl in |- *.
rewrite map_app.
simpl in |- *.
apply H.
replace (lift_frm 0 B :: lift_frm 0 A :: map (lift_frm 0) G) with
 (map (lift_frm 0) (B :: A :: G)).
cut (ND (map (lift_frm 0) G' ++ map (lift_frm 0) (B :: A :: G)) p x).
intro c.
exact c.
rewrite <- map_app.
exact H2.
reflexivity.
unfold lift_cxt in |- *.
symmetry  in |- *.
apply length_map.
(*uvq_elim*)
elim (uvq_elim_inv H0).
intros.
elim H1.
clear H1.
intros.
rewrite H1.
apply ND_uvq_elim.
apply H.
exact H2.
(*exq_intro*)
elim (exq_intro_inv H0).
intros.
rewrite H1.
apply ND_exq_intro.
apply H.
exact H2.
(*exq_elim*)
elim (exq_elim_inv H1).
intros r H2; elim H2; clear H2; intros H2 H3.
assert (c1 := H G G' A B (exq r) H2).
assert
 (c2 :
  ND (r :: lift_cxt 0 (G' ++ A :: B :: G))
    (map_prf_hyp exch (S (length G')) p0) (lift_frm 0 C)).
replace (length G') with (length (lift_cxt 0 G')).
unfold lift_cxt in |- *.
rewrite map_app.
apply
 (H0 (lift_cxt 0 G) (r :: lift_cxt 0 G') (lift_frm 0 A) 
    (lift_frm 0 B) (lift_frm 0 C)).
simpl in |- *.
cut
 (ND (r :: lift_cxt 0 G' ++ map (lift_frm 0) (B :: A :: G)) p0 (lift_frm 0 C)).
exact (fun c => c).
unfold lift_cxt in |- *.
rewrite <- map_app.
exact H3.
unfold lift_cxt in |- *.
symmetry  in |- *.
apply length_map.
apply ND_exq_elim with (1:=c1) (2:=c2).
Qed.

End ND_exchange_rule.

