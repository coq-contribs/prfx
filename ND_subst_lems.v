(** Proof Reflection in Coq ; ND_subst_lems.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export ND_lift_lems.

Set Implicit Arguments.

Section ND_substitution_lemmas.

Variable l1 l2 : list nat.

Let P := prf l1 l2.
Let F := frm l1 l2.
Let T := trm l1.
Let Ts := trms l1.
Let C := list F.

Lemma subst_var_hyp_ok :
 forall (i n : nat) (G D : C) (p : F) (t : T),
 ND (D ++ lift_cxt n G) (hyp _ _ i) p ->
 ND (subst_cxt n D t ++ G) (hyp _ _ i) (subst_frm n p t).
Proof.
simple induction i.
(*i=O*)
intros n G D p t.
case D; simpl in |- *.
(*D=nil*)
case G; simpl in |- *.
(*G=nil*)
intro H.
elim (nohyp_inv H).
(*G=q,G'*)
intros q G' H.
rewrite (hypO_inv H).
rewrite simpl_subst_frm.
exact (ND_hypO G' q).
(*D=q,D'*)
intros q D' H.
rewrite (hypO_inv H).
exact (ND_hypO (subst_cxt n D' t ++ G) (subst_frm n q t)).
(*i=Si'*)
intros i' IH n G D p t.
case D; simpl in |- *.
(*D=nil*)
case G; simpl in |- *.
(*G=nil*)
intro H.
elim (nohyp_inv H).
(*G=q,G'*)
intros q G' H.
cut (ND G' (hyp _ _ i') (subst_frm n p t)).
exact (fun h => ND_hypS q h).
exact (IH n G' nil p t (hypS_inv H)).
(*D=q,D'*)
intros q D' H.
cut (ND (subst_cxt n D' t ++ G) (hyp _ _ i') (subst_frm n p t)).
exact (fun h => ND_hypS (subst_frm n q t) h).
exact (IH n G D' p t (hypS_inv H)).
Qed.



Lemma subst_var_prf_ok :
 forall (d : P) (n : nat) (G D : C) (p : F) (t : T),
 ND (D ++ lift_cxt n G) d p ->
 ND (subst_cxt n D t ++ G) (subst_var_prf n d t) (subst_frm n p t).
Proof.
simple induction d; clear d; simpl in |- *.
(*top+*)
intros n G D p t H.
rewrite (top_inv H).
simpl in |- *.
apply ND_top_intro.
(*hyp i*)
exact subst_var_hyp_ok.
(*bot-*)
intros d IHd q n G D p t H.
elim (bot_inv H).
intros H1 H2.
rewrite H1.
apply ND_bot_elim.
exact (IHd n G D (bot _ _) t H2).
(*imp+*)
intros q d IHd n G D p t H.
elim (imp_intro_inv H).
intros r H0.
elim H0.
intros H1 H2.
rewrite H1.
simpl in |- *.
apply ND_imp_intro.
exact (IHd n G (q :: D) r t H2).
(*imp-*)
intros d IHd e IHe n G D p t H.
elim (imp_elim_inv H).
intros r H0.
elim H0.
intros H1 H2.
exact (ND_imp_elim (IHd n G D (imp r p) t H1) (IHe n G D r t H2)).
(*cnj+*)
intros d IHd e IHe n G D p t H.
(* e.g. the next 9 lines  iso. "Inversion H." *)
elim (cnj_intro_inv H).
intros p1 H0.
elim H0.
intros p2 H1.
elim H1.
intros H2 H3.
elim H3.
intros H4 H5.
rewrite H2.
exact (ND_cnj_intro (IHd n G D p1 t H4) (IHe n G D p2 t H5)).
(*cnj-1*)
intros d IHd n G D p t H.
elim (cnj_elim1_inv H).
intros q H0.
exact (ND_cnj_elim1 (IHd n G D (cnj p q) t H0)).
(*cnj-2*)
intros d IHd n G D p t H.
elim (cnj_elim2_inv H).
intros q H0.
exact (ND_cnj_elim2 (IHd n G D (cnj q p) t H0)).
(*dsj+1*)
intros q d IHd n G D p t H.
elim (dsj_intro1_inv H).
intros r H0.
elim H0.
intros H1 H2.
rewrite H1.
exact (ND_dsj_intro1 (subst_frm n q t) (IHd n G D r t H2)).
(*dsj+2*)
intros q d IHd n G D p t H.
elim (dsj_intro2_inv H).
intros r H0.
elim H0.
intros H1 H2.
rewrite H1.
exact (ND_dsj_intro2 (subst_frm n q t) (IHd n G D r t H2)).
(*dsj-*)
intros d IHd e IHe f IHf n G D p t H.
elim (dsj_elim_inv H).
intros r1 H0; elim H0; clear H0; intros r2 H0; elim H0; clear H0;
 intros H0 H1; elim H1; clear H1; intros H1 H2.
exact
 (ND_dsj_elim (IHd n G D (dsj r1 r2) t H0) (IHe n G (r1 :: D) p t H1)
    (IHf n G (r2 :: D) p t H2)).
(*uvq+*)
intros d IHd n G D p t H.
elim (uvq_intro_inv H).
intros q H0.
elim H0.
intros H1 H2.
rewrite H1.
simpl in |- *.
apply ND_uvq_intro.
replace (lift_cxt 0 (subst_cxt n D t ++ G)) with
 (subst_cxt (S n) (lift_cxt 0 D) t ++ lift_cxt 0 G).
replace (lift_cxt 0 (subst_cxt n D t ++ G)) with
 (subst_cxt (S n) (lift_cxt 0 D) t ++ lift_cxt 0 G).
apply (IHd (S n) (lift_cxt 0 G) (lift_cxt 0 D) q t).
rewrite <- permute_lift_cxt.
unfold lift_cxt in |- *.
rewrite <- map_app.
exact H2.
exact (le_O_n n).
rewrite <- commute_lift_subst_cxt.
unfold lift_cxt in |- *.
rewrite map_app.
reflexivity.
exact (le_O_n n).
rewrite <- commute_lift_subst_cxt.
unfold lift_cxt in |- *.
rewrite map_app.
reflexivity.
exact (le_O_n n).
(*uvq-*)
intros t d IHd n G D p u H.
elim (uvq_elim_inv H).
intros q H0.
elim H0.
intros H1 H2.
rewrite H1.
pattern n at 4 in |- *.
rewrite <- (plusO n).
rewrite (distr_subst_frm q t u 0 n).
apply ND_uvq_elim.
rewrite (plusO n).
exact (IHd n G D (uvq q) u H2).
(*exq+*)
intros q t d IHd n G D p u H.
elim (exq_intro_inv H).
intros H0 H1.
rewrite H0.
simpl in |- *.
apply ND_exq_intro.
pattern n at 3 in |- *.
rewrite <- (plusO n).
rewrite <- (distr_subst_frm q t u 0 n).
rewrite (plusO n).
apply IHd.
exact H1.
(*exq-*)
intros d IHd e IHe n G D p t H.
elim (exq_elim_inv H).
intros r H0; elim H0; clear H0; intros H0 H1.
cut
 (ND (subst_frm (S n) r t :: lift_cxt 0 (subst_cxt n D t ++ G))
    (subst_var_prf (S n) e t) (lift_frm 0 (subst_frm n p t))).
intro He.
apply (ND_exq_elim (e:=(subst_var_prf (S n) e t)) (subst_frm n p t) (IHd n G D (exq r) t H0)).
exact He.
unfold lift_cxt in |- *.
rewrite map_app.
replace (map (lift_frm 0) (subst_cxt n D t)) with
 (subst_cxt (S n) (lift_cxt 0 D) t).
rewrite commute_lift_subst_frm.
apply (IHe (S n) (lift_cxt 0 G) (r :: lift_cxt 0 D) (lift_frm 0 p) t).
rewrite <- permute_lift_cxt.
simpl in |- *. unfold lift_cxt in |- *.
rewrite <- map_app.
exact H1.
exact (le_O_n n).
exact (le_O_n n).
symmetry  in |- *.
exact (commute_lift_subst_cxt D t (le_O_n n)).
Qed.

Lemma substO_var_prf_ok :
 forall (G : C) (d : P) (p : F) (t : T),
 ND (lift_cxt 0 G) d p -> ND G (subst_var_prf 0 d t) (subst_frm 0 p t).
Proof.
intros G d p t H.
exact (subst_var_prf_ok 0 G nil t H).
Qed.

Lemma subst_hyp_ok :
 forall (G : C) (d : P) (p q : F),
 ND G d p ->
 forall (i : nat) (D : C),
 ND (D ++ p :: G) (hyp _ _ i) q -> ND (D ++ G) (subst_hyp (length D) i d) q.
Proof.
intros G d p q H i.
elim i.
(*i=0*)
simple destruct D; simpl in |- *.
(*D=nil*)
intro H0.
rewrite (hypO_inv H0).
exact H.
(*D=cons r D'*)
intros r D' H0.
rewrite (hypO_inv H0).
exact (ND_hypO (D' ++ G) r).
(*i=(S i')*)
intros i' IH D.
case D; simpl in |- *.
(*D=nil*)
intro H0.
exact (hypS_inv H0).
(*D=cons r D'*)
intros r D' H0.
exact
 (ND_weakening (d:=subst_hyp (length D') i' d) (D' ++ G) nil r (IH D' (hypS_inv H0))).
Qed.

Lemma subst_hyp_prf_ok :
 forall (e : P) (G D : C) (d : P) (p q : F),
 ND G d p ->
 ND (D ++ p :: G) e q -> ND (D ++ G) (subst_hyp_prf (length D) e d) q.
Proof.
simple induction e; clear e; simpl in |- *.
(*top+*)
intros G D d p q Hd H.
rewrite (top_inv H).
apply ND_top_intro.
(*hyp*)
intros i G D d p q Hd H.
exact (subst_hyp_ok Hd D H).
(*bot-*)
intros e IHe r G D d p q Hd H.
elim (bot_inv H).
intros H0 H1.
rewrite H0.
apply ND_bot_elim.
exact (IHe G D d p (bot _ _) Hd H1).
(*imp+*)
intros r e IHe G D d p q Hd H.
elim (imp_intro_inv H).
intros s H0.
elim H0.
intros H1 H2.
rewrite H1.
exact (ND_imp_intro (IHe G (r :: D) d p s Hd H2)).
(*imp-*)
intros e IHe f IHf G D d p q Hd H.
elim (imp_elim_inv H).
intros r H0.
elim H0.
intros H1 H2.
exact (ND_imp_elim (IHe G D d p (imp r q) Hd H1) (IHf G D d p r Hd H2)).
(*cnj+*)
intros e IHe f IHf G D d p q Hd H.
elim (cnj_intro_inv H).
intros p1 H0.
elim H0.
intros p2 H1.
elim H1.
intros H2 H3.
rewrite H2.
elim H3.
intros H4 H5.
exact (ND_cnj_intro (IHe G D d p p1 Hd H4) (IHf G D d p p2 Hd H5)).
(*cnj-1*)
intros e IHe G D d p q Hd H.
elim (cnj_elim1_inv H).
intros r H0.
exact (ND_cnj_elim1 (IHe G D d p (cnj q r) Hd H0)).
(*cnj-2*)
intros e IHe G D d p q Hd H.
elim (cnj_elim2_inv H).
intros r H0.
exact (ND_cnj_elim2 (IHe G D d p (cnj r q) Hd H0)).
(*dsj+1*)
intros r e IHe G D d p q Hd H.
elim (dsj_intro1_inv H).
intros s H0.
elim H0.
intros H1 H2.
rewrite H1.
exact (ND_dsj_intro1 r (IHe G D d p s Hd H2)).
(*dsj+2*)
intros r e IHe G D d p q Hd H.
elim (dsj_intro2_inv H).
intros s H0.
elim H0.
intros H1 H2.
rewrite H1.
exact (ND_dsj_intro2 r (IHe G D d p s Hd H2)).
(*dsj-*)
intros e IHe f IHf g IHg G D d p q Hd H.
elim (dsj_elim_inv H).
intros r1 H0; elim H0; clear H0; intros r2 H0; elim H0; clear H0;
 intros H0 H1; elim H1; clear H1; intros H1 H2.
exact
 (ND_dsj_elim (IHe G D d p (dsj r1 r2) Hd H0) (IHf G (r1 :: D) d p q Hd H1)
    (IHg G (r2 :: D) d p q Hd H2)).
(*uvq+*)
intros e IHe G D d p q Hd H.
elim (uvq_intro_inv H).
intros p' H0.
elim H0.
intros H1 H2.
rewrite H1.
apply ND_uvq_intro.
unfold lift_cxt in |- *.
rewrite map_app.
simpl in |- *.
replace (length D) with (length (map (lift_frm 0) D)).
apply
 (IHe (lift_cxt 0 G) (lift_cxt 0 D) (lift_var_prf 0 d) 
    (lift_frm 0 p) p' (ND_lift_var Hd 0)).
exact (rewr_cxt (map_app (lift_frm 0) D (p :: G)) H2).
symmetry  in |- *.
apply length_map.
(*uvq-*)
intros t e IHe G D d p q Hd H.
elim (uvq_elim_inv H).
intros p' H0.
elim H0.
intros H1 H2.
rewrite H1.
exact (ND_uvq_elim t (IHe G D d p (uvq p') Hd H2)).
(*exq+*)
intros r t e IHd G D d p q Hd H.
elim (exq_intro_inv H).
intros H0 H1.
rewrite H0.
apply ND_exq_intro.
exact (IHd G D d p (subst_frm 0 r t) Hd H1).
(*exq-*)
intros e IHe f IHf G D d p q Hd H.
elim (exq_elim_inv H).
intros r H0; elim H0; clear H0; intros H0 H1.
assert
 (H2 :
  ND (r :: lift_cxt 0 (D ++ G))
    (subst_hyp_prf (S (length D)) f (lift_var_prf 0 d)) 
    (lift_frm 0 q)).
     
unfold lift_cxt in |- *.
rewrite map_app.
replace (length D) with (length (lift_cxt 0 D)).
apply
 (IHf (lift_cxt 0 G) (r :: lift_cxt 0 D) (lift_var_prf 0 d) 
    (lift_frm 0 p) (lift_frm 0 q) (ND_lift_var Hd 0)).
apply
 (rewr_cxt (G:=r :: lift_cxt 0 (D ++ p :: G))
    (G':=(r :: lift_cxt 0 D) ++ lift_frm 0 p :: lift_cxt 0 G)).
unfold lift_cxt in |- *.
simpl in |- *.
replace (map (lift_frm 0) D ++ lift_frm 0 p :: map (lift_frm 0) G) with
 (map (lift_frm 0) (D ++ p :: G));
 [ reflexivity | exact (map_app (lift_frm 0) D (p :: G)) ].
exact H1.
symmetry  in |- *.
unfold lift_cxt in |- *.
apply length_map.
apply ND_exq_elim with (1:=IHe G D d p (exq r) Hd H0) (2:=H2).
Qed.

Lemma substO_hyp_prf_ok :
 forall (G : C) (d e : P) (p q : F),
 ND G d p -> ND (p :: G) e q -> ND G (subst_hyp_prf 0 e d) q.
Proof.
intros G d e p q H H0.
exact (subst_hyp_prf_ok nil H H0).
Qed.

End ND_substitution_lemmas.

