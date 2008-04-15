(** Proof Reflection in Coq ; ND_lift_lems.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export ND.
Require Export inv_lems.
Require Export subst_lems.

Set Implicit Arguments.

Section ND_lifting_lemmas.

Variable l1 l2 : list nat.

Let P := prf l1 l2.
Let F := frm l1 l2.
Let T := trm l1.
Let Ts := trms l1.
Let C := list F.

Lemma ND_lift_var :
 forall (G : C) (d : P) (p : F),
 ND G d p ->
 forall n : nat, ND (lift_cxt n G) (lift_var_prf n d) (lift_frm n p).
Proof.
intros G d p H.
elim H; clear H G d p; simpl in |- *.
intros G m.
apply ND_top_intro.
intros G p n.
apply ND_hypO.
intros G p q i Hi IHi n.
apply ND_hypS.
apply IHi.
intros G d p Hd IHd n.
apply ND_bot_elim.
apply IHd.
intros G d p q Hd IHd n.
apply ND_imp_intro.
apply IHd.
intros G d e p q Hd IHd He IHe n.
exact (ND_imp_elim (IHd n) (IHe n)).
intros G d e p q Hd IHd He IHe n.
exact (ND_cnj_intro (IHd n) (IHe n)).
intros G d p q Hd IHd n.
exact (ND_cnj_elim1 (IHd n)).
intros G d p q Hd IHd n.
exact (ND_cnj_elim2 (IHd n)).
intros G d p q Hd IHd n.
exact (ND_dsj_intro1 (lift_frm n q) (IHd n)).
intros G d p q Hd IHd n.
exact (ND_dsj_intro2 (lift_frm n p) (IHd n)).
intros G d e f p q r Hd IHd He IHe Hf IHf n.
exact (ND_dsj_elim (IHd n) (IHe n) (IHf n)).
intros G d p Hd IHd n.
apply ND_uvq_intro.
rewrite (permute_lift_cxt G (le_O_n n)).
exact (IHd (S n)).
intros G d t p Hd IHd n.
rewrite (distr_lift_substO_frm p t n).
exact (ND_uvq_elim (lift_trm n t) (IHd n)).
intros G d t p Hd IHd n.
cut
 (ND (lift_cxt n G) (lift_var_prf n d)
    (subst_frm 0 (lift_frm (S n) p) (lift_trm n t))).
intro H.
apply ND_exq_intro with (1:=H).
rewrite <- (distr_lift_substO_frm p t n).
exact (IHd n).
intros G d e p q Hd IHd He IHe n.
cut
 (ND (lift_frm (S n) p :: lift_cxt 0 (lift_cxt n G)) 
    (lift_var_prf (S n) e) (lift_frm 0 (lift_frm n q))).
intro H.
apply ND_exq_elim with (1:=IHd n) (2:=H).
rewrite (permute_lift_frm q (le_O_n n)).
rewrite (permute_lift_cxt G (le_O_n n)).
exact (IHe (S n)).
Qed.

Lemma ND_weak_hyp :
 forall (i : nat) (G D : C) (p q : F),
 ND (D ++ G) (hyp _ _ i) p ->
 ND (D ++ q :: G) (hyp _ _ (lift (length D) i)) p.
Proof.
simple induction i; simple destruct D.
intros p q H.
exact (ND_hypS q H).
intros r D' p q H.
rewrite (hypO_inv H).
exact (ND_hypO (D' ++ q :: G) r).
intros p q H0.
exact (ND_hypS q H0).
intros r D' p q H0.
exact (ND_hypS r (H G D' p q (hypS_inv H0))).
Qed.

Definition rewr_prf (G : C) (d d' : P) (p : F) (H : d = d') 
  (H0 : ND G d p) : ND G d' p := eq_ind d (fun e => ND G e p) H0 d' H.

Definition rewr_cxt (G G' : C) (d : P) (p : F) (H : G = G') 
  (H0 : ND G d p) : ND G' d p := eq_ind G (fun g => ND g d p) H0 G' H.

(* Induction on (ND G d p) with one of G,d,p NOT a variable    *)
(* is not useful. Instead, we proceed with induction on d:P.     *) 
(* This is rather expensive, as all instances have to be inverted. *)

Lemma ND_weakening :
 forall (d : P) (G D : C) (p q : F),
 ND (D ++ G) d p -> ND (D ++ q :: G) (lift_hyp_prf (length D) d) p.
Proof.
simple induction d; clear d; simpl in |- *.
(* top_intro *)
intros G D p q H.
rewrite (top_inv H).
apply ND_top_intro.
(* hyp *)
exact ND_weak_hyp.
(* bot_elim *)
intros d IHd r G D p q H.
elim (bot_inv H).
intros H1 H2.
rewrite <- H1.
exact (ND_bot_elim p (IHd G D (bot _ _) q H2)).
(* imp_intro *)
intros r d IHd G D p q H.
elim (imp_intro_inv H).
intros s H0.
elim H0.
intros H1 H2.
rewrite H1.
apply ND_imp_intro.
exact (IHd G (r :: D) s q H2).
(* imp_elim *)
intros d IHd e IHe G D p q H.
elim (imp_elim_inv H).
intros r H0.
elim H0.
intros H1 H2.
exact (ND_imp_elim (IHd G D (imp r p) q H1) (IHe G D r q H2)).
(* cnj_intro *)
intros d IHd e IHe G D p q H.
elim (cnj_intro_inv H).
intros p1 H0.
elim H0.
intros p2 H1.
elim H1.
intros H2 H3.
elim H3.
intros H4 H5.
rewrite H2.
exact (ND_cnj_intro (IHd G D p1 q H4) (IHe G D p2 q H5)).
(* cnj_elim1 *)
intros d IHd G D p q H.
elim (cnj_elim1_inv H).
intros r H0.
exact (ND_cnj_elim1 (IHd G D (cnj p r) q H0)).
(* cnj_elim2 *)
intros d IHd G D p q H.
elim (cnj_elim2_inv H).
intros r H0.
exact (ND_cnj_elim2 (IHd G D (cnj r p) q H0)).
(* dsj_intro1 *)
intros r d IHd G D p q H.
elim (dsj_intro1_inv H).
intros s H0.
elim H0.
intros H1 H2.
rewrite H1.
exact (ND_dsj_intro1 r (IHd G D s q H2)).
(* dsj_intro2 *)
intros r d IHd G D p q H.
elim (dsj_intro2_inv H).
intros s H0.
elim H0.
intros H1 H2.
rewrite H1.
exact (ND_dsj_intro2 r (IHd G D s q H2)).
(* dsj_elim *)
intros d IHd e IHe f IHf G D p q H.
elim (dsj_elim_inv H).
intros r1 H0; elim H0; clear H0; intros r2 H0; elim H0; clear H0;
 intros H0 H1; elim H1; clear H1; intros H1 H2.
exact
 (ND_dsj_elim (IHd G D (dsj r1 r2) q H0) (IHe G (r1 :: D) p q H1)
    (IHf G (r2 :: D) p q H2)).
(* uvq_intro *)
intros d IHd G D p q H.
elim (uvq_intro_inv H).
intros p' H0; elim H0; clear H0; intro H0; rewrite H0; clear H0; intro H0.
apply ND_uvq_intro.
(* For some reason the Rewrite tactic doesn't work here;          *)
(* I work around it using the above defined rewr_cxt and rewr_prf.*)
apply
 (rewr_cxt (G:=lift_cxt 0 D ++ lift_cxt 0 (q :: G))
    (G':=lift_cxt 0 (D ++ q :: G)) (d:=lift_hyp_prf (length D) d) (p:=p')).
symmetry  in |- *.
exact (map_app (lift_frm 0) D (q :: G)).
replace (length D) with (length (lift_cxt 0 D)).
apply (IHd (lift_cxt 0 G) (lift_cxt 0 D) p' (lift_frm 0 q)).
apply (rewr_cxt (G:=lift_cxt 0 (D ++ G)) (G':=lift_cxt 0 D ++ lift_cxt 0 G)).
exact (map_app (lift_frm 0) D G).
exact H0.
symmetry  in |- *.
exact (length_map (lift_frm 0) D).
(* uvq_elim *)
intros t d IHd G D p q H.
elim (uvq_elim_inv H).
intros r H0.
elim H0.
intros H1 H2.
rewrite H1.
apply ND_uvq_elim.
exact (IHd G D (uvq r) q H2).
(* exq_intro *)
intros r t d IHd G D p q H.
elim (exq_intro_inv H).
intros H0 H1.
rewrite H0.
apply ND_exq_intro.    
exact (IHd G D (subst_frm 0 r t) q H1).
(* exq_elim *)
intros d IHd e IHe G D p q H.
elim (exq_elim_inv H).
intros s H0; elim H0; clear H0; intros H0 H1.
cut
 (ND (s :: lift_cxt 0 (D ++ q :: G)) (lift_hyp_prf (S (length D)) e)
    (lift_frm 0 p)).
apply ND_exq_elim with (1:=IHd G D (exq s) q H0).
apply
 (rewr_cxt (G:=s :: lift_cxt 0 D ++ lift_cxt 0 (q :: G))
    (G':=s :: lift_cxt 0 (D ++ q :: G))).
replace (lift_cxt 0 D ++ lift_cxt 0 (q :: G)) with (lift_cxt 0 (D ++ q :: G)).
reflexivity.
exact (map_app (lift_frm 0) D (q :: G)).
apply
 (rewr_prf (G:=s :: lift_cxt 0 D ++ lift_cxt 0 (q :: G))
    (d:=lift_hyp_prf (S (length (lift_cxt 0 D))) e)
    (d':=lift_hyp_prf (S (length D)) e)).
rewrite (eq_S (length D) (length (lift_cxt 0 D))).
reflexivity.
exact (length_map (lift_frm 0) D).
apply (IHe (lift_cxt 0 G) (s :: lift_cxt 0 D) (lift_frm 0 p) (lift_frm 0 q)).
apply
 (rewr_cxt (G:=s :: lift_cxt 0 (D ++ G))
    (G':=s :: lift_cxt 0 D ++ lift_cxt 0 G)).
replace (lift_cxt 0 D ++ lift_cxt 0 G) with (lift_cxt 0 (D ++ G)).
reflexivity.
exact (map_app (lift_frm 0) D G).
exact H1.
Qed.

End ND_lifting_lemmas.
