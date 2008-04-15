(** Proof Reflection in Coq ; subj_red.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export red.
Require Export ND_subst_lems.

Set Implicit Arguments.

Section subject_reduction.

Variable l1 l2 : list nat.

Let P := prf l1 l2.
Let F := frm l1 l2.
Let C := list F.
Let T := trm l1.

(*
Proof by case analysis on (imm_red d e) and inverting the so obtained
instances (ND G d p) twice by using inversion lemmas.

The difference with old_subj_red.v is that here the Inversion tactic is
avoided; the large proof terms it constructs are now folded and opaque
in the proof, by the use of the inversion lemma's (see inv_lems.v).
This file contains more lines of tactics though.

To give an idea, compare the size of their compiled counterparts.
subj_red.vo     	 58354
old_subj_red.vo		428700

Compilation times:
coqc -opt subj_red.v  	   12.70s user 0.22s system 96% cpu 13.393  total
coqc -opt old_subj_red.v  163.34s user 1.74s system 97% cpu 2:50.07 total
*)

Lemma SR_imm_red :
 forall (G : C) (d e : P) (p : F), imm_red d e -> ND G d p -> ND G e p.
Proof.
intros G d e p H.
case H; clear H d e.

(*pr_imp*)
intros d e q H.
(* next 12 lines iso.: Inversion_clear H. Inversion_clear H0. *)
elim (imp_elim_inv H). clear H.
intros r H.
elim H. clear H.
intros H1 H2.
elim (imp_intro_inv H1). clear H1.
intros s H3.
elim H3. clear H3.
intros H4 H5.
injection H4. clear H4.
intros H6 H7.
rewrite H6.
rewrite H7 in H2.
apply (substO_hyp_prf_ok H2 H5).

(*pr_cnj1*)
intros d1 d2 H.
elim (cnj_elim1_inv H). clear H.
intros q H0.
elim (cnj_intro_inv H0). clear H0.
intros p1 H1.
elim H1. clear H1.
intros p2 H2.
elim H2. clear H2.
intros H3 H4.
elim H4. clear H4.
intros H5 H6.
injection H3. clear H3.
intros H7 H8.
rewrite H8.
exact H5.

(*pr_cnj2*)
intros d1 d2 H.
elim (cnj_elim2_inv H). clear H.
intros q H0.
elim (cnj_intro_inv H0). clear H0.
intros p1 H1.
elim H1. clear H1.
intros p2 H2.
elim H2. clear H2.
intros H3 H4.
elim H4. clear H4.
intros H5 H6.
injection H3.
intros H7 H8.
rewrite H7.
exact H6.

(*pr_dsj1*)
intros d e1 e2 q H.
elim (dsj_elim_inv H); clear H.
intros r1 H; elim H; clear H; intros r2 H; elim H; clear H; intros H H0;
 elim H0; clear H0; intros H0 H1.
elim (dsj_intro1_inv H); clear H.
intros s H2; elim H2; clear H2; intros H2 H3.
injection H2; intros H4 H5.
rewrite H5 in H0.
apply (substO_hyp_prf_ok H3 H0).

(*pr_dsj2*)
intros d e1 e2 q H.
elim (dsj_elim_inv H); clear H.
intros r1 H; elim H; clear H; intros r2 H; elim H; clear H; intros H H0;
 elim H0; clear H0; intros H0 H1.
elim (dsj_intro2_inv H); clear H.
intros s H2; elim H2; clear H2; intros H2 H3.
injection H2; intros H4 H5.
rewrite H4 in H1.
apply (substO_hyp_prf_ok H3 H1).

(*pr_uvq*)
intros d t H.
elim (uvq_elim_inv H). clear H.
intros q H0.
elim H0. clear H0.
intros H1 H2.
rewrite H1. clear H1.
elim (uvq_intro_inv H2).
intros r H3.
elim H3. clear H3.
intros H4 H5.
injection H4. clear H4.
intro H6.
rewrite H6.
apply (substO_var_prf_ok G t H5).

(*pr_exq*)
intros d e t q H.
elim (exq_elim_inv H); clear H.
intros r H; elim H; clear H; intros H H0.
elim (exq_intro_inv H); clear H; intros H1 H2.
injection H1; clear H1; intro H1.
assert (H3 : ND (subst_frm 0 q t :: G) (subst_var_prf 0 e t) p).
rewrite <- (simpl_subst_frm p 0 t).
rewrite H1 in H0.
exact (subst_var_prf_ok 0 G (q :: nil) t H0).
exact (subst_hyp_prf_ok nil H2 H3).

(*pcd_bot*)
intros d e f q H.
elim (bot_inv H); clear H; intros H H0; rewrite H; clear H.
elim (dsj_elim_inv H0); clear H0.
intros r H; elim H; clear H; intros H H0; elim H0; clear H0; intros H0 H1;
 elim H1; clear H1; intros H1 H2.
exact (ND_dsj_elim H0 (ND_bot_elim q H1) (ND_bot_elim q H2)).

(*pcd_imp*)
intros d e f g H.
elim (imp_elim_inv H); clear H.
intros s H; elim H; clear H; intros H H0.
elim (dsj_elim_inv H); clear H.
intros r1 H; elim H; clear H; intros r2 H; elim H; clear H; intros H H1;
 elim H1; clear H1; intros H1 H2.
exact
 (ND_dsj_elim H (ND_imp_elim H1 (ND_weakening G nil r1 H0))
    (ND_imp_elim H2 (ND_weakening G nil r2 H0))).

(*pcd_cnj1*)
intros d e f H.
elim (cnj_elim1_inv H); clear H; intros s H.
elim (dsj_elim_inv H); clear H.
intros r1 H; elim H; clear H; intros r2 H; elim H; clear H; intros H H0;
 elim H0; clear H0; intros H0 H1.
exact (ND_dsj_elim H (ND_cnj_elim1 H0) (ND_cnj_elim1 H1)).

(*pcd_cnj2*)
intros d e f H.
elim (cnj_elim2_inv H); clear H; intros s H.
elim (dsj_elim_inv H); clear H.
intros r1 H; elim H; clear H; intros r2 H; elim H; clear H; intros H H0;
 elim H0; clear H0; intros H0 H1.
exact (ND_dsj_elim H (ND_cnj_elim2 H0) (ND_cnj_elim2 H1)).

(*pcd_dsj*) 
intros d e f g h H.
elim (dsj_elim_inv H); clear H.
intros r1 H; elim H; clear H; intros r2 H; elim H; clear H; intros H H0;
 elim H0; clear H0; intros H0 H1.
elim (dsj_elim_inv H); clear H.
intros r3 H; elim H; clear H; intros r4 H; elim H; clear H; intros H H2;
 elim H2; clear H2; intros H2 H3.
exact
 (ND_dsj_elim H
    (ND_dsj_elim H2 (ND_weakening G (r1 :: nil) r3 H0)
       (ND_weakening G (r2 :: nil) r3 H1))
    (ND_dsj_elim H3 (ND_weakening G (r1 :: nil) r4 H0)
       (ND_weakening G (r2 :: nil) r4 H1))).

(*pcd_uvq*)
intros d e f t H. 
elim (uvq_elim_inv H); clear H.
intros q H; elim H; clear H; intros H H0.
rewrite H; clear H.
elim (dsj_elim_inv H0); clear H0.
intros r1 H; elim H; clear H; intros r2 H; elim H; clear H; intros H H0;
 elim H0; clear H0; intros H0 H1.

exact (ND_dsj_elim H (ND_uvq_elim t H0) (ND_uvq_elim t H1)).

(*pcd_exq*)
intros d e f g H.
elim (exq_elim_inv H); clear H.
intros s H; elim H; clear H; intros H H0.
elim (dsj_elim_inv H); clear H.
intros r1 H; elim H; clear H; intros r2 H; elim H; clear H; intros H H1;
 elim H1; clear H1; intros H1 H2.
apply ND_dsj_elim with (1:=H).
apply ND_exq_elim with (1:=H1).
exact (ND_weakening (lift_cxt 0 G) (s :: nil) (lift_frm 0 r1) H0).
apply ND_exq_elim with (1:=H2).
exact (ND_weakening (lift_cxt 0 G) (s :: nil) (lift_frm 0 r2) H0).

(*pce_bot*)
intros d e q H.
elim (bot_inv H); clear H.
intros H H0; rewrite H; clear H.
elim (exq_elim_inv H0); clear H0.
 intros r H; elim H; clear H; intros H H0.
apply ND_exq_elim with (1:=H).
exact (ND_bot_elim (lift_frm 0 q) H0).

(*pce_imp*)
intros d e f H.
elim (imp_elim_inv H); clear H.
intros s H; elim H; clear H; intros H H0.
elim (exq_elim_inv H); clear H.
intros r H; elim H; clear H; intros H H1.
assert
 (H2 :
  ND (r :: lift_cxt 0 G) (lift_hyp_prf 0 (lift_var_prf 0 f)) (lift_frm 0 s)).
apply
 (ND_weakening (d:=lift_var_prf 0 f) (lift_cxt 0 G) nil
    (p:=lift_frm 0 s) r).
exact (ND_lift_var H0 0).
apply ND_exq_elim with (1:=H) (2:=(ND_imp_elim H1 H2)).

(*pce_cnj1*)
intros d e H.
elim (cnj_elim1_inv H); clear H.
intros q H.
elim (exq_elim_inv H); clear H.
intros r H; elim H; clear H; intros H H0.
apply ND_exq_elim with (1:=H) (2:=ND_cnj_elim1 H0).

(*pce_cnj2*)
intros d e H.
elim (cnj_elim2_inv H); clear H.
intros q H.
elim (exq_elim_inv H); clear H.
intros r H; elim H; clear H; intros H H0.
apply ND_exq_elim with (1:=H) (2:=ND_cnj_elim2 H0).

(*pce_dsj*)
intros d e f g H.
elim (dsj_elim_inv H); clear H.
intros r1 H; elim H; clear H; intros r2 H; elim H; clear H; intros H H0;
 elim H0; clear H0; intros H0 H1.
elim (exq_elim_inv H); clear H.
intros r H; elim H; clear H; intros H H2.
apply ND_exq_elim with (1:=H).
simpl in H2.
apply ND_dsj_elim with (1:=H2).
exact (ND_weakening (lift_cxt 0 G) (lift_frm 0 r1 :: nil) r (ND_lift_var H0 0)).
exact (ND_weakening (lift_cxt 0 G) (lift_frm 0 r2 :: nil) r (ND_lift_var H1 0)).

(*pce_uvq*)
intros d e t H.
elim (uvq_elim_inv H); clear H.
intros p' H; elim H; clear H; intros H H0.
rewrite H; clear H.
elim (exq_elim_inv H0); clear H0.
intros r H; elim H; clear H; intros H H0.
cut
 (ND (r :: lift_cxt 0 G) (uvq_elim (lift_trm 0 t) e)
    (lift_frm 0 (subst_frm 0 p' t))).
intro H1.
apply ND_exq_elim with (1:=H) (2:=H1).
rewrite distr_lift_substO_frm.
apply ND_uvq_elim.
exact H0.

(*pce_exq*)
intros d e f H.
elim (exq_elim_inv H); clear H.
intros s H; elim H; clear H; intros H H0.
elim (exq_elim_inv H); clear H.
intros r H; elim H; clear H; intros H H1.
cut
 (ND (r :: lift_cxt 0 G) (exq_elim e (lift_hyp_prf 1 (lift_var_prf 1 f)))
    (lift_frm 0 p)).
intro H2.
apply ND_exq_elim with (1:=H) (2:=H2).
cut
 (ND (lift_frm 1 s :: lift_cxt 0 (r :: lift_cxt 0 G))
    (lift_hyp_prf 1 (lift_var_prf 1 f)) (lift_frm 0 (lift_frm 0 p))).
intro H2.
simpl in H1.
apply ND_exq_elim with (1:=H1) (2:=H2).
unfold lift_cxt in |- *.
apply
 (ND_weakening (d:=lift_var_prf 1 f) (lift_cxt 0 (lift_cxt 0 G))
    (lift_frm 1 s :: nil) (p:=lift_frm 0 (lift_frm 0 p)) 
    (lift_frm 0 r)).
simpl in |- *.
rewrite permute_lift_cxt.
rewrite permute_lift_frm.
exact (ND_lift_var H0 1).
exact (le_n 0).
exact (le_n 0).

Qed.

(*****************************************************************************)

Lemma SR :
 forall d d' : P, red d d' -> forall (G : C) (p : F), ND G d p -> ND G d' p.
Proof.
intros d d' H.
elim H; clear H d d'.

(*red_imm_red*)
intros d d' H G p H0.
exact (SR_imm_red H H0).

(*red_bot_elim*)
intros d d' p H IH G q H0.
elim (bot_inv H0). clear H0.
intros H0 H1.
rewrite H0.
exact (ND_bot_elim p (IH G (bot _ _) H1)).

(*red_imp_intro*)
intros d d' p H IH G q H0.
elim (imp_intro_inv H0). clear H0.
intros r H0.
elim H0.
intros H1 H2.
rewrite H1.
exact (ND_imp_intro (IH (p :: G) r H2)).

(*red_imp_elim_1*)
intros d d' e H IH G p H0.
elim (imp_elim_inv H0). clear H0.
intros q H0.
elim H0. intros H1 H2.
exact (ND_imp_elim (IH G (imp q p) H1) H2).

(*red_imp_elim_2*)
intros d d' e H IH G p H0.
elim (imp_elim_inv H0). clear H0.
intros q H0.
elim H0. intros H1 H2.
exact (ND_imp_elim H1 (IH G q H2)).

(*red_cnj_intro_1*)
intros d d' e H IH G p H0.
elim (cnj_intro_inv H0). clear H0.
intros p1 H0.
elim H0. intros p2 H1.
elim H1. clear H0 H1.
intros H1 H2.
rewrite H1.
elim H2. clear H1 H2.
intros H1 H2.
exact (ND_cnj_intro (IH G p1 H1) H2).

(*red_cnj_intro_2*)
intros d d' e H IH G p H0.
elim (cnj_intro_inv H0). clear H0.
intros p1 H0.
elim H0. intros p2 H1.
elim H1. clear H0 H1.
intros H1 H2.
rewrite H1.
elim H2. clear H1 H2.
intros H1 H2.
exact (ND_cnj_intro H1 (IH G p2 H2)).

(*red_cnj_elim1*)
intros d d' H IH G p H0.
elim (cnj_elim1_inv H0). clear H0.
intros q H0.
exact (ND_cnj_elim1 (IH G (cnj p q) H0)).

(*red_cnj_elim2*)
intros d d' H IH G p H0.
elim (cnj_elim2_inv H0). clear H0.
intros q H0.
exact (ND_cnj_elim2 (IH G (cnj q p) H0)).

(*red_dsj_intro1*)
intros d d' p H IH G q H0.
elim (dsj_intro1_inv H0). clear H0.
intros r H0.
elim H0. intros H1 H2.
rewrite H1.
exact (ND_dsj_intro1 p (IH G r H2)).

(*red_dsj_intro2*)
intros d d' p H IH G q H0.
elim (dsj_intro2_inv H0). clear H0.
intros r H0.
elim H0. intros H1 H2.
rewrite H1.
exact (ND_dsj_intro2 p (IH G r H2)).

(*red_dsj_elim_1*)
intros d d' e f H IH G q H0.
elim (dsj_elim_inv H0); clear H0.
intros r1 H0; elim H0; clear H0; intros r2 H0; elim H0; clear H0;
 intros H0 H1; elim H1; clear H1; intros H1 H2.
exact (ND_dsj_elim (IH G (dsj r1 r2) H0) H1 H2).

(*red_dsj_elim_2*)
intros d d' e f H IH G q H0.
elim (dsj_elim_inv H0); clear H0.
intros r1 H0; elim H0; clear H0; intros r2 H0; elim H0; clear H0;
 intros H0 H1; elim H1; clear H1; intros H1 H2.
exact (ND_dsj_elim H0 (IH (r1 :: G) q H1) H2).

(*red_dsj_elim_3*)
intros d d' e f H IH G q H0.
elim (dsj_elim_inv H0); clear H0.
intros r1 H0; elim H0; clear H0; intros r2 H0; elim H0; clear H0;
 intros H0 H1; elim H1; clear H1; intros H1 H2.
exact (ND_dsj_elim H0 H1 (IH (r2 :: G) q H2)).

(*red_uvq_intro*)
intros d d' H IH G p H0.
elim (uvq_intro_inv H0).
intros p' H1.
elim H1.
clear H0 H1.
intros H0 H1.
rewrite H0.
exact (ND_uvq_intro G (IH (lift_cxt 0 G) p' H1)).

(*red_uvq_elim*)
intros d d' t H IH G p H0.
elim (uvq_elim_inv H0). intros p' H1.
elim H1. intro H2.
rewrite H2. clear H0 H1 H2.
intro H0.
exact (ND_uvq_elim t (IH G (uvq p') H0)).

(*red_exq_intro*)
intros d d' t p H IH G q H0.
elim (exq_intro_inv H0).
intro H1. rewrite H1. clear H0 H1. intro H0.
exact (ND_exq_intro t p (IH G (subst_frm 0 p t) H0)).

(*red_exq_elim_1*)
intros d d' e H IH G p H0.
elim (exq_elim_inv H0); clear H0.
intros r H0; elim H0; clear H0; intros H0 H1.
exact (ND_exq_elim p (IH G (exq r) H0) H1).

(*red_exq_elim_2*)
intros d d' e H IH G p H0.
elim (exq_elim_inv H0); clear H0.
intros r H0; elim H0; clear H0; intros H0 H1.
exact (ND_exq_elim p H0 (IH (r :: lift_cxt 0 G) (lift_frm 0 p) H1)).


Qed.


End subject_reduction.

