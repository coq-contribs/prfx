(** Proof Reflection in Coq ; inv_lems.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export ND.

Set Implicit Arguments.

Section Inversion_Lemmata.

Variable l1 l2 : list nat.

Let P := prf l1 l2.
Let F := frm l1 l2.
Let T := trm l1.
Let Ts := trms l1.
Let C := list F.

(* The proof terms of the following lemma's are relatively large;
   it's important to keep them opaque in other proofs. *)

Lemma nohyp_inv : forall (i : nat) (p : F), ND nil (hyp _ _ i) p -> False.
Proof.
intros i p H.
inversion H.
Qed.

Lemma hypO_inv : forall (G : C) (p q : F), ND (q :: G) (hyp _ _ 0) p -> p = q.
intros G p q H.
inversion H.
reflexivity.
Qed.

Lemma hypS_inv :
 forall (G : C) (i : nat) (p q : F),
 ND (q :: G) (hyp _ _ (S i)) p -> ND G (hyp _ _ i) p.
intros G i p q H.
inversion_clear H.
exact H0.
Qed.

Lemma top_inv : forall (G : C) (p : F), ND G (top_intro _ _) p -> p = top _ _.
Proof.
intros G p H.
inversion H.
reflexivity.
Qed.

Lemma bot_inv :
 forall (G : C) (d : P) (p q : F),
 ND G (bot_elim d q) p -> p = q /\ ND G d (bot _ _).
Proof.
intros G d p q H.
inversion_clear H.
split.
reflexivity.
exact H0.
Qed.

Lemma imp_intro_inv :
 forall (G : C) (d : P) (p q : F),
 ND G (imp_intro q d) p -> exists r : F, p = imp q r /\ ND (q :: G) d r.
Proof.
intros G d p q H.
inversion_clear H.
exists q0.
split.
reflexivity.
exact H0.
Qed.

Lemma imp_elim_inv :
 forall (G : C) (d e : P) (p : F),
 ND G (imp_elim d e) p -> exists q : F, ND G d (imp q p) /\ ND G e q.
Proof.
intros G d e p H.
inversion_clear H.
exists p0.
split.
exact H0.
exact H1.
Qed.

Lemma cnj_intro_inv :
 forall (G : C) (d1 d2 : P) (p : F),
 ND G (cnj_intro d1 d2) p ->
 exists p1 : F, (exists p2 : F, p = cnj p1 p2 /\ ND G d1 p1 /\ ND G d2 p2).
Proof.
intros G d1 d2 p H.
inversion_clear H.
exists p0.
exists q.
split.
reflexivity.
split.
exact H0.
exact H1.
Qed.

Lemma cnj_elim1_inv :
 forall (G : C) (d : P) (p : F),
 ND G (cnj_elim1 d) p -> exists q : F, ND G d (cnj p q).
Proof.
intros G d p H.
inversion_clear H.
exists q.
exact H0.
Qed.

Lemma cnj_elim2_inv :
 forall (G : C) (d : P) (p : F),
 ND G (cnj_elim2 d) p -> exists q : F, ND G d (cnj q p).
Proof.
intros G d p H.
inversion_clear H.
exists p0.
exact H0.
Qed.

Lemma dsj_intro1_inv :
 forall (G : C) (d : P) (p q2 : F),
 ND G (dsj_intro1 q2 d) p -> exists q1 : F, p = dsj q1 q2 /\ ND G d q1.
Proof.
intros G d p q2 H.
inversion_clear H.
exists p0.
split.
reflexivity.
exact H0.
Qed.

Lemma dsj_intro2_inv :
 forall (G : C) (d : P) (p q1 : F),
 ND G (dsj_intro2 q1 d) p -> exists q2 : F, p = dsj q1 q2 /\ ND G d q2.
Proof.
intros G d p q1 H.
inversion_clear H.
exists q.
split.
reflexivity.
exact H0.
Qed.

Lemma dsj_elim_inv :
 forall (G : C) (d e1 e2 : P) (p : F),
 ND G (dsj_elim d e1 e2) p ->
 exists r1 : F,
   (exists r2 : F,
      ND G d (dsj r1 r2) /\ ND (r1 :: G) e1 p /\ ND (r2 :: G) e2 p).
Proof.
intros G d e1 e2 p H.
inversion_clear H.
exists p0.
exists q.
split.
exact H0.
split.
exact H1.
exact H2.
Qed.

Lemma uvq_intro_inv :
 forall (G : C) (d : P) (p : F),
 ND G (uvq_intro d) p -> exists p' : F, p = uvq p' /\ ND (lift_cxt 0 G) d p'.
Proof.
intros G d p H.
inversion_clear H.
exists p0.
split.
reflexivity.
exact H0.
Qed.

Lemma uvq_elim_inv :
 forall (G : C) (d : P) (t : T) (p : F),
 ND G (uvq_elim t d) p ->
 exists p' : F, p = subst_frm 0 p' t /\ ND G d (uvq p').
Proof.
intros G d t p H.
inversion_clear H.
exists p0.
split.
reflexivity.
exact H0.
Qed.

Lemma exq_intro_inv :
 forall (G : C) (d : P) (t : T) (p p' : F),
 ND G (exq_intro p' t d) p -> p = exq p' /\ ND G d (subst_frm 0 p' t).
Proof.
intros G d t p p' H.
inversion_clear H.
split.
reflexivity.
exact H0.
Qed.

Lemma exq_elim_inv :
 forall (G : C) (d e : P) (p : F),
 ND G (exq_elim d e) p ->
 exists q : F, ND G d (exq q) /\ ND (q :: lift_cxt 0 G) e (lift_frm 0 p).
Proof.
intros G d e p H.
inversion_clear H.
exists p0.
split.
exact H0.
exact H1.
Qed.

End Inversion_Lemmata.