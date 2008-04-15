(** Proof Reflection in Coq ; ND.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export subst.

Set Implicit Arguments.

Section Natural_Deduction.

Variable l1 l2 : list nat.

Let T := trm l1.
Let F := frm l1 l2.
Let C := list F.
Let P := prf l1 l2.

(* rules ND_hypO, ND_hypS in stead of:                      *)
(* ND_hyp : (G:C;i:nat)(ND G (Hyp i)(nth i G Top)) *)
(* prevents default value for nth and makes reasoning easier.       *)

Inductive ND : C -> P -> F -> Prop :=
  | ND_top_intro : forall G : C, ND G (top_intro _ _) (top _ _)
  | ND_hypO : forall (G : C) (p : F), ND (p :: G) (hyp _ _ 0) p
  | ND_hypS :
      forall (G : C) (p q : F) (i : nat),
      ND G (hyp _ _ i) p -> ND (q :: G) (hyp _ _ (S i)) p
  | ND_bot_elim :
      forall (G : C) (d : P) (p : F),
      ND G d (bot _ _) -> ND G (bot_elim d p) p
  | ND_imp_intro :
      forall (G : C) (d : P) (p q : F),
      ND (p :: G) d q -> ND G (imp_intro p d) (imp p q)
  | ND_imp_elim :
      forall (G : C) (d e : P) (p q : F),
      ND G d (imp p q) -> ND G e p -> ND G (imp_elim d e) q
  | ND_cnj_intro :
      forall (G : C) (d e : P) (p q : F),
      ND G d p -> ND G e q -> ND G (cnj_intro d e) (cnj p q)
  | ND_cnj_elim1 :
      forall (G : C) (d : P) (p q : F),
      ND G d (cnj p q) -> ND G (cnj_elim1 d) p
  | ND_cnj_elim2 :
      forall (G : C) (d : P) (p q : F),
      ND G d (cnj p q) -> ND G (cnj_elim2 d) q
  | ND_dsj_intro1 :
      forall (G : C) (d : P) (p q : F),
      ND G d p -> ND G (dsj_intro1 q d) (dsj p q)
  | ND_dsj_intro2 :
      forall (G : C) (d : P) (p q : F),
      ND G d q -> ND G (dsj_intro2 p d) (dsj p q)
  | ND_dsj_elim :
      forall (G : C) (d e f : P) (p q r : F),
      ND G d (dsj p q) ->
      ND (p :: G) e r -> ND (q :: G) f r -> ND G (dsj_elim d e f) r
  | ND_uvq_intro :
      forall (G : C) (d : P) (p : F),
      ND (lift_cxt 0 G) d p -> ND G (uvq_intro d) (uvq p)
  | ND_uvq_elim :
      forall (G : C) (d : P) (t : T) (p : F),
      ND G d (uvq p) -> ND G (uvq_elim t d) (subst_frm 0 p t)
  | ND_exq_intro :
      forall (G : C) (d : P) (t : T) (p : F),
      ND G d (subst_frm 0 p t) -> ND G (exq_intro p t d) (exq p)
  | ND_exq_elim :
      forall (G : C) (d e : P) (p q : F),
      ND G d (exq p) ->
      ND (p :: lift_cxt 0 G) e (lift_frm 0 q) -> ND G (exq_elim d e) q.

End Natural_Deduction.

