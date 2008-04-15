(** Proof Reflection in Coq ; red.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export subst.

Set Implicit Arguments.

Section reduction.

Variable l1 l2 : list nat.

Let T := trm l1.
Let F := frm l1 l2.
Let P := prf l1 l2.

Inductive imm_red : P -> P -> Prop :=
 
 (* proper reductions *)
 
  | pr_imp :
      forall (d e : P) (p : F),
      imm_red (imp_elim (imp_intro p d) e) (subst_hyp_prf 0 d e)
  | pr_cnj1 : forall d1 d2 : P, imm_red (cnj_elim1 (cnj_intro d1 d2)) d1
  | pr_cnj2 : forall d1 d2 : P, imm_red (cnj_elim2 (cnj_intro d1 d2)) d2
  | pr_dsj1 :
      forall (d e1 e2 : P) (p : F),
      imm_red (dsj_elim (dsj_intro1 p d) e1 e2) (subst_hyp_prf 0 e1 d)
  | pr_dsj2 :
      forall (d e1 e2 : P) (p : F),
      imm_red (dsj_elim (dsj_intro2 p d) e1 e2) (subst_hyp_prf 0 e2 d)
  | pr_uvq :
      forall (d : P) (t : T),
      imm_red (uvq_elim t (uvq_intro d)) (subst_var_prf 0 d t)
  | pr_exq :
      forall (d e : P) (t : T) (p : F),
      imm_red (exq_elim (exq_intro p t d) e)
        (subst_hyp_prf 0 (subst_var_prf 0 e t) d)
      
      (* permutative conversions *)
      
      (* pull out dsj_elim *)
      
  | pcd_bot :
      forall (d e f : P) (p : F),
      imm_red (bot_elim (dsj_elim d e f) p)
        (dsj_elim d (bot_elim e p) (bot_elim f p))
  | pcd_imp :
      forall d e f g : P,
      imm_red (imp_elim (dsj_elim d e f) g)
        (dsj_elim d (imp_elim e (lift_hyp_prf 0 g))
           (imp_elim f (lift_hyp_prf 0 g)))
  | pcd_cnj1 :
      forall d e f : P,
      imm_red (cnj_elim1 (dsj_elim d e f))
        (dsj_elim d (cnj_elim1 e) (cnj_elim1 f))
  | pcd_cnj2 :
      forall d e f : P,
      imm_red (cnj_elim2 (dsj_elim d e f))
        (dsj_elim d (cnj_elim2 e) (cnj_elim2 f))
  | pcd_dsj :
      forall d e f g h : P,
      imm_red (dsj_elim (dsj_elim d e f) g h)
        (dsj_elim d (dsj_elim e (lift_hyp_prf 1 g) (lift_hyp_prf 1 h))
           (dsj_elim f (lift_hyp_prf 1 g) (lift_hyp_prf 1 h)))
  | pcd_uvq :
      forall (d e f : P) (t : T),
      imm_red (uvq_elim t (dsj_elim d e f))
        (dsj_elim d (uvq_elim t e) (uvq_elim t f))
  | pcd_exq :
      forall d e f g : P,
      imm_red (exq_elim (dsj_elim d e f) g)
        (dsj_elim d (exq_elim e (lift_hyp_prf 1 g))
           (exq_elim f (lift_hyp_prf 1 g)))
      
      (* pull out exq_elim *)
      
  | pce_bot :
      forall (d e : P) (p : F),
      imm_red (bot_elim (exq_elim d e) p)
        (exq_elim d (bot_elim e (lift_frm 0 p)))
  | pce_imp :
      forall d e f : P,
      imm_red (imp_elim (exq_elim d e) f)
        (exq_elim d (imp_elim e (lift_hyp_prf 0 (lift_var_prf 0 f))))
  | pce_cnj1 :
      forall d e : P,
      imm_red (cnj_elim1 (exq_elim d e)) (exq_elim d (cnj_elim1 e))
  | pce_cnj2 :
      forall d e : P,
      imm_red (cnj_elim2 (exq_elim d e)) (exq_elim d (cnj_elim2 e))
  | pce_dsj :
      forall d e f g : P,
      imm_red (dsj_elim (exq_elim d e) f g)
        (exq_elim d
           (dsj_elim e (lift_hyp_prf 1 (lift_var_prf 0 f))
              (lift_hyp_prf 1 (lift_var_prf 0 g))))
  | pce_uvq :
      forall (d e : P) (t : T),
      imm_red (uvq_elim t (exq_elim d e))
        (exq_elim d (uvq_elim (lift_trm 0 t) e))
  | pce_exq :
      forall d e f : P,
      imm_red (exq_elim (exq_elim d e) f)
        (exq_elim d (exq_elim e (lift_hyp_prf 1 (lift_var_prf 1 f)))).

Infix "|-->" := imm_red (left associativity, at level 50).

Inductive red : P -> P -> Prop :=
  | red_imm_red : forall d d' : P, d |--> d' -> red d d'
  | red_bot_elim :
      forall (d d' : P) (p : F),
      red d d' -> red (bot_elim d p) (bot_elim d' p)
  | red_imp_intro :
      forall (d d' : P) (p : F),
      red d d' -> red (imp_intro p d) (imp_intro p d')
  | red_imp_elim_1 :
      forall d d' e : P, red d d' -> red (imp_elim d e) (imp_elim d' e)
  | red_imp_elim_2 :
      forall d d' e : P, red d d' -> red (imp_elim e d) (imp_elim e d')
  | red_cnj_intro_1 :
      forall d d' e : P, red d d' -> red (cnj_intro d e) (cnj_intro d' e)
  | red_cnj_intro_2 :
      forall d d' e : P, red d d' -> red (cnj_intro e d) (cnj_intro e d')
  | red_cnj_elim1 :
      forall d d' : P, red d d' -> red (cnj_elim1 d) (cnj_elim1 d')
  | red_cnj_elim2 :
      forall d d' : P, red d d' -> red (cnj_elim2 d) (cnj_elim2 d')
  | red_dsj_intro1 :
      forall (d d' : P) (p : F),
      red d d' -> red (dsj_intro1 p d) (dsj_intro1 p d')
  | red_dsj_intro2 :
      forall (d d' : P) (p : F),
      red d d' -> red (dsj_intro2 p d) (dsj_intro2 p d')
  | red_dsj_elim_1 :
      forall d d' e f : P, red d d' -> red (dsj_elim d e f) (dsj_elim d' e f)
  | red_dsj_elim_2 :
      forall d d' e f : P, red d d' -> red (dsj_elim e d f) (dsj_elim e d' f)
  | red_dsj_elim_3 :
      forall d d' e f : P, red d d' -> red (dsj_elim e f d) (dsj_elim e f d')
  | red_uvq_intro :
      forall d d' : P, red d d' -> red (uvq_intro d) (uvq_intro d')
  | red_uvq_elim :
      forall (d d' : P) (t : T),
      red d d' -> red (uvq_elim t d) (uvq_elim t d')
  | red_exq_intro :
      forall (d d' : P) (t : T) (p : F),
      red d d' -> red (exq_intro p t d) (exq_intro p t d')
  | red_exq_elim_1 :
      forall d d' e : P, red d d' -> red (exq_elim d e) (exq_elim d' e)
  | red_exq_elim_2 :
      forall d d' e : P, red d d' -> red (exq_elim e d) (exq_elim e d').

Infix "-->" := red (left associativity, at level 50).

End reduction.

