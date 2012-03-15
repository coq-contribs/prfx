(** Proof Reflection in Coq ; objects.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export indices.

Set Implicit Arguments.

Section objects.

Variable l1 l2 : list nat.

Unset Elimination Schemes. (* Default trm_ind is useless *)

Inductive trm : Set :=
  | var : nat -> trm
  | fun_ : forall i : index l1, listn trm (select i) -> trm.

(*
trm_ind
     : (P:(trm->Prop))
        ((n:nat)(P (var n)))
        ->((i:(index l1); l:(listn trm (select_expl nat l1 i)))
            (P (fun l)))
        ->(t:trm)(P t)
*)

Definition trms := listn trm.
Definition emp := niln trm.

Section ip1.

Variable P : trm -> Prop.
Variable P0 : forall n : nat, trms n -> Prop.
Hypothesis h : forall n : nat, P (var n).
Hypothesis
  h0 :
    forall (i : index l1) (l : trms (select i)), P0 l -> P (fun_ i l).
Hypothesis h1 : P0 emp.
Hypothesis
  h2 :
    forall (n : nat) (t : trm),
    P t -> forall l : trms n, P0 l -> P0 (consn t l).

Fixpoint trm_ind' (t : trm) : P t :=
  match t as x return (P x) with
  | var n => h n
  | fun_ i l => h0 i (listn_ind P0 h1 (fun n0 t0 v0 h => h2 (trm_ind' t0) h) l)
  end.

End ip1.

Section ip2.

Variable P : trm -> Prop.
Let P0 (n : nat) (l : trms n) : Prop := forall t : trm, inn t l -> P t.
Hypothesis h : forall n : nat, P (var n).
Hypothesis
  h0 :
    forall (i : index l1) (l : trms (select i)), P0 l -> P (fun_ i l).
Let h1 : P0 emp := fun t => False_ind (P t).
Let h2 (n : nat) (t : trm) (d : P t) (l : trms n) (d0 : P0 l) :
  P0 (consn t l) :=
  fun u d1 =>
  or_ind (fun d2 : u = t => eq_ind_r (fun t0 => P t0) d d2)
    (fun d2 : inn u l => d0 u d2) d1.

Definition trm_ind := trm_ind' P P0 h h0 h1 h2.

End ip2.

Set Elimination Schemes.

Inductive frm : Set :=
  | top : frm
  | bot : frm
  | rel : forall i : index l2, trms (select i) -> frm
  | imp : frm -> frm -> frm
  | cnj : frm -> frm -> frm
  | dsj : frm -> frm -> frm
  | uvq : frm -> frm
  | exq : frm -> frm.

Inductive prf : Set :=
  | top_intro : prf
  | hyp : nat -> prf
  | bot_elim : prf -> frm -> prf
  | imp_intro : frm -> prf -> prf
  | imp_elim : prf -> prf -> prf
  | cnj_intro : prf -> prf -> prf
  | cnj_elim1 : prf -> prf
  | cnj_elim2 : prf -> prf
  | dsj_intro1 : frm -> prf -> prf
  | dsj_intro2 : frm -> prf -> prf
  | dsj_elim : prf -> prf -> prf -> prf
  | uvq_intro : prf -> prf
  | uvq_elim : trm -> prf -> prf
  | exq_intro : frm -> trm -> prf -> prf
  | exq_elim : prf -> prf -> prf.

Section map_trm_sec.

Variable g : nat -> nat -> nat.

Fixpoint map_trm (n : nat) (t : trm) {struct t} : trm :=
  match t with
  | var i => var (g n i)
  | fun_ i l => fun_ i (mapn (map_trm n) l)
  end.

End map_trm_sec.

Section map_var_sec.

Variable g : nat -> trm -> trm.

Fixpoint map_frm_var (n : nat) (p : frm) {struct p} : frm :=
  match p with
  | top => top
  | bot => bot
  | rel i l => rel i (mapn (g n) l)
  | imp q r => imp (map_frm_var n q) (map_frm_var n r)
  | cnj q r => cnj (map_frm_var n q) (map_frm_var n r)
  | dsj q r => dsj (map_frm_var n q) (map_frm_var n r)
  | uvq q => uvq (map_frm_var (S n) q)
  | exq q => exq (map_frm_var (S n) q)
  end.

Fixpoint map_prf_var (n : nat) (d : prf) {struct d} : prf :=
  match d with
  | top_intro => top_intro
  | hyp i => hyp i
  | bot_elim e p => bot_elim (map_prf_var n e) (map_frm_var n p)
  | imp_intro p e => imp_intro (map_frm_var n p) (map_prf_var n e)
  | imp_elim e f => imp_elim (map_prf_var n e) (map_prf_var n f)
  | cnj_intro e f => cnj_intro (map_prf_var n e) (map_prf_var n f)
  | cnj_elim1 e => cnj_elim1 (map_prf_var n e)
  | cnj_elim2 e => cnj_elim2 (map_prf_var n e)
  | dsj_intro1 p e => dsj_intro1 (map_frm_var n p) (map_prf_var n e)
  | dsj_intro2 p e => dsj_intro2 (map_frm_var n p) (map_prf_var n e)
  | dsj_elim e e1 e2 =>
      dsj_elim (map_prf_var n e) (map_prf_var n e1) (map_prf_var n e2)
  | uvq_intro e => uvq_intro (map_prf_var (S n) e)
  | uvq_elim t e => uvq_elim (g n t) (map_prf_var n e)
  | exq_intro p t e =>
      exq_intro (map_frm_var (S n) p) (g n t) (map_prf_var n e)
  | exq_elim e f => exq_elim (map_prf_var n e) (map_prf_var (S n) f)
  end.

End map_var_sec.

Section map_hyp_sec.

Variable g : nat -> nat -> nat.

Fixpoint map_prf_hyp (n : nat) (d : prf) {struct d} : prf :=
  match d with
  | top_intro => top_intro
  | hyp i => hyp (g n i)
  | bot_elim d p => bot_elim (map_prf_hyp n d) p
  | imp_intro p d => imp_intro p (map_prf_hyp (S n) d)
  | imp_elim d e => imp_elim (map_prf_hyp n d) (map_prf_hyp n e)
  | cnj_intro d e => cnj_intro (map_prf_hyp n d) (map_prf_hyp n e)
  | cnj_elim1 d => cnj_elim1 (map_prf_hyp n d)
  | cnj_elim2 d => cnj_elim2 (map_prf_hyp n d)
  | dsj_intro1 p d => dsj_intro1 p (map_prf_hyp n d)
  | dsj_intro2 p d => dsj_intro2 p (map_prf_hyp n d)
  | dsj_elim d e1 e2 =>
      dsj_elim (map_prf_hyp n d) (map_prf_hyp (S n) e1)
        (map_prf_hyp (S n) e2)
  | uvq_intro d => uvq_intro (map_prf_hyp n d)
  | uvq_elim t d => uvq_elim t (map_prf_hyp n d)
  | exq_intro p t d => exq_intro p t (map_prf_hyp n d)
  | exq_elim d e => exq_elim (map_prf_hyp n d) (map_prf_hyp (S n) e)
  end.

End map_hyp_sec.

Section boolpreds.

Fixpoint trm_eqb (t u : trm) {struct u} : bool :=
  match t, u with
  | var i, var j => nat_eqb i j
  | fun_ i l, fun_ j w => index_eqb l1 i j && listn_eqb trm_eqb l w
  | _, _ => false
  end.

Definition trms_eqb := listn_eqb trm_eqb.

Fixpoint frm_eqb (p q : frm) {struct q} : bool :=
  match p, q with
  | top, top => true
  | bot, bot => true
  | rel i l, rel j w => index_eqb l2 i j && trms_eqb l w
  | imp c d, imp e f => frm_eqb c e && frm_eqb d f
  | cnj c d, cnj e f => frm_eqb c e && frm_eqb d f
  | dsj c d, dsj e f => frm_eqb c e && frm_eqb d f
  | uvq c, uvq d => frm_eqb c d
  | exq c, exq d => frm_eqb c d
  | _, _ => false
  end.

Fixpoint free_inb_trm (n : nat) (t : trm) {struct t} : bool :=
  match t with
  | var m => nat_eqb n m
  | fun_ i l => mapn_orb (free_inb_trm n) l
  end.

Definition free_inb_trms (n k : nat) (l : trms k) :=
  mapn_orb (free_inb_trm n) l.

Fixpoint free_inb_frm (n : nat) (p : frm) {struct p} : bool :=
  match p with
  | top => false
  | bot => false
  | rel i l => free_inb_trms n l
  | imp q r => free_inb_frm n q || free_inb_frm n r
  | cnj q r => free_inb_frm n q || free_inb_frm n r
  | dsj q r => free_inb_frm n q || free_inb_frm n r
  | uvq q => free_inb_frm (S n) q
  | exq q => free_inb_frm (S n) q
  end.

End boolpreds.

End objects.

Notation Var := (var _) (only parsing).
Notation Top := (top _ _) (only parsing).
Notation Bot := (bot _ _) (only parsing).
Notation Hyp := (hyp _ _) (only parsing).
Notation Top_intro := (top_intro _ _) (only parsing).
