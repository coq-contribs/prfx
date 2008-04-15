(** Proof Reflection in Coq ; lift.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export objects.

Set Implicit Arguments.

Section lifting.

Variable l1 l2 : list nat.

Let T := trm l1.
Let Ts := trms l1.
Let F := frm l1 l2.
Let P := prf l1 l2.

Fixpoint lift (n i : nat) {struct n} : nat :=
  match n with
  | O => S i
  | S n' => match i with
            | O => 0
            | S i' => S (lift n' i')
            end
  end.

(** `projection': the reverse of lifting when [n] unequal to [i] *)

Fixpoint proj (n i : nat) {struct i} : nat :=
  match i with
  | O => 0
  | S i' => match n with
            | O => i'
            | S n' => S (proj n' i')
            end
  end.

Definition lift_trm : nat -> T -> T := map_trm lift.
Definition proj_trm : nat -> T -> T := map_trm proj.

Definition lift_trms n := mapn (lift_trm n).
Definition proj_trms n := mapn (proj_trm n).

Definition lift_frm : nat -> F -> F := map_frm_var lift_trm.
Definition proj_frm : nat -> F -> F := map_frm_var proj_trm.

Definition lift_cxt n := map (lift_frm n).

Definition lift_var_prf : nat -> P -> P := map_prf_var lift_trm.

Definition lift_hyp_prf : nat -> P -> P := map_prf_hyp lift.

Variable A : Set.

Fixpoint shiftVAR (VAR : nat -> A) (n : nat) {struct n} : 
 nat -> A :=
  match n with
  | O => VAR
  | S n' => shiftVAR (fun p => VAR (S p)) n'
  end.

End lifting.