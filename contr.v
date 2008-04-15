(** Proof Reflection in Coq ; contr.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export objects.

Set Implicit Arguments.

Section contr_prf.

Variable l1 l2 : list nat.

Let P := prf l1 l2.

Fixpoint contr (n i : nat) {struct i} : nat :=
  match n, i with
  | O, i' => pred i'
  | S n', O => 0
  | S n', S i' => S (contr n' i')
  end.

Definition contr_hyp : nat -> P -> P := map_prf_hyp contr.

End contr_prf.
