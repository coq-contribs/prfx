(** Proof Reflection in Coq ; exch.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export objects.

Set Implicit Arguments.

Section exch_prf.

Variable l1 l2 : list nat.

Let P := prf l1 l2.

(* (exch n n)=(S n), (exch n (S n))=n, otherwise (exch n m)=m, see lemma's below *)

Fixpoint exch (n i : nat) {struct i} : nat :=
  match n, i with
  | O, O => 1
  | O, S O => 0
  | O, i' => i' (*i'>1*)
  | S n', O => 0
  | S n', S i' => S (exch n' i')
  end.

Definition exch_hyp : nat -> P -> P := map_prf_hyp exch.

Lemma exch_ok1 : forall n : nat, exch n n = S n.
Proof.
simple induction n; simpl in |- *.
reflexivity.
intros n' IH.
rewrite IH.
reflexivity.
Qed.

Lemma exch_ok2 : forall n : nat, exch n (S n) = n.
simple induction n; simpl in |- *.
reflexivity.
intro n'.
case n'.
reflexivity.
intros n'' IH.
rewrite IH.
reflexivity.
Qed.

Lemma exch_ok3 : forall i n : nat, n <> i -> S n <> i -> exch n i = i.
Proof.
simple induction i.
simple destruct n.
intro H.
apply False_ind.
apply H.
reflexivity.
reflexivity.
intros i' IH n.
case n.
case i'.
intros H H0.
apply False_ind.
apply H0.
reflexivity.
reflexivity.
intros n' H H0.
simpl in |- *.
rewrite (IH n').
reflexivity.
red in |- *.
intro H1.
apply H.
rewrite H1.
reflexivity.
red in |- *.
intro H1.
apply H0.
rewrite H1.
reflexivity.
Qed.

End exch_prf.
