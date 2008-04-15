(** Proof Reflection in Coq ; nat_eqb.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Fixpoint nat_eqb (n m : nat) {struct m} : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => nat_eqb n' m'
  | _, _ => false
  end.

Lemma nat_eqb_dec : forall n m : nat, nat_eqb n m = true -> n = m.
Proof.
simple induction n.
simple destruct m.
trivial.
intros. discriminate.
intros n' IH m.
case m.
intros. discriminate.
intros m' H.
rewrite <- (IH m' H).
reflexivity.
Qed.

Lemma nat_eqb_refl : forall n : nat, nat_eqb n n = true.
Proof. simple induction n; auto. Qed.