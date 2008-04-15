(** Proof Reflection in Coq ; ND_unique_types.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export check_sound.

Set Implicit Arguments.

Section uniqueness_of_types.

Variable l1 l2 : list nat.

Let P := prf l1 l2.
Let F := frm l1 l2.
Let T := trm l1.

Lemma unique_types :
 forall (G : list F) (d : P) (p q : F), ND G d p -> ND G d q -> p = q.
Proof.
intros G d p q H H0.
assert (H1 := ND2check H).
assert (H2 := ND2check H0).
rewrite H1 in H2; injection H2; exact (fun h => h).
Qed.

End uniqueness_of_types.