(** Proof Reflection in Coq ; indices.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export Arith.
Require Export Compare_dec.
Require Export list.

(* parts of this file were taken from or inspired by 
   Venanzio Capretta's development of universal algebra in Coq *)

Inductive sigTS (T : Type) (P : T -> Set) : Type :=
    existTS : forall B : T, P B -> sigTS T P.

Inductive empty : Set :=.

Definition from_empty (A : Set) := empty_rec (fun _ => A).

Definition empty_ind' (e : empty) (p : Prop) : p := empty_ind (fun _ => p) e.

Set Implicit Arguments.

Section Sigma_Type_Set.

Variable T : Type.
Variable P : T -> Set.

Definition projTS1 (p : sigTS T P) : T := 
  match p with existTS a _ => a end.

Definition projTS2 (p : sigTS T P) : P (projTS1 p) :=
  match p as p' return (P (projTS1 p')) with
  | existTS _ x => x
  end.

End Sigma_Type_Set.

Section indices.

Variable A : Set.

Fixpoint index (l : list A) : Set :=
  match l with
  | nil => empty
  | _ :: t => (unit + index t)%type
  end.

Fixpoint index_eqb (l : list A) : index l -> index l -> bool :=
  match l return (index l -> index l -> bool) with
  | nil => fun _ => from_empty bool
  | a :: t =>
      fun i j =>
      match i, j with
      | inl _, inl _ => true
      | inr i', inr j' => index_eqb t i' j'
      | _, _ => false
      end
  end.

Lemma index_eqb_refl :
 forall (L : list A) (i : index L), index_eqb L i i = true.
Proof.
simple induction L.
intro H. elim H.
intros a l IH i.
case i.
intro u. case u; reflexivity.
exact IH.
Qed.

Lemma index_eqb_dec :
 forall (L : list A) (i j : index L), index_eqb L i j = true -> i = j.
Proof.
simple induction L.
simple destruct i.
intros a l IH i.
case i.
intros u j.
case u.
case j.
intro u2.
case u2.
reflexivity.
intros. discriminate.
intros i' j.
case j.
intros. discriminate.
intros j' H.
rewrite (IH i' j' H).
reflexivity.
Qed.

Definition ltll (n : nat) (l : list A) := n < length l.

Fixpoint index_inj (n : nat) (l : list A) {struct l} : 
 ltll n l -> index l :=
  match l as l' return (ltll n l' -> index l') with
  | nil => fun p => False_rec empty (lt_n_O n p)
  | a :: t =>
      match n as m return (ltll m (a :: t) -> unit + index t) with
      | O => fun _ => inl (index t) tt
      | S n' => fun p => inr unit (index_inj (lt_S_n n' (length t) p))
      end
  end.

Section index_L.

Variable L : list A.
Let len := length L.

Lemma ltll_dec_opaque : forall n : nat, {ltll n L} + {~ ltll n L}.
Proof.
intro n.
case (le_gt_dec (S n) len); intro H.
left.
exact H.
right.
unfold not in |- *.
intro H0.
exact (le_not_gt (S n) len H0 H).
Qed.

(*
Transparent le_gt_dec.
Transparent le_not_gt.
Transparent le_lt_dec.
Transparent ltll_dec_opaque.
Eval Cbv Beta Delta -[length] Iota in ltll_dec_opaque.
*)

Definition ltll_dec (n : nat) : {ltll n L} + {~ ltll n L} :=
  match
    (fix F (n0 : nat) : {S n <= n0} + {S n0 <= S n} :=
       match n0 as n1 return ({S n <= n1} + {S n1 <= S n}) with
       | O => right (S n <= 0) (lt_le_S 0 (S n) (lt_O_Sn n))
       | S n1 =>
           match
             (fix F0 (n2 : nat) : forall m : nat, {n2 <= m} + {S m <= n2} :=
                match
                  n2 as n3 return (forall m : nat, {n3 <= m} + {S m <= n3})
                with
                | O => fun m : nat => left (S m <= 0) (le_O_n m)
                | S n3 =>
                    fun m : nat =>
                    (fix F1 (n4 : nat) : {S n3 <= n4} + {S n4 <= S n3} :=
                       match
                         n4 as n5 return ({S n3 <= n5} + {S n5 <= S n3})
                       with
                       | O =>
                           right (S n3 <= 0) (lt_le_S 0 (S n3) (lt_O_Sn n3))
                       | S n5 =>
                           match
                             F0 n3 n5
                             return ({S n3 <= S n5} + {S (S n5) <= S n3})
                           with
                           | left y =>
                               left (S (S n5) <= S n3) (le_n_S n3 n5 y)
                           | right y =>
                               right (S n3 <= S n5) (le_n_S (S n5) n3 y)
                           end
                       end) m
                end) n n1 return ({S n <= S n1} + {S (S n1) <= S n})
           with
           | left y => left (S (S n1) <= S n) (le_n_S n n1 y)
           | right y => right (S n <= S n1) (le_n_S (S n1) n y)
           end
       end) (length L)
    return ({S n <= length L} + {S n <= length L -> False})
  with
  | left h => left (S n <= length L -> False) h
  | right h =>
      right (S n <= length L) (fun h0 => le_not_lt (S n) (length L) h0 h)
  end.

Definition nat2index_sig (n : nat) : sigTS Set (fun B : Set => B) :=
  match ltll_dec n with
  | left p => existTS Set (fun B : Set => B) (index L) (index_inj p)
  | _ => existTS Set (fun B : Set => B) unit tt
  end.

Definition nat2index (n : nat) : Set := projTS1 (nat2index_sig n).

Definition nat_inj (n : nat) : nat2index n := projTS2 (nat2index_sig n).

Fixpoint index2nat (L : list A) : index L -> nat :=
  match L return (index L -> nat) with
  | nil => fun e => from_empty nat e
  | a :: t =>
      fun i => match i with
               | inl tt => 0
               | inr i' => S (index2nat t i')
               end
  end.

End index_L.

Fixpoint select_expl (l : list A) : index l -> A :=
  match l as l' return (index l' -> A) with
  | nil => empty_rec (fun _ => A)
  | h :: t =>
      fun i : unit + index t =>
      match i with
      | inl tt => h
      | inr i' => select_expl t i'
      end
  end.

End indices.

Infix "}-" := nat_inj (left associativity, at level 50).

Notation select := (select_expl _) (only parsing).
