(** Proof Reflection in Coq ; list.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export List.
Require Export Bool.
Require Export nat_eqb.
Require Export Eqdep.

Set Implicit Arguments.

Section preliminaries.

Variable A : Set.

Inductive opt : Set :=
  | val : A -> opt
  | err : opt.

Fixpoint opt_nth (n : nat) (l : list A) {struct l} : opt :=
  match n, l with
  | O, a :: _ => val a
  | S m, _ :: t => opt_nth m t
  | _, nil => err
  end.

End preliminaries.

Notation Nil := nil (only parsing).
Notation Proj1 := (proj1 (B:=_)) (only parsing).
Notation Proj2 := (proj2 (B:=_)) (only parsing).
Notation Conj := (conj (B:=_)) (only parsing).
Notation Err := (err _) (only parsing).


Section listns.

Variable A : Set.

Inductive listn : nat -> Set :=
  | niln : listn 0
  | consn : forall n : nat, A -> listn n -> listn (S n).

Variable A_eqb : A -> A -> bool.

Fixpoint listn_eqb (x : nat) (l : listn x) (y : nat) 
 (m : listn y) {struct m} : bool :=
  match l, m with
  | niln, niln => true
  | consn x0 a l0, consn y0 b m0 => A_eqb a b && listn_eqb l0 m0
  | _, _ => false
  end.

Hypothesis A_eqb_refl : forall a : A, A_eqb a a = true.

Lemma listn_eqb_refl : forall (n : nat) (l : listn n), listn_eqb l l = true.
Proof.
induction l.
reflexivity.
simpl in |- *.
rewrite A_eqb_refl.
rewrite IHl.
reflexivity.
Qed.

Lemma eq_dep_niln :
 forall (n : nat) (l : listn n), n = 0 -> eq_dep _ _ n l 0 niln.
Proof.
simple destruct l.
trivial.
intros. discriminate.
Qed.

Lemma eq_niln : forall l : listn 0, l = niln.
Proof.
intros.
apply eq_dep_eq with (P := listn).
apply eq_dep_niln.
reflexivity.
Qed.

Lemma eq_dep_consn :
 forall (n : nat) (l : listn n) (m : nat),
 n = S m ->
 exists t : A, (exists w : listn m, eq_dep _ _ n l (S m) (consn t w)).
Proof.
simple destruct l.
intros.
discriminate.
intros n' t w m H.
cut (n' = m); auto.
intro c.
generalize w.
clear w.
dependent rewrite c.
intro w.
split with t.
split with w.
apply eq_dep_intro.
Qed.

Lemma eq_consn :
 forall (n : nat) (l : listn (S n)),
 exists t : A, (exists w : listn n, l = consn t w).
Proof.
intros n l.
elim (eq_dep_consn l (refl_equal (S n))).
intros t H.
elim H.
intros w H0.
split with t.
split with w.
apply eq_dep_eq with (P := listn).
exact H0.
Qed.

Hypothesis A_eqb_dec : forall a a' : A, A_eqb a a' = true -> a = a'.

Lemma listn_eqb_dec :
 forall (n : nat) (l m : listn n), listn_eqb l m = true -> l = m.
Proof.
induction l.
intros m h.
rewrite (eq_niln m).
reflexivity.
intro m.
elim (eq_consn m); intros t h; elim h; clear h; intros m' h.
rewrite h.
simpl in |- *.
intro h0.
elim andb_prop with (1 := h0); intros h1 h2.
rewrite (A_eqb_dec h1).
rewrite (IHl m' h2).
reflexivity.
Qed.

Fixpoint inn (x : A) (n : nat) (l : listn n) {struct l} : Prop :=
  match l with
  | niln => False
  | consn n a l0 => x = a \/ inn x l0
  end.

End listns.

Section mapns.

Variable A B : Set.
Variable f : A -> B.

Fixpoint mapn (n : nat) (l : listn A n) {struct l} : 
 listn B n :=
  match l in (listn _ n) return (listn B n) with
  | niln => niln B
  | consn n a t => consn (f a) (mapn t)
  end.

Variable p : A -> bool.

Fixpoint mapnb (c : bool) (b : bool -> bool -> bool) 
 (n : nat) (l : listn A n) {struct l} : bool :=
  match l with
  | niln => c
  | consn n a t => b (p a) (mapnb c b t)
  end.

Definition mapn_orb := mapnb false orb.
Definition mapn_andb := mapnb true andb.

Lemma mapnb_orb_false :
 forall (n : nat) (l : listn A n),
 mapn_orb l = false -> forall a : A, inn a l -> p a = false.
Proof.
induction l.
intros h a h0; elim h0.
unfold mapn_orb in |- *; simpl in |- *; intros h a0 h0;
 elim orb_false_elim with (1 := h); intros h1 h2; elim h0; 
 intro h3.
rewrite h3; exact h1.
exact (IHl h2 a0 h3).
Qed.

End mapns.

Section more_on_lists.

Variable A B : Set.
Variable f g : A -> B.

Lemma map_app :
 forall l1 l2 : list A, map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
intros l1 l2.
elim l1.
reflexivity.
intros a l1' IH.
simpl in |- *.
rewrite IH.
reflexivity.
Qed.

Lemma length_map : forall l : list A, length l = length (map f l).
Proof.
simple induction l.
reflexivity.
intros a l' IH.
simpl in |- *.
rewrite IH.
reflexivity.
Qed.

Hypothesis ee : forall x : A, f x = g x.

Lemma map_feeg : forall l : list A, map f l = map g l.
Proof.
induction l.
reflexivity.
simpl in |- *; rewrite ee; rewrite IHl; reflexivity.
Qed.

Lemma mapn_feeg : forall (n : nat) (l : listn A n), mapn f l = mapn g l.
Proof.
induction l.
reflexivity.
simpl in |- *; rewrite ee; rewrite IHl; reflexivity.
Qed.

Lemma mapn_inn :
 forall (n : nat) (l : listn A n),
 (forall x : A, inn x l -> f x = g x) -> mapn f l = mapn g l.
Proof.
intros n l h.
induction l.
reflexivity.
simpl in |- *.
rewrite h.
rewrite IHl.
reflexivity.
intros x h0.
apply h.
right; exact h0.
left; reflexivity.
Qed.

Variable C : Set.
Variable f1 : A -> B.
Variable f2 : B -> C.

Lemma map_map :
 forall l : list A, map f2 (map f1 l) = map (fun x => f2 (f1 x)) l.
Proof.
simple induction l.
reflexivity.
intros a t IH.
simpl in |- *.
rewrite IH.
reflexivity.
Qed.

Lemma mapn_mapn :
 forall (n : nat) (l : listn A n),
 mapn f2 (mapn f1 l) = mapn (fun x => f2 (f1 x)) l.
Proof.
induction l.
reflexivity.
simpl in |- *; rewrite IHl; reflexivity.
Qed.

Lemma mapn_id : forall (n : nat) (l : listn A n), mapn (fun x => x) l = l.
Proof.
induction l.
reflexivity.
simpl in |- *; rewrite IHl; reflexivity.
Qed.

End more_on_lists.