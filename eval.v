(** Proof Reflection in Coq ; eval.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export objects.

Set Implicit Arguments.

Section evaluation.

Variable A : Set.
Variable l1 l2 : list nat.

Let T := trm l1.
Let Ts := trms l1.
Let F := frm l1 l2.
Let P := prf l1 l2.

Definition fun_piT := forall i : index l1, listn A (select i) -> A.

Variable FUN : fun_piT.

Section term_evaluation.

Variable VAR : nat -> A.

Fixpoint eval_trm (t : T) : A :=
  match t with
  | var i => VAR i
  | fun_ i l => FUN i (mapn eval_trm l)
  end.

Definition eval_trms (z : nat) (l : Ts z) := mapn eval_trm l.

End term_evaluation.

Definition insertVAR_O (x : A) (V : nat -> A) (m : nat) :=
  match m with
  | O => x
  | S m' => V m'
  end.

Fixpoint insertVAR (x : A) (V : nat -> A) (n : nat) {struct n} : 
 nat -> A :=
  match n with
  | O => insertVAR_O x V
  | S n' =>
      fun m =>
      match m with
      | O => V 0
      | S m' => insertVAR x (fun p => V (S p)) n' m'
      end
  end.

Section formula_evaluation.

Definition rel_piT :=
  forall i : index l2, listn A (select i) -> Prop.

Variable REL : rel_piT.

Fixpoint eval_frm' (VAR : nat -> A) (p : F) {struct p} : Prop :=
  match p with
  | top => True
  | bot => False
  | rel i l => REL i (eval_trms VAR l)
  | imp q r => eval_frm' VAR q -> eval_frm' VAR r
  | cnj q r => eval_frm' VAR q /\ eval_frm' VAR r
  | dsj q r => eval_frm' VAR q \/ eval_frm' VAR r
  | uvq q => forall x : A, eval_frm' (insertVAR_O x VAR) q
  | exq q => exists x : A, eval_frm' (insertVAR_O x VAR) q
  end.

(* conjunction of evaluated list elements *)

Fixpoint eval_cxt' (VAR : nat -> A) (G : list F) {struct G} : Prop :=
  match G with
  | nil => True
  | p :: g => eval_frm' VAR p /\ eval_cxt' VAR g
  end.

Variable dflt : A.

Definition eval_frm := eval_frm' (fun _ => dflt).
Definition eval_cxt := eval_cxt' (fun _ => dflt).

End formula_evaluation.

End evaluation.

