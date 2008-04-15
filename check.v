(** Proof Reflection in Coq ; check.v ; 050128 ; Dimitri Hendriks; Coq 8.0pl1 *)

Require Export subst.

Set Implicit Arguments.

Section checksec.

Variable l1 l2 : list nat.

Let T := trm l1.
Let Ts := trms l1.
Let F := frm l1 l2.
Let P := prf l1 l2.


Fixpoint check (G : list F) (h : P) {struct h} : opt F :=
  match h with
  | top_intro => val (top _ _)
  | hyp n => opt_nth n G
  | bot_elim h0 p =>
      match check G h0 with
      | val bot => val p
      | _ => err _
      end
  | imp_intro p h0 =>
      match check (p :: G) h0 with
      | val p0 => val (imp p p0)
      | _ => err _
      end
  | imp_elim h1 h2 =>
      match check G h1, check G h2 with
      | val (imp p p0), val p' => if frm_eqb p p' then val p0 else err _
      | _, _ => err _
      end
  | cnj_intro h1 h2 =>
      match check G h1, check G h2 with
      | val p1, val p2 => val (cnj p1 p2)
      | _, _ => err _
      end
  | cnj_elim1 h0 =>
      match check G h0 with
      | val (cnj p _) => val p
      | _ => err _
      end
  | cnj_elim2 h0 =>
      match check G h0 with
      | val (cnj _ p) => val p
      | _ => err _
      end
  | dsj_intro1 p h0 =>
      match check G h0 with
      | val p0 => val (dsj p0 p)
      | _ => err _
      end
  | dsj_intro2 p h0 =>
      match check G h0 with
      | val p0 => val (dsj p p0)
      | _ => err _
      end
  | dsj_elim h0 h1 h2 =>
      match check G h0 with
      | val (dsj p1 p2) =>
          match check (p1 :: G) h1, check (p2 :: G) h2 with
          | val c, val c' => if frm_eqb c c' then val c else err _
          | _, _ => err _
          end
      | _ => err _
      end
  | uvq_intro h0 =>
      match check (lift_cxt 0 G) h0 with
      | val p => val (uvq p)
      | _ => err _
      end
  | uvq_elim t h0 =>
      match check G h0 with
      | val (uvq p) => val (subst_frm 0 p t)
      | _ => err _
      end
  | exq_intro p t h0 =>
      match check G h0 with
      | val q => if frm_eqb (subst_frm 0 p t) q then val (exq p) else err _
      | _ => err _
      end
  | exq_elim h1 h2 =>
      match check G h1 with
      | val (exq q) =>
          match check (q :: lift_cxt 0 G) h2 with
          | val r => if free_inb_frm 0 r then err _ else val (proj_frm 0 r)
          | _ => err _
          end
      | _ => err _
      end
  end.


End checksec.

