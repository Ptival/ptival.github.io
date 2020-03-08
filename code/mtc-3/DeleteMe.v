From Coq Require Import MSets.
Require Import List.
Import ListNotations.

Module VarSet := Make(Nat_as_OT).

From Coq Require Import String.

Definition var := VarSet.elt.
Definition type := nat.

Inductive Judgement : Type :=
| judge (v : var) (t : type)
.

Definition ty_ctx := (list Judgement).

Definition disj_vars (s1 s2 : VarSet.t) := VarSet.Empty (VarSet.inter s1 s2).

(* Functions to convert between the different types listed above *)

Fixpoint var_to_varset (v : var) : VarSet.t :=
  VarSet.singleton v.

Coercion var_to_varset : var >-> VarSet.t.

Fixpoint bound_variables (g : ty_ctx) : VarSet.t :=
  match g with
  | nil => VarSet.empty
  | cons (judge v _) g' =>VarSet.union (VarSet.singleton v) (bound_variables g')
  end.
Coercion bound_variables : ty_ctx >-> VarSet.t.

Inductive ctx_join :=
| join_single (g : ty_ctx)
| join_double (g1 g2 : ty_ctx)
              (disjoint_proof : disj_vars g1 g2)
.

Fixpoint coerce_ctx_join (dj : ctx_join) : ty_ctx :=
  match dj with
  | join_single g => g
  | join_double g1 g2 _ => g1 ++ g2
  end.
Coercion coerce_ctx_join : ctx_join >-> ty_ctx.

Fixpoint coerce_judgement_to_ty_ctx (j : Judgement) : ty_ctx :=
  cons j nil.
Coercion coerce_judgement_to_ty_ctx : Judgement >-> ty_ctx.

Set Printing Coercions.

Definition foo (i : Judgement) : VarSet.t := i.

Theorem test x t
  : var_to_varset x = bound_variables (coerce_judgement_to_ty_ctx (judge x t)).
Proof.
  unfold coerce_judgement_to_ty_ctx.
  simpl.
  unfold var_to_varset.
  unfold VarSet.singleton.
  destruct var.
  simpl.
  reflexivity.
Qed.

Inductive expr_has_type : ty_ctx -> nat -> type -> Prop :=
(* General Expressions *)
| ty_var (g : ty_ctx) (x : var) (t : type)
         (xfree : disj_vars x g)
  : expr_has_type (join_double (judge x t) g xfree) x t
.

Set Printing All.
