From Coq Require Import
     ssreflect
.

From MTC Require Import
     Algebra
     BooleanType
     Boolean
     IndexedAlgebra
     IndexedFunctor
     IndexedSum1
     NaturalType
     Natural
     Sum1
     WellTypedValue
     WellTypedValueProjection
.

Definition TypeLanguage  := (BooleanType + NaturalType)%Sum1.
Definition ValueLanguage := (Boolean + Natural)%Sum1.

Definition WellTypedValue
  : (TypedExpr TypeLanguage ValueLanguage)-indexedPropFunctor
  := (WellTypedValue__Boolean + WellTypedValue__Natural)%IndexedSum1.

(**
Let's keep a test here to make sure the tactic still works!
 *)
Goal
  IndexedProofAlgebra ForWellTypedValueProjection
  WellTypedValue__Natural
  (WellTypedValueProjectionStatement
     WellTypedValue__Boolean
     booleanType
     WellTypedValue
  ).

  wellTypedValueProjection__Other.

  (* If ^ this does not succeed, comment it out and debug with: *)

  (* constructor. *)
  (* rewrite /IndexedAlgebra. *)
  (* move => i []. *)
  (* rewrite /WellTypedValueProjectionStatement /=. *)
  (* move => *. *)
  (* match goal with *)
  (* | [ A : proj1_sig ?T = _ *)
  (*   , B : proj1_sig ?tau = _ *)
  (*     |- _ *)
  (*   ] => move : A B *)
  (* end. *)
  (* move ->. *)
  (* match goal with *)
  (* | [ |- ?l = ?r -> _ ] => *)
  (*   move /(wrapF_inversion (unwrapUP' l) (unwrapUP' r)) => // *)
  (* end. *)

Qed.
