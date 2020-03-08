From Coq Require Import
     ssreflect
.

From MTC Require Import
     Algebra
     Functor
     IndexedAlgebra
     IndexedFunctor
     IndexedSubFunctor
     WellTypedValue
.

(**
[WellTypedValueProjection] states that [WellTypedValue__F] is the correct handler
for handling type [tau] that satisfies [WellTypedValue__V].  In practice,
[WellTypedValue__F] will be for a given feature, for instance
[WellTypedValue__Boolean], while [WellTypedValue__V] will be the compound well-typed
relation.  This lets us do an inversion of [WellTypedValue__V] where only the
correct well-typed relation is considered.
 *)
Definition WellTypedValueProjectionStatement
           {T V}
           `{Functor T} `{Functor V}
           (WellTypedValue__F : (TypedExpr T V)-indexedPropFunctor)
           (tau : Fix T)
           (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
           (tv : TypedExpr T V)
  : Prop
  := proj1_sig (type tv) = tau ->
     WellTypedValue__F (IndexedFix WellTypedValue__V) tv.

Variant ForWellTypedValueProjection := .

Definition wellTypedValueProjection
           {T V}
           `{Functor T} `{Functor V}
           (WellTypedValue__F : (TypedExpr T V)-indexedPropFunctor)
           (tau : Fix T)
           (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
           `{IndexedFunctor (TypedExpr T V) WellTypedValue__V}
           `{S : ! IndexedSubFunctor WellTypedValue__F WellTypedValue__V}
           `{A : ! IndexedProofAlgebra
                   ForWellTypedValueProjection
                   WellTypedValue__V
                   (WellTypedValueProjectionStatement WellTypedValue__F tau WellTypedValue__V)}
  :=  indexedFold indexedProofAlgebra.

(**
This was obtained by stating one of the goals it tries to solve, say:

IndexedProofAlgebra ForWellTypedValueProjection
  WellTypedValue__Natural
  (WellTypedValueProjectionStatement WellTypedValue__Boolean booleanType WellTypedValue)

and try and prove it as generically as possible.
 *)
Ltac wellTypedValueProjection__Other :=
  constructor;
  rewrite /IndexedAlgebra;
  move => i [];
  rewrite /WellTypedValueProjectionStatement /=;
  move => *;
  match goal with
  | [ A : proj1_sig ?T = _
    , B : proj1_sig ?tau = _
      |- _
    ] => move : A B
  end;
  move ->;
  match goal with
  | [ |- ?l = ?r -> _ ] =>
    move /(wrapF_inversion (unwrapUP' l) (unwrapUP' r)) => //
  end.

Hint Extern 5
     (IndexedProofAlgebra ForWellTypedValueProjection _ _)
=> wellTypedValueProjection__Other : typeclass_instances.
