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

(** FIXME: document this *)
Definition WellTypedValueProj1TypeStatement
           {T V}
           `{Functor T} `{Functor V}
           (WTV : (TypedExpr T V)-indexedPropFunctor)
           (te : TypedExpr T V)
  : Prop
  := forall tau' UP',
    tau' = proj1_sig (type te) ->
    IndexedFix WTV
               {|
                 type := exist _ tau' UP';
                 expr := expr te;
               |}.

Variant ForWellTypedValueProj1Type := .

Definition wellTypedValueProj1Type
           {T V}
           `{Functor T} `{Functor V}
           (WTV : (TypedExpr T V)-indexedPropFunctor)
           `{IndexedFunctor (TypedExpr T V) WTV}
           `{A : ! IndexedProofAlgebra
                   ForWellTypedValueProj1Type
                   WTV
                   (WellTypedValueProj1TypeStatement WTV)}
  :=  indexedFold indexedProofAlgebra.
