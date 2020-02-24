From MTC Require Import
     Algebra
     Functor
     IndexedAlgebra
     IndexedFunctor
.

Record TypedExpr T E : Set :=
  {
    type : Fix T;
    expr : Fix E;
  }.
Arguments type {T E}.
Arguments expr {T E}.
