From MTC Require Import
     Algebra
     Functor
     IndexedAlgebra
     IndexedFunctor
.

Record TypedExpr
       T E
       `{Functor T} `{Functor E}
  :=
    {
      type : Expression T;
      expr : Expression E;
    }.
Arguments type {T E _ _}.
Arguments expr {T E _ _}.
