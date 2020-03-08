From MTC Require Import
     Algebra
     Functor
.

(**
We will use this as an alias for the return type of the [Eval] operation.  While
it is just [Expression], the idea is that we could decide to change it later, so
all [ProgramAlebra]s should use the alias.
 *)
Definition EvalResult
           V `{Functor V}
  := Expression V.

(** Tag for [Eval]-related [ProgramAlgebra]s *)
Variant ForEval := .

(**
The [eval] operation is defined as the fold of its [ProgramAlgebra].
 *)
Definition eval
           {E V}
           `{Functor V}
           {eval__E : ProgramAlgebra ForEval E (EvalResult V)}
  : Fix E -> EvalResult V
  := mendlerFold programAlgebra.
