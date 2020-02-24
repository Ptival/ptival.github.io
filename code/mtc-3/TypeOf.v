From MTC Require Import
     Algebra
.

(**
For a given extensible type [T], the [typeOf] operation will either return a
concrete type [Some tau], or will fail and return [None] if the input is
ill-typed.
 *)
Definition TypeOfResult T := option (Fix T).

(** Tag for [TypeOf]-related [ProgramAlgebra]s *)
Variant ForTypeOf := .

(**
The [typeOf] operation is defined as the fold of its [ProgramAlgebra].
 *)
Definition typeOf
           {E T}
           {typeOf__E : ProgramAlgebra ForTypeOf E (TypeOfResult T)}
  : Fix E -> TypeOfResult T
  := mendlerFold programAlgebra.
