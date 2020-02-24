From Coq Require Import
     ssreflect
.

From MTC Require Import
     Algebra
     Functor
.

(**
Because [typeEquality] is a binary operation, its return type is curried: it
expects another extensible type (a value of type [Fix T]), and returns a [bool]
indicating whether that extensible type is equal to the extensible type being
folded.
 *)
Definition TypeEqualityResult
           T
  := Fix T -> bool.

(** Tag for [TypeEquality]-related [ProgramAlgebra]s *)
Variant ForTypeEquality := .

(**
The [typeEquality] operation is defined as the fold of its [ProgramAlgebra].
 *)
Definition typeEquality
           {T}
           {typeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
  : Fix T -> TypeEqualityResult T
  := mendlerFold programAlgebra.

Definition TypeEqualityCorrectnessStatement
           {T} `{Functor T}
           {typeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
           (tau : Fix T)
  : Prop
  := forall tau',
    typeEquality tau tau' = true ->
    tau = tau'.

Variant ForTypeEqualityCorrectness := .

Lemma typeEqualityCorrectness
      {T} `{Functor T}
      {typeEquality__T :
         ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
      `{PA : ! ProofAlgebra ForTypeEqualityCorrectness T
               (sig TypeEqualityCorrectnessStatement)}
  : forall tau, TypeEqualityCorrectnessStatement tau.
Proof.
  move => tau.
  apply (Induction tau).
Qed.
