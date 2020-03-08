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
           T `{Functor T}
  := Expression T -> bool.

(** Tag for [TypeEquality]-related [ProgramAlgebra]s *)
Variant ForTypeEquality := .

(**
The [typeEquality] operation is defined as the fold of its [ProgramAlgebra].
 *)
Definition typeEquality
           {T} `{Functor T}
           {typeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
  : Fix T -> TypeEqualityResult T
  := mendlerFold programAlgebra.

Definition TypeEqualityCorrectnessStatement
           {T} `{Functor T}
           {typeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
           (tau : Fix T) (UP'__tau : UP' tau)
  : Prop
  := forall tau',
    typeEquality tau tau' = true ->
    tau = proj1_sig tau'.

Variant ForTypeEqualityCorrectness := .

Lemma typeEqualityCorrectness
      {T} `{Functor T}
      {TypeEquality__T :
         ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
      `{TypeEqualityCorrectness__T :
          ! ProofAlgebra ForTypeEqualityCorrectness T
            (sig (PropUP' TypeEqualityCorrectnessStatement))}
      `{! WellFormedProofAlgebra TypeEqualityCorrectness__T}
  : forall (tau : Expression T),
    TypeEqualityCorrectnessStatement (proj1_sig tau) (proj2_sig tau).
Proof.
  move => [tau UP'__tau].
  pose proof (Induction tau UP'__tau).
  apply : (proj2_sig (Induction tau UP'__tau)).
Qed.
