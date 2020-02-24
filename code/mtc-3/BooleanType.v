From Coq Require Import
     ssreflect
.

From MTC Require Import
     Algebra
     Functor
     SubFunctor
     TypeEquality
.

Local Open Scope SubFunctor.

Inductive BooleanType (A : Set) : Set :=
| MkBooleanType : BooleanType A
.
Arguments MkBooleanType {A}.

Global Instance Functor__BooleanType
  : Functor BooleanType
  := {| fmap := fun A B f 'MkBooleanType => MkBooleanType |}.

Definition booleanType
           {T}
           `{Functor T}
           `{T supports BooleanType}
  : Fix T
  := injectF MkBooleanType.

Definition isBooleanType
           {E} `{Functor E} `{E supports BooleanType}
  : Fix E -> bool
  := fun v =>
       match projectF v with
       | Some MkBooleanType => true
       | _                  => false
       end.

Global Instance TypeEquality__BooleanType
           T `{Functor T} `{T supports BooleanType}
  : ProgramAlgebra ForTypeEquality BooleanType (TypeEqualityResult T)
  :=
    {|
      programAlgebra :=
        fun _ _ '(MkBooleanType) => fun t => isBooleanType t
      ;
    |}.

Global Instance TypeEqualityCorrectness__BooleanType
       {T} `{Functor T}
       `{! T supports BooleanType}
       `{! ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
       `{! WellFormedCompoundProgramAlgebra ForTypeEquality T BooleanType}
  : ProofAlgebra
      ForTypeEqualityCorrectness
      BooleanType
      (sig TypeEqualityCorrectnessStatement).
Proof.
  constructor => [] [].
  exists booleanType.
  rewrite /TypeEqualityCorrectnessStatement.
  move => tau'.
  rewrite /typeEquality /mendlerFold {1} /booleanType.
  rewrite /injectF /wrapF.
  rewrite wellFormedCompoundProgramAlgebra /=.
  rewrite / isBooleanType.
  case P : (projectF tau') => [ [] | ] // => _.
  move : P.
  rewrite / projectF.
  move /project_success.
  move /(f_equal (wrapF (E := T))).
  rewrite /booleanType /injectF.
  rewrite wrapF_unwrapF => //.
Defined.
