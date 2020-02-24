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

Inductive NaturalType (A : Set) : Set :=
| MkNaturalType : NaturalType A
.
Arguments MkNaturalType {A}.

Global Instance Functor_NaturalType
  : Functor NaturalType
  := {| fmap := fun A B f 'MkNaturalType => MkNaturalType |}.

Definition naturalType
           {T} `{Functor T} `{T supports NaturalType}
  : Fix T
  := injectF MkNaturalType.

Definition isNaturalType
           {E} `{Functor E} `{E supports NaturalType}
  : Fix E -> bool
  := fun v =>
       match projectF v with
       | Some MkNaturalType => true
       | _                  => false
       end.

Global Instance typeEquality__NaturalType
       T `{Functor T} `{T supports NaturalType}
  : ProgramAlgebra ForTypeEquality NaturalType (TypeEqualityResult T)
  :=
    {|
      programAlgebra :=
        fun _ _ '(MkNaturalType) => fun t => isNaturalType t
      ;
    |}.

Global Instance TypeEquality__NaturalType
           T `{Functor T} `{T supports NaturalType}
  : ProgramAlgebra ForTypeEquality NaturalType (TypeEqualityResult T)
  :=
    {|
      programAlgebra :=
        fun _ _ '(MkNaturalType) => fun t => isNaturalType t
      ;
    |}.

Global Instance TypeEqualityCorrectness__NaturalType
       {T} `{Functor T} `{T supports NaturalType}
       `{ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
       `{! WellFormedCompoundProgramAlgebra ForTypeEquality T NaturalType}
  : ProofAlgebra
      ForTypeEqualityCorrectness
      NaturalType
      (sig TypeEqualityCorrectnessStatement).
Proof.
  constructor => [] [].
  exists naturalType.
  rewrite /TypeEqualityCorrectnessStatement.
  move => tau'.
  rewrite /typeEquality /mendlerFold {1} /naturalType.
  rewrite /injectF /wrapF.
  rewrite wellFormedCompoundProgramAlgebra /=.
  rewrite / isNaturalType.
  case P : (projectF tau') => [ [] | ] // => _.
  move : P.
  rewrite /projectF.
  move /project_success.
  move /(f_equal (wrapF (E := T))).
  rewrite wrapF_unwrapF => //.
Defined.
