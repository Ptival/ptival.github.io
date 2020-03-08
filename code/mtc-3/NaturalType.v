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
  : Functor NaturalType.
Proof.
  refine {| fmap := fun A B f 'MkNaturalType => MkNaturalType |}.
  - move => ? [] //.
  - move => ? ? ? ? ? [] //.
Defined.

Definition naturalTypeExpression
           {T}
           `{Functor T}
           `{T supports NaturalType}
  : Expression T
  := injectUP' MkNaturalType.

Definition naturalType
           {T}
           `{Functor T}
           `{T supports NaturalType}
  : Fix T
  := proj1_sig naturalTypeExpression.

Global Instance UP'__naturalType
       {T}
       `{Functor T}
       `{T supports NaturalType}
  : UP' naturalType
  := proj2_sig naturalTypeExpression.

Definition isNaturalType
           {E} `{Functor E} `{E supports NaturalType}
  : Fix E -> bool
  := fun v =>
       match projectUP' v with
       | Some MkNaturalType => true
       | _                  => false
       end.

Global Instance TypeEquality__NaturalType
       {T} `{Functor T} `{T supports NaturalType}
  : ProgramAlgebra ForTypeEquality NaturalType (TypeEqualityResult T)
  :=
    {|
      programAlgebra :=
        fun _ _ '(MkNaturalType) => fun tau' => isNaturalType (proj1_sig tau')
      ;
    |}.

Global Instance TypeEqualityCorrectness__NaturalType
       {T} `{Functor T} `{T supports NaturalType}
       `{TypeEquality__T :
           ! ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
       `{! WellFormedCompoundProgramAlgebra
           TypeEquality__T TypeEquality__NaturalType}
  : ProofAlgebra
      ForTypeEqualityCorrectness
      NaturalType
      (sig (PropUP' TypeEqualityCorrectnessStatement)).
Proof.
  constructor => [] [].
  exists naturalType.
  rewrite /PropUP'.
  econstructor.
  rewrite /TypeEqualityCorrectnessStatement.
  move => tau'.
  rewrite /typeEquality /mendlerFold {1}/naturalType.
  rewrite /injectUP' /=.
  rewrite {1}wellFormedSubFunctor.
  rewrite {1}/wrapF.
  rewrite wellFormedCompoundProgramAlgebra /=.
  rewrite /isNaturalType.
  case P : (projectUP' (proj1_sig tau')) => [ [] | ] // => _.
  move : P.
  rewrite /projectUP'.
  move /projectSuccess.
  rewrite /naturalType /naturalTypeExpression /=.
  rewrite wellFormedSubFunctor /=.
  move => P.
  move : P (f_equal wrapUP' P) => _.
  move => P.
  move : P (f_equal (@proj1_sig _ _) P) => _.
  setoid_rewrite wrapUP'_unwrapUP'.
  {
    move => -> /=.
    rewrite wellFormedSubFunctor //.
  }
  {
    apply proj2_sig.
  }
Defined.

Global Instance WellFormedProofAlgebra__TypeEqualityCorrectness__NaturalType
       {T}
       `{Functor T}
       `{! T supports NaturalType}
       `{TypeEquality__T :
           ! ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
       `{! WellFormedCompoundProgramAlgebra TypeEquality__T TypeEquality__NaturalType}
       : WellFormedProofAlgebra TypeEqualityCorrectness__NaturalType.
Proof.
  constructor => [] [] //=.
  rewrite /naturalType /=.
  rewrite wellFormedSubFunctor //.
Qed.
