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
  : Functor BooleanType.
Proof.
  refine {| fmap := fun A B f 'MkBooleanType => MkBooleanType |}.
  - move => ? [] //.
  - move => ? ? ? ? ? [] //.
Defined.

Definition booleanTypeExpression
           {T}
           `{Functor T}
           `{T supports BooleanType}
  : Expression T
  := injectUP' MkBooleanType.

Definition booleanType
           {T}
           `{Functor T}
           `{T supports BooleanType}
  : Fix T
  := proj1_sig booleanTypeExpression.

Global Instance UP'__booleanType
       {T}
       `{Functor T}
       `{T supports BooleanType}
  : UP' booleanType
  := proj2_sig booleanTypeExpression.

Definition isBooleanType
           {E} `{Functor E} `{E supports BooleanType}
  : Fix E -> bool
  := fun v =>
       match projectUP' v with
       | Some MkBooleanType => true
       | _                  => false
       end.

Global Instance TypeEquality__BooleanType
           {T} `{Functor T} `{T supports BooleanType}
  : ProgramAlgebra ForTypeEquality BooleanType (TypeEqualityResult T)
  :=
    {|
      programAlgebra :=
        fun _ _ '(MkBooleanType) => fun tau' => isBooleanType (proj1_sig tau')
      ;
    |}.

Global Instance TypeEqualityCorrectness__BooleanType
       {T}
       `{Functor T}
       `{! T supports BooleanType}
       `{TypeEquality__T :
           ! ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
       `{! WellFormedCompoundProgramAlgebra TypeEquality__T TypeEquality__BooleanType}
  : ProofAlgebra
      ForTypeEqualityCorrectness
      BooleanType
      (sig (PropUP' TypeEqualityCorrectnessStatement)).
Proof.
  constructor => [] [].
  exists booleanType.
  rewrite /PropUP'.
  econstructor.
  rewrite /TypeEqualityCorrectnessStatement.
  move => tau'.
  rewrite /typeEquality /mendlerFold {1}/booleanType.
  rewrite /injectUP' /=.
  rewrite {1}wellFormedSubFunctor.
  rewrite {1}/wrapF.
  rewrite wellFormedCompoundProgramAlgebra /=.
  rewrite /isBooleanType.
  case P : (projectUP' (proj1_sig tau')) => [ [] | ] // => _.
  move : P.
  rewrite /projectUP'.
  move /projectSuccess.
  rewrite /booleanType /booleanTypeExpression /=.
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

Global Instance WellFormedProofAlgebra__TypeEqualityCorrectness__BooleanType
       {T}
       `{Functor T}
       `{! T supports BooleanType}
       `{TypeEquality__T :
           ! ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
       `{! WellFormedCompoundProgramAlgebra TypeEquality__T TypeEquality__BooleanType}
       : WellFormedProofAlgebra TypeEqualityCorrectness__BooleanType.
Proof.
  constructor => [] [] //=.
  rewrite /booleanType /=.
  rewrite wellFormedSubFunctor //.
Qed.
