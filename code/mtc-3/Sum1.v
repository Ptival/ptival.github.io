From Coq Require Import
     ssreflect
.

From MTC Require Import
     Functor
     SubFunctor
.

Local Open Scope SubFunctor.

Declare Scope Sum1.
Delimit Scope Sum1 with Sum1.
Local Open Scope Sum1.

Variant Sum1 (F G : Set -> Set) (A : Set) : Set :=
| inl1 : F A -> (F + G)%Sum1 A
| inr1 : G A -> (F + G)%Sum1 A
where
"F + G" := (Sum1 F G) : Sum1.
Arguments inl1 {F G A}.
Arguments inr1 {F G A}.

Global Instance Functor__Sum1
       {F G} `{Functor F} `{Functor G}
  : Functor (F + G)
  :=
    {|
      fmap :=
        fun A B f fga =>
          match fga with
          | inl1 fa => inl1 (fmap f fa)
          | inr1 ga => inr1 (fmap f ga)
          end;
    |}.

Global Instance SubFunctor__Left
       F G H
       `{Functor F} `{Functor G} `{Functor H}
       `{G supports F}
  : (G + H) supports F.
Proof.
  refine
    {|
      inject  := fun _ fa => inl1 (inject fa);
      project :=
        fun _ gh =>
          match gh with
          | inl1 g => project g
          | inr1 h => None
          end
      ;
    |}.
  {
    move => A fa.
    rewrite project_inject => //.
  }
  {
    move => ? [].
    {
      move => f fa EQ.
      rewrite (project_success EQ) => //.
    }
    {
      move => //.
    }
  }
Defined.

Global Instance SubFunctor__Right
       F G H
       `{Functor F} `{Functor G} `{Functor H}
       `{H supports F}
  : (G + H) supports F.
Proof.
  refine
    {|
      inject  := fun _ fa => inr1 (inject fa);
      project :=
        fun _ gh =>
          match gh with
          | inl1 g => None
          | inr1 h => project h
          end
      ;
    |}.
  {
    move => A fa.
    rewrite project_inject => //.
  }
  {
    move => ? [].
    {
      move => //.
    }
    {
      move => g fa EQ.
      rewrite (project_success EQ) => //.
    }
  }
Defined.

Definition sum1Dispatch
           {A} {L R : Set -> Set} {O}
           (fl : L A -> O) (fr : R A -> O) (v : (L + R)%Sum1 A)
  : O
  :=
    match v with
    | inl1 l => fl l
    | inr1 r => fr r
    end.

Notation "f || g" := (sum1Dispatch f g) : Sum1.
