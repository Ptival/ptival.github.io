From Coq Require Import
     ssreflect
.

From MTC Require Import
     Functor
.

(**
[F] is a SubFunctor of [E] when [E] is "larger" than [F].
 *)
Class SubFunctor
      F E
      `{Functor F} `{Functor E}
  :=
    {

      inject  : forall {A : Set}, F A -> E A;

      project : forall {A : Set}, E A -> option (F A);

      project_inject : forall {A} {fa : F A},
          project (inject fa) = Some fa;

      projectSuccess : forall {A} {ea : E A} {fa : F A},
          project ea = Some fa -> ea = inject fa;

      wellFormedSubFunctor :
        forall (A B : Set) (f : A -> B) (fa : F A),
          fmap f (inject fa) = inject (fmap f fa);

    }.
Arguments inject  {F E _ _ _ A}.
Arguments project {F E _ _ _ A}.

Declare Scope SubFunctor.
Delimit Scope SubFunctor with SubFunctor.
Notation "E 'supports' F" := (SubFunctor F E) (at level 50) : SubFunctor.
Local Open Scope SubFunctor.

Global Instance SubFunctor__Refl
       F `{Functor F}
  : F supports F.
Proof.
  refine
    {|
      inject  := fun _ x => x;
      project := fun _ x => Some x;
    |}.
  - move => //.
  - move => ??? [] //.
  - move => //.
Defined.
