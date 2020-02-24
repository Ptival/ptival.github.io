From MTC Require Import
     Algebra
     Functor
     SubFunctor
.

Local Open Scope SubFunctor.

(**
Ideally, we'd also make this an extensible data type, or maybe use [string], but
for simplicity here, let's set things in stone.
 *)
Variant Reason :=
| IfConditionNotBoolean
| LeftAddendNotNatural
| RightAddendNotNatural
| NeitherAddendNatural
.

Inductive Stuck (E : Set) : Set :=
| MkStuck (why : Reason)
.
Arguments MkStuck {E}.

Global Instance Functor__Stuck
  : Functor Stuck
  := {| fmap := fun _ _ f '(MkStuck why) => MkStuck why |}.

Definition stuck
           {E} `{Functor E} `{E supports Stuck}
           (why : Reason)
  : Fix E
  := injectF (MkStuck why).
