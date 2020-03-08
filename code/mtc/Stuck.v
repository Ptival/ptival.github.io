From Coq Require Import
     ssreflect
.

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
  : Functor Stuck.
Proof.
  refine {| fmap := fun _ _ f '(MkStuck why) => MkStuck why |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section Stuck.

  Context
    {E}
    `{Functor E}
    `{E supports Stuck}
  .

  Definition stuckExpression
             (why : Reason)
    : Expression E
    := injectUP' (MkStuck why).

  Definition stuck
             (why : Reason)
    : Fix E
    := proj1_sig (stuckExpression why).

  Global Instance UP'__stuck
         (why : Reason)
    : UP' (stuck why)
    := proj2_sig (stuckExpression why).

End Stuck.
