From MTC Require Import
     IndexedFunctor
     IndexedSubFunctor
     IndexedSum1
.

Local Open Scope IndexedSubFunctor.

Definition IndexedAlgebra
           {I} (F : I-indexedPropFunctor) (A : I-indexedProp)
  : Prop
  := forall i, F A i -> A i.

Definition IndexedMendlerAlgebra
           {I} (F : I-indexedPropFunctor) (A : I-indexedProp)
  : Prop
  := forall i (R : I -> Prop), (forall i, R i -> A i) -> F R i -> A i.

Definition IndexedFix
           {I} (F : I-indexedPropFunctor) i
  : Prop
  := forall (A : I-indexedProp), IndexedMendlerAlgebra F A -> A i.

Definition indexedMendlerFold
           {I} {F : I-indexedPropFunctor} {A : I -> Prop}
           (f : IndexedMendlerAlgebra F A) i
  : IndexedFix F i -> A i
  := fun e => e A f.

Definition indexedWrapF
           {I} {F : I-indexedPropFunctor}
           i (unwrapped : F (IndexedFix F) i)
  : IndexedFix F i
  := fun A f
     => f i (IndexedFix F) (indexedMendlerFold f) unwrapped.

Definition indexedFold
           {I} {F : I-indexedPropFunctor} {A : I-indexedProp}
           `{IndexedFunctor I F}
           (f : IndexedAlgebra F A) i (e : IndexedFix F i)
  : A i
  := indexedMendlerFold (fun i' r rec fa => f i' (indexedFmap i' rec fa)) i e.

Definition indexedUnwrapF
           {I} {F : I-indexedPropFunctor} `{IndexedFunctor I F}
  : forall (i : I), IndexedFix F i -> F (IndexedFix F) i
  := indexedFold (fun i => indexedFmap i indexedWrapF).

(**
NOTE: [F] is explicit because you'll need to specify it when backwards-proving
to avoid the type class mechanism from picking [E] for it, since the conlusion
does not mention [F].
 *)
Definition indexedInjectF
           {I} {E : I-indexedPropFunctor}
           (F : I-indexedPropFunctor)
           `{IndexedFunctor I E} `{IndexedFunctor I F}
           `{(E supports F)%IndexedSubFunctor} {i}
           (fexp : F (IndexedFix E) i)
  : IndexedFix E i
  := indexedWrapF i (indexedInject fexp).

Class IndexedProofAlgebra
      (Tag : Set) {I} (F : I-indexedPropFunctor) A :=
  {
    indexedProofAlgebra : IndexedAlgebra F A;
  }.

Global Instance
       IndexedProofAlgebra__Sum1
       {Tag I} F G {A : I-indexedProp}
       `{! IndexedProofAlgebra Tag F A}
       `{! IndexedProofAlgebra Tag G A}
  : IndexedProofAlgebra Tag (F + G)%IndexedSum1 A
  :=
    {|
      indexedProofAlgebra :=
        fun i fg =>
          match fg with
          | iinl1 f => indexedProofAlgebra i f
          | iinr1 g => indexedProofAlgebra i g
          end
      ;
    |}.
