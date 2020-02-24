From MTC Require Import
     IndexedFunctor
     IndexedSum1
.

Local Open Scope IndexedSum1.

(**
[F] is a SubFunctor of [E] when [E] is "larger" than [F].
 *)
Class IndexedSubFunctor
      {I} (F E : I-indexedPropFunctor)
  : Prop
  :=
    {
      indexedInject  : forall {A i}, F A i -> E A i;
      indexedProject : forall {A i}, E A i -> F A i \/ True;
    }.

Declare Scope IndexedSubFunctor.
Delimit Scope IndexedSubFunctor with IndexedSubFunctor.
Notation "E 'supports' F" := (IndexedSubFunctor F E) (at level 50) : IndexedSubFunctor.
Local Open Scope IndexedSubFunctor.

Global Instance IndexedSubFunctor__Refl
       {I} {F} `{IndexedFunctor I F} : IndexedSubFunctor F F :=
  {|
    indexedInject  := fun _ _ fa => fa;
    indexedProject := fun _ _ fa => or_introl fa;
  |}.

Global Instance IndexedSubFunctor__Left
       {I} {F G H}
       `{IndexedFunctor I F} `{IndexedFunctor I G} `{IndexedFunctor I H}
       `{G supports F}
  : (G + H) supports F :=
  {|
    indexedInject  := fun _ _ fa => iinl1 (indexedInject fa);
    indexedProject := fun _ _ gh =>
                        match gh with
                        | iinl1 g => indexedProject g
                        | iinr1 _ => or_intror Logic.I
                        end;
  |}.

Global Instance IndexedSubFunctor__Right
       {I} {F G H}
       `{IndexedFunctor I F} `{IndexedFunctor I G} `{IndexedFunctor I H}
       `{H supports F}
  : (G + H) supports F :=
  {|
    indexedInject  := fun _ _ fa => iinr1 (indexedInject fa);
    indexedProject := fun _ _ gh =>
                        match gh with
                        | iinl1 _  => or_intror Logic.I
                        | iinr1 ha => indexedProject ha
                        end;
  |}.
