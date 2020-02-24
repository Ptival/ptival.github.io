Notation "I '-indexedProp'" := (I -> Prop) (at level 50, only parsing).
Notation "I '-indexedPropFunctor'" := (I-indexedProp -> I-indexedProp) (at level 50).

Class IndexedFunctor I (F : I-indexedPropFunctor) : Prop :=
  {
    indexedFmap : forall {A B : I -> Prop} i, (forall i, A i -> B i) -> F A i -> F B i;
  }.
