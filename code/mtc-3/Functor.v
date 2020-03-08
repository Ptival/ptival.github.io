Definition compose {A B C} (g : B -> C) (f : A -> B) (a : A) :=
  g (f a).

Class Functor (F : Set -> Set) :=
  {

    fmap : forall {A B : Set} (f : A -> B), F A -> F B;

    fmapId :
      forall {A : Set} (e : F A),
        fmap (fun x => x) e = e;

    fmapFusion :
      forall {A B C : Set}
        (f : A -> B)
        (g : B -> C)
        (a : F A),
        fmap g (fmap f a) = fmap (compose g f) a;

  }.
