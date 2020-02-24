Class Functor (F : Set -> Set) :=
  {
    fmap : forall {A B : Set} (f : A -> B), F A -> F B;
  }.
