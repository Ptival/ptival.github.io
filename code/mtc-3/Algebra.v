From Coq Require Import
     ssreflect
.

From MTC Require Import
     Functor
     SubFunctor
     Sum1
.

Local Open Scope SubFunctor.

(** A regular [Algebra]. *)
Definition Algebra (F : Set -> Set) (A : Set) : Set :=
  F A -> A.

(**
[MendlerAlgebra]s give us control over when recursion happens.
 *)
Definition MendlerAlgebra (F : Set -> Set) (A : Set) : Set :=
  forall (R : Set), (R -> A) -> F R -> A.

(**
[Fix] turns a functor [F] into its fixed point [Set], being the set of all folds
of its [MendlerAlgebra]s.
 *)
Definition Fix (F : Set -> Set) : Set :=
  forall (A : Set), MendlerAlgebra F A -> A.

(**
[ProgramAlgebra] is simply a type class wrapper around [MendlerAlgebra]s, with
an extra [Tag] so as to help type class resolution pick the correct instances.
 *)
Class ProgramAlgebra (Tag : Set) F A :=
  {
    programAlgebra : MendlerAlgebra F A;
  }.

Global Instance ProgramAlgebra__Sum1
       (Tag : Set) (F G : Set -> Set)
       (A : Set)
       `{ProgramAlgebra Tag F A}
       `{ProgramAlgebra Tag G A}
  : ProgramAlgebra Tag (F + G)%Sum1 A
  :=
    {|
      programAlgebra :=
        fun _ rec s =>
          match s with
          | inl1 l => programAlgebra _ rec l
          | inr1 r => programAlgebra _ rec r
          end
    |}.

(**
A [MendlerAlgebra] can be used to fold a [Fix E] simply by applying the algebra.
 *)
Definition mendlerFold
           {E A} (alg : MendlerAlgebra E A)
  : Fix E -> A
  := fun e => e A alg.

(**
A simple [Algebra] can also be used to fold a [Fix E].
 *)
Definition fold
           {E A} `{Functor E} (alg : Algebra E A)
  : Fix E -> A
  := mendlerFold (fun r rec fa => alg (fmap rec fa)).

(**
[wrapF] lets us wrap an unwrapped [E (Fix E)] into a [Fix E].  Eventually, we'll
want a more general wrapping from an [F (Fix E)] into a [Fix E], which will be
possible when [E supports F].
 *)
Definition wrapF
           {E} (unwrapped : E (Fix E))
  : Fix E
  := fun A f => f _ (mendlerFold f) unwrapped.

(**
Conversely, [unwrapF] unfolds a [Fix E] into an [E (Fix E)].  Again, we will
eventually want to "cast" down into a feature [F (Fix E)], though this will
not always work: if the wrapped expression was a [G (Fix E)] for [F <> G],
the casting down will fail.
 *)
Definition unwrapF
           {E} `{Functor E}
  : Fix E -> E (Fix E)
  := fold (fmap wrapF).

(**
[projectF] lets us inspect a wrapped expression, and ask the question "is it an
expression of this given feature?".  If it is, it returns [Some f] where [f] has
type [F (Fix E)] for the feature [F] we are interested about.  If it is not, it
returns [None], indicating that the outermost constructor must belong to a
different feature.
 *)
Definition projectF
           {E F}
           `{Functor E} `{Functor F}
           `{E supports F}
           (e : Fix E)
  : option (F (Fix E))
  := project (unwrapF e).

Definition injectF
           {E F}
           `{Functor E} `{Functor F}
           `{E supports F}
           (f : F (Fix E))
  : Fix E
  := wrapF (inject f).

(* Lemma fold_wrapF *)
(*       {F} `{Functor F} *)
(*       (e : Fix F) *)
(*   : fold wrapF e = e. *)
(* Admitted. (* similar lemma to be proven in another blog post *) *)

Lemma unwrapF_wrapF
   {E} `{Functor E}
  : forall (e : E (Fix E)),
    unwrapF (wrapF e) = e.
Admitted. (* similar lemma to be proven in another blog post *)

Lemma wrapF_unwrapF
      {E} `{Functor E}
  : forall (e : Fix E),
    wrapF (unwrapF e) = e.
Admitted. (* similar lemma to be proven in another blog post *)

Lemma wrapF_inversion
      {E} `{Functor E}
  : forall (e e' : E (Fix E)),
      wrapF e = wrapF e' ->
      e = e'.
Proof.
  move => e e' / (f_equal unwrapF).
  rewrite ! unwrapF_wrapF.
  rewrite //.
Qed.

(* Class WellFormedProgramAlgebra *)
(*       {Tag F A} *)
(*       `{Functor F} *)
(*       `(ProgramAlgebra Tag F A) *)
(*   := *)
(*     { *)
(*       wellFormedProgramAlgebra *)
(*       : forall {A B : Set} (f : A -> B) rec (fa : F A), *)
(*         programAlgebra B rec (fmap f fa) = *)
(*         programAlgebra A (fun fa => rec (f fa)) fa *)
(*     }. *)

(** *)
(* NOTE: We have to specify [E := E] here, otherwise [inject] will pick *)
(* [SubFunctor__Refl] and not actually inject in [E], turning the statement into a *)
(* reflexive tautology. *)
(*  *)
Class WellFormedCompoundProgramAlgebra
      Tag E F {A}
      `{Functor E} `{Functor F}
      `{E supports F}
      `{ProgramAlgebra Tag E A}
      `{ProgramAlgebra Tag F A}
  :=
    {
      wellFormedCompoundProgramAlgebra
      : forall T rec fa,
        programAlgebra T rec (inject (E := E) fa)
        =
        programAlgebra T rec fa;
    }.

Global Instance WellFormedCompoundProgramAlgebra__Refl
       {Tag F A}
       `{Functor F}
       `{ProgramAlgebra Tag F A}
  : WellFormedCompoundProgramAlgebra Tag F F.
Proof.
  constructor.
  move => rec fa.
  rewrite /inject /SubFunctor__Refl => //.
Qed.

Global Instance
       WellFormedCompoundProgramAlgebra__Left
       {Tag F G H A}
       `{Functor F} `{Functor G} `{Functor H}
       `{! ProgramAlgebra Tag F A}
       `{! ProgramAlgebra Tag G A}
       `{! ProgramAlgebra Tag H A}
       `{! G supports F}
       `{! WellFormedCompoundProgramAlgebra Tag G F}
  : WellFormedCompoundProgramAlgebra Tag (G + H)%Sum1 F.
Proof.
  constructor.
  move => R rec f.
  rewrite /inject /SubFunctor__Left /=.
  rewrite wellFormedCompoundProgramAlgebra => //.
Qed.

Global Instance
       WellFormedCompoundProgramAlgebra__Right
       {Tag F G H A}
       `{Functor F} `{Functor G} `{Functor H}
       `{! ProgramAlgebra Tag F A}
       `{! ProgramAlgebra Tag G A}
       `{! ProgramAlgebra Tag H A}
       `{! H supports F}
       `{! WellFormedCompoundProgramAlgebra Tag H F}
  : WellFormedCompoundProgramAlgebra Tag (G + H)%Sum1 F.
Proof.
  constructor.
  move => rec f.
  rewrite /inject /SubFunctor__Right => fa /=.
  rewrite wellFormedCompoundProgramAlgebra //.
Qed.

Theorem projectF_injectF
        {E F}
        `{Functor E} `{Functor F}
        `{E supports F}
        {e : Fix E}
        {f : F (Fix E)}
  : projectF e = Some f ->
    e = injectF (E := E) f.
Proof.
Admitted. (* similar lemma to be proven in another blog post *)

Class ProofAlgebra (Tag : Set) F A :=
  {
    proofAlgebra : Algebra F A;
  }.

Global Instance
       ProofAlgebra__Sum1
       {Tag} F G {A}
       `{Functor F} `{Functor G}
       {FAlg : ProofAlgebra Tag F A}
       {GAlg : ProofAlgebra Tag G A}
  : ProofAlgebra Tag (F + G)%Sum1 A
  :=
    {|
      proofAlgebra :=
        fun fg =>
          match fg with
          | inl1 f => proofAlgebra f
          | inr1 g => proofAlgebra g
          end
      ;
    |}.

Lemma Induction
      {Tag F} `{Functor F}
      {P : Fix F -> Prop}
      `{ProofAlgebra Tag F (sig P)}
  : forall (f : Fix F),
    P f.
Admitted. (* similar lemma to be proven in another blog post *)

Lemma discriminate_inject
      {F G H : Set -> Set}
      `{Functor F}
      `{Functor G}
      `{Functor H}
      `{H supports F}
      `{H supports G}
  : forall A (f : F A) (g : G A),
    inject (E := H) f <> inject (E := H) g.
Admitted. (* similar lemma to be proven in another blog post *)
