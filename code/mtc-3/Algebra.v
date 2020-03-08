From Coq Require Import
     FunctionalExtensionality
     Setoid
     ssreflect
.

From MTC Require Import
     Functor
     SubFunctor
     Sum1
.

Local Open Scope SubFunctor.
Local Open Scope Sum1.

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
       {A : Set}
       `{ProgramAlgebra Tag F A}
       `{ProgramAlgebra Tag G A}
  : ProgramAlgebra Tag (F + G) A
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

Definition MendlerUP
      {F A}
      (alg : MendlerAlgebra F A) (h : Fix F -> A)
  : h = mendlerFold alg ->
    forall e,
      h (wrapF e) = alg (Fix F) h e.
Proof.
  move => -> //.
Qed.

Class MendlerUP'
      {F}
      (e : Fix F)
  :=
    {
      mendlerUP' :
        forall A (f : MendlerAlgebra F A) (h : Fix F -> A),
          (forall e', h (wrapF e') = f _ h e') ->
          h e = mendlerFold f e;
    }.

Lemma UP
      F `{Functor F}
      A (alg : Algebra F A) (h : Fix F -> A)
  : h = fold alg ->
    forall e,
      h (wrapF e) = alg (fmap h e).
Proof.
  move => -> //.
Qed.

Class UP'
      {F} `{Functor F} (e : Fix F)
  :=
    {
      foldUP' :
        forall A (alg : Algebra F A) (h : Fix F -> A),
          (forall e, h (wrapF e) = alg (fmap h e)) ->
          h e = fold alg e;
    }.

Definition Expression
           V `{Functor V}
  := { e : Fix V | UP' e }.

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

Definition wrapUP'
           {F} `{Functor F}
           (v : F (Expression F))
  : Expression F.
  apply (exist _ (wrapF (fmap (F := F) (@proj1_sig _ _) v))).
  constructor => A alg rec EQ.
  rewrite EQ.
  rewrite /fold /mendlerFold /wrapF.
  rewrite !fmapFusion.
  f_equal.
  f_equal.
  rewrite /compose.
  apply functional_extensionality.
  move => [e' E'] /=.
  apply foldUP' => //.
Defined.

Definition injectUP'
           {E F}
           `{Functor E} `{Functor F}
           `{SubFunctor F E}
           (fexp : F (Expression E))
  : Expression E
  := wrapUP' (inject fexp).

Definition injectF
           {E F}
           `{Functor E} `{Functor F}
           `{E supports F}
           (f : F (Expression E))
  : Fix E
  := proj1_sig (injectUP' f).

Lemma fmap_wrapF
      {E} `{Functor E}
  :
    (fun (R : Set) (rec : R -> E (Fix E)) (e : E R) =>
       fmap wrapF (fmap rec e))
    =
    (fun (R : Set) (rec : R -> E (Fix E)) (e : E R) =>
       fmap (fun r => wrapF (rec r)) e).
Proof.
  eapply functional_extensionality_dep => R.
  eapply functional_extensionality_dep => rec.
  eapply functional_extensionality_dep => e.
  rewrite fmapFusion //.
Qed.

Lemma unwrapF_wrapF
   {E} `{Functor E}
  : forall (e : E (Fix E)),
    unwrapF (wrapF e) = fmap (fun e => wrapF (unwrapF e)) e.
Proof.
  move => e.
  rewrite /unwrapF /=.
  erewrite (MendlerUP (fun R rec fp => fmap (fun r => wrapF (rec r)) fp)) => //.
  rewrite / fold / mendlerFold.
  eapply functional_extensionality.
  move => e'.
  rewrite fmap_wrapF //.
Qed.

Lemma fold_wrapF
      {F} `{Functor F}
      (e : Fix F)
      {UP'__e : UP' e}
  : fold wrapF e = e.
Proof.
  apply : sym_eq.
  apply : foldUP' => e'.
  rewrite fmapId //.
Qed.

Lemma wrapF_unwrapF
      {E} `{Functor E}
  : forall (e : Fix E),
    UP' e ->
    wrapF (unwrapF e) = e.
Proof.
  move => e UP'__e.
  rewrite <- fold_wrapF => //.
  apply (foldUP' _ _ (fun e => wrapF (unwrapF e))).
  move => e'.
  rewrite unwrapF_wrapF //.
Qed.

Definition unwrapUP'
           {F} `{Functor F}
           (v : Fix F)
  : F (Expression F)
  := fold (fmap wrapUP') v.

Lemma unwrapUP'_wrapF
      {E} `{Functor E}
  : forall (e : E (Fix E)),
    unwrapUP' (wrapF e)
    =
    fmap (fun e => wrapUP' (unwrapUP' e)) e.
Proof.
  move => e.
  rewrite {1}/unwrapUP'.
  setoid_rewrite UP => //.
  rewrite fmapFusion //.
Qed.

Lemma fmap_unwrapUP'
      {E} `{Functor E}
  : forall (e : Fix E),
    UP' e ->
    fmap (@proj1_sig _ _) (unwrapUP' e) = unwrapF e.
Proof.
  move => e UP__e.
  rewrite /unwrapF.
  apply (foldUP' _ _ (fun e => fmap (@proj1_sig _ _) (unwrapUP' e))).
  move => e'.
  rewrite fmapFusion /compose.
  rewrite unwrapUP'_wrapF.
  rewrite fmapFusion //.
Qed.

Theorem wrapUP'_unwrapUP'
        {E} `{Functor E}
  : forall (e : Fix E),
    UP' e ->
    proj1_sig (wrapUP' (unwrapUP' e)) = e.
Proof.
  move => e UP__e /=.
  rewrite fmap_unwrapUP'.
  rewrite wrapF_unwrapF //.
Qed.

Lemma wrapF_fold_fmap_wrapF
   {E} `{Functor E}
  : (fun e : sig UP' =>
         wrapF (fold (fmap wrapF) (proj1_sig e))) =
    @proj1_sig _ _.
Proof.
  apply : functional_extensionality.
  move => x.
  setoid_rewrite wrapF_unwrapF => //.
  move : x => [] //.
Qed.

Lemma unwrapF_wrapF_fmap
   {E} `{Functor E}
  : forall (e : E (sig (UP' (F := E)))),
    unwrapF (wrapF (fmap (@proj1_sig _ _) e)) = fmap (@proj1_sig _ _) e.
Proof.
  move => e.
  rewrite / unwrapF.
  erewrite UP => //.
  rewrite fmapFusion.
  rewrite fmapFusion.
  setoid_rewrite wrapF_fold_fmap_wrapF => //.
Qed.

Lemma wrapF_inversion
      {E} `{Functor E}
  : forall (e e' : E (sig UP')),
      wrapF (fmap (@proj1_sig _ _) e) = wrapF (fmap (@proj1_sig _ _) e') ->
      fmap (@proj1_sig _ _) e = fmap (@proj1_sig _ _) e'.
Proof.
  move => e e' / (f_equal unwrapF).
  rewrite !unwrapF_wrapF_fmap.
  rewrite //.
Qed.

(**
NOTE: We have to specify [E := E] here, otherwise [inject] will pick
[SubFunctor__Refl] and not actually inject in [E], turning the statement into a
reflexive tautology.
 *)
Class WellFormedCompoundProgramAlgebra
      {Tag E F A}
      `{Functor E} `{Functor F}
      `{E supports F}
      `(ProgramAlgebra Tag E A)
      `(ProgramAlgebra Tag F A)
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
       `{Alg__F : ProgramAlgebra Tag F A}
  : WellFormedCompoundProgramAlgebra Alg__F Alg__F.
Proof.
  constructor.
  move => rec fa.
  rewrite /inject /SubFunctor__Refl => //.
Qed.

Global Instance
       WellFormedCompoundProgramAlgebra__Left
       {Tag F G H A}
       `{Functor F} `{Functor G} `{Functor H}
       `{Alg__F : ! ProgramAlgebra Tag F A}
       `{Alg__G : ! ProgramAlgebra Tag G A}
       `{Alg__H : ! ProgramAlgebra Tag H A}
       `{! G supports F}
       `{! WellFormedCompoundProgramAlgebra Alg__G Alg__F}
  : WellFormedCompoundProgramAlgebra (ProgramAlgebra__Sum1 Tag G H) Alg__F.
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
       `{Alg__F : ! ProgramAlgebra Tag F A}
       `{Alg__G : ! ProgramAlgebra Tag G A}
       `{Alg__H : ! ProgramAlgebra Tag H A}
       `{! H supports F}
       `{! WellFormedCompoundProgramAlgebra Alg__H Alg__F}
  : WellFormedCompoundProgramAlgebra (ProgramAlgebra__Sum1 Tag G H) Alg__F.
Proof.
  constructor.
  move => rec f.
  rewrite /inject /SubFunctor__Right => fa /=.
  rewrite wellFormedCompoundProgramAlgebra //.
Qed.

Definition projectUP'
           {E F}
           `{Functor E} `{Functor F}
           `{E supports F}
           (e : Fix E)
  : option (F (Expression E))
  := project (unwrapUP' e).

Theorem projectSuccessUP'
        {E F}
        `{Functor E} `{Functor F}
        `{E supports F}
        {e : Fix E}
        {f : F { e : Fix E | UP' e }}
  : UP' e ->
    projectUP' e = Some f ->
    e = injectF f.
Proof.
  move => UP'__g /projectSuccess.
  rewrite /injectF /injectUP' => <- .
  rewrite wrapUP'_unwrapUP' //.
Qed.

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
  : ProofAlgebra Tag (F + G) A
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

Lemma Fusion'
      {F} `{Functor F}
      (e : Fix F) {UP'__e : UP' e}
      (A B : Set) (h : A -> B) (f : Algebra F A) (g : Algebra F B)
      (HF : forall a, h (f a) = g (fmap h a))
      : (fun e' => h (fold f e')) e = fold g e.
Proof.
  apply foldUP' => e'.
  rewrite (UP F _ f) => //.
  rewrite HF.
  rewrite fmapFusion.
  rewrite /compose //.
Qed.

Class WellFormedProofAlgebra
      {Tag E F} {P : Fix E -> Prop}
      `{Functor E} `{Functor F}
      `{E supports F}
      `(PA : ! ProofAlgebra Tag F (sig P))
  :=
    {
      wellFormedProofAlgebra
      : forall e,
        (* run [proofAlgebra], then observe the term *)
        proj1_sig (proofAlgebra e)
        =
        (* observe all subterms via [fmap], and combine them *)
        wrapF (inject (E := E) (fmap (proj1_sig (P := P)) e));
    }.

Hint Extern 0
     (WellFormedProofAlgebra _)
=> (constructor; move => [] //)
  : typeclass_instances.

Local Instance SubFunctorInversion__Left
       {E F G}
       `{Functor E} `{Functor F} `{Functor G}
       `{! E supports (F + G)}
  : E supports F.
Proof.
  refine
    {|
      inject := fun A fa => inject (inl1 fa);
      project :=
        fun A ea =>
          match project ea with
          | Some (inl1 fa) => Some fa
          | _ => None
          end
      ;
    |}.
  {
    move => *; rewrite project_inject //.
  }
  {
    move => A ea fa.
    case P : (project ea) => [ [] | ] //.
    move => [] <- .
    rewrite (projectSuccess P) //.
  }
  {
    move => A B f fa.
    rewrite wellFormedSubFunctor //.
  }
Defined.

Local Instance SubFunctorInversion__Right
       {E F G}
       `{Functor E} `{Functor F} `{Functor G}
       `{! E supports (F + G)}
  : E supports G.
Proof.
  refine
    {|
      inject := fun A ga => inject (F := F + G) (inr1 ga);
      project :=
        fun A ea =>
          match project (F := F + G) ea with
          | Some (inr1 ga) => Some ga
          | _ => None
          end
      ;
    |}.
  {
    move => *; rewrite project_inject //.
  }
  {
    move => A ea ga.
    case P : (project ea) => [ [] | ] //.
    move => [] <- .
    rewrite (projectSuccess P) //.
  }
  {
    move => A B f ga.
    rewrite wellFormedSubFunctor //.
  }
Defined.

Global Instance WellFormedProofAlgebra__Sum1
      {Tag E F G} {P : Fix E -> Prop}
      `{Functor E} `{Functor F} `{Functor G}
      `{EFG : E supports (F + G)%Sum1}
      `(Alg__F : ! ProofAlgebra Tag F (sig P))
      `{! WellFormedProofAlgebra
          (E := E)
          (H1 := SubFunctorInversion__Left)
          Alg__F}
      `(Alg__G : ! ProofAlgebra Tag G (sig P))
      `{! WellFormedProofAlgebra
          (E := E)
          (H1 := SubFunctorInversion__Right (H2 := EFG))
          Alg__G}
  : WellFormedProofAlgebra (E := E) (ProofAlgebra__Sum1 F G).
Proof.
  constructor.
  move => [].
  {
    move => f.
    rewrite (
        wellFormedProofAlgebra
          (H1 := SubFunctorInversion__Left (H2 := EFG))
      ) //.
  }
  {
    move => g.
    rewrite (
        wellFormedProofAlgebra
          (H1 := SubFunctorInversion__Right (H2 := EFG))
      ) //.
  }
Defined.

Lemma proj1_fold
      {Tag F} `{Functor F}
      {P : Fix F -> Prop}
      {PA : ProofAlgebra Tag F (sig P)}
      `{! WellFormedProofAlgebra PA}
  : forall (f : Fix F),
    UP' f ->
    proj1_sig (fold proofAlgebra f) = f.
Proof.
  move => f UP.
  setoid_rewrite Fusion' with (g := wrapF) => //.
  {
    rewrite fold_wrapF //.
  }
  {
    move => a.
    rewrite wellFormedProofAlgebra //.
  }
Qed.

Lemma Induction
      {Tag F} {P : Fix F -> Prop}
      `{Functor F}
      `{PA : ! ProofAlgebra Tag F (sig P)}
      `{! WellFormedProofAlgebra PA}
  : forall (f : Fix F),
    UP' f -> (* FIXME: try to use [Expression F] isntead *)
    P f.
Proof.
  move => f UP.
  setoid_rewrite <- proj1_fold => //.
  apply proj2_sig.
Qed.

(**
NOTE: [P] can not be over [Expression F] as this would prevent moving the
property across different [UP'] proofs.
 *)
Definition PropUP'
           {E} `{Functor E}
           (P : forall (e : Fix E), UP' e -> Prop)
           (e : Fix E)
  : Prop
  := sig (P e).
