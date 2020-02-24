From Coq Require Import
     ssreflect
.

From MTC Require Import
     Algebra
     Eval
     Functor
     Hacks
     IndexedAlgebra
     IndexedFunctor
     IndexedSubFunctor
     NaturalType
     Soundness
     Stuck
     SubFunctor
     TypeOf
     WellTypedValue
     WellTypedValueProjection
.

Local Open Scope SubFunctor.

Inductive Natural (E : Set) : Set :=
| MkNatural (n : nat)
| Plus (m n : E)
.
Arguments MkNatural {E}.
Arguments Plus      {E}.

Global Instance Functor__Natural
  : Functor Natural
  :=
    {|
      fmap :=
        fun _ _ f v =>
          match v with
          | MkNatural n => MkNatural n
          | Plus a b    => Plus (f a) (f b)
          end
    |}.

Definition natural
           {E} `{Functor E} `{E supports Natural}
           (n : nat)
  : Fix E
  := injectF (MkNatural n).

Definition plus
           {E} `{Functor E} `{E supports Natural}
           (a b : Fix E)
  : Fix E
  := injectF (Plus a b).

Definition isNatural
           {E} `{Functor E} `{E supports Natural}
  : Fix E -> option nat
  := fun v =>
       match projectF v with
       | Some (MkNatural n) => Some n
       | _                  => None
       end.

Global Instance Eval__Natural
       {R} `{Functor R}
       `{R supports Natural}
       `{R supports Stuck}
  : ProgramAlgebra ForEval Natural (EvalResult R)
  :=
    {|
      programAlgebra :=
        fun _ rec n =>
          match n with
          | MkNatural n => natural n
          | Plus a b    =>
            match (isNatural (rec a), isNatural (rec b)) with
            | (Some na, Some nb) => natural (na + nb)
            | (None,    Some _)  => stuck LeftAddendNotNatural
            | (Some _,  None)    => stuck RightAddendNotNatural
            | (None,    None)    => stuck NeitherAddendNatural
            end
          end
    |}.

Global Instance TypeOf__Natural
       {T} `{Functor T} `{T supports NaturalType}
  : ProgramAlgebra ForTypeOf Natural (TypeOfResult T)
  :=
    {|
      programAlgebra :=
        fun _ rec v =>
          match v with
          | MkNatural _ => Some naturalType
          | Plus a b =>
            match (rec a, rec b) with
            | (Some tau__a, Some tau__b) =>
              if (isNaturalType tau__a && isNaturalType tau__b)%bool
              then Some naturalType
              else None
            | _ => None
            end
      end
      ;
    |}.

Inductive WellTypedValue__Natural
          {T E}
          `{Functor T} `{Functor E}
          `{T supports NaturalType}
          `{E supports Natural}
          (WTV : TypedExpr T E -> Prop)
  : TypedExpr T E -> Prop
  :=
  | WellTypedValue__natural : forall tau e b,
      e = natural b ->
      tau = naturalType ->
      WellTypedValue__Natural WTV {| type := tau; expr := e |}
.

Global Instance IndexedFunctor__WellTypedValue__Natural
       {T V}
       `{Functor T} `{Functor V}
       `{T supports NaturalType}
       `{V supports Natural}
  : IndexedFunctor (TypedExpr T V) WellTypedValue__Natural.
Proof.
  constructor.
  move => A B i IH [] t v n -> -> .
  econstructor => //; apply IH => //.
Qed.

(**
This is a nice-to-have inversion principle for [WellTypedValue__Natural].  It
gives us a little bit more control than using the [inversion] tactic.
 *)
Definition WellTypedValueInversionClear__Natural
           {T V}
           `{Functor T} `{Functor V}
           `{T supports NaturalType}
           `{V supports Natural}
           (WellTypedValue__V : (TypedExpr T V)-indexedProp)
           (tv : TypedExpr T V)
           (P : (TypedExpr T V)-indexedPropFunctor)
           (IH : forall tau v b,
               {| type := tau; expr := v |} = tv ->
               v = natural b ->
               tau = naturalType ->
               P WellTypedValue__V {| type := tau; expr := v |})
           (WT : WellTypedValue__Natural WellTypedValue__V tv)
  : P WellTypedValue__V tv
  :=
    match WT in (WellTypedValue__Natural _ p) return (p = tv -> P WellTypedValue__V tv) with
    | WellTypedValue__natural _ tau e b P__e P__tau =>
      fun EQ => eq_ind _ (fun p => P WellTypedValue__V p) (IH _ _ _ EQ P__e P__tau) tv EQ
    end eq_refl.

Global Instance WellTypedValueProjection__Natural
       {T V}
       `{Functor T} `{Functor V}
       `{T supports NaturalType}
       `{V supports Natural}
       (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
       `{(WellTypedValue__V supports WellTypedValue__Natural)%IndexedSubFunctor}
  : IndexedProofAlgebra
      ForWellTypedValueProjection
      WellTypedValue__Natural
      (WellTypedValueProjectionStatement
         WellTypedValue__Natural
         naturalType
         WellTypedValue__V
      ).
Proof.
  constructor.
  move => tv [] t v n ? ?.
  apply : (WellTypedValue__natural _ _ _ n) => //.
Qed.

Lemma Soundness__natural
      {T E V}
      `{Functor T} `{Functor E} `{Functor V}
      `{T supports NaturalType}
      `{E supports Natural}
      `{V supports Natural}
      `{V supports Stuck}

      (WTV : (TypedExpr T V)-indexedPropFunctor)
      `((WTV supports WellTypedValue__Natural)%IndexedSubFunctor)

      `{Eval__E         : ProgramAlgebra ForEval         E (EvalResult   V)}
      `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult T)}

      `{! WellFormedCompoundProgramAlgebra ForEval   E Natural}
      `{! WellFormedCompoundProgramAlgebra ForTypeOf E Natural}
  : forall (n : nat),
    forall tau,
      typeOf (natural n) = Some tau ->
      IndexedFix
        WTV
        {|
          type := tau;
          expr := eval (natural n);
        |}.
Proof.
  rewrite /=.
  move => n tau.
  rewrite /typeOf /eval /natural /=.
  rewrite /mendlerFold /injectF /=.
  rewrite /wrapF.
  rewrite wellFormedCompoundProgramAlgebra /=.
  rewrite wellFormedCompoundProgramAlgebra /=.
  move => [] <- .
  apply indexedWrapF.
  apply indexedInject.
  econstructor => //.
Defined.

Lemma Soundness__plus
      {T E V}
      `{Functor T} `{Functor E} `{Functor V}
      `{T supports NaturalType}
      `{E supports Natural}
      `{V supports Natural}
      `{V supports Stuck}
      (WTV : (TypedExpr T V)-indexedPropFunctor)
      `((WTV supports WellTypedValue__Natural)%IndexedSubFunctor)
      `{Eval__E : ProgramAlgebra ForEval E (EvalResult V)}
      `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult T)}
      `{! WellFormedCompoundProgramAlgebra ForEval   E Natural}
      `{! WellFormedCompoundProgramAlgebra ForTypeOf E Natural}

      `{! IndexedFunctor (TypedExpr T V) WTV}

      `{! IndexedProofAlgebra
          ForWellTypedValueProjection
          WTV
          (WellTypedValueProjectionStatement WellTypedValue__Natural
                                             naturalType
                                             WTV)
       }

  : forall (a b : sig (SoundnessStatement WTV)),
    let a := proj1_sig a in
    let b := proj1_sig b in
    forall tau,
      typeOf (plus a b) = Some tau ->
      IndexedFix
        WTV
        {|
          type := tau;
          expr := eval (plus a b);
        |}.
Proof.
  rewrite /=.
  move => [a IH__a] [b IH__b].
  move : IH__a IH__b.
  rewrite {1 2}/SoundnessStatement.
  rewrite /eval /typeOf /plus /mendlerFold /injectF /wrapF.
  move => IH__a IH__b.
  rewrite wellFormedCompoundProgramAlgebra => /=.
  rewrite wellFormedCompoundProgramAlgebra => /=.
  case TO__a : (mendlerFold _ a) => [ tau__a | ] //.
  move : IH__a (IH__a _ TO__a) => _ WT__a.
  case TO__b : (mendlerFold _ b) => [ tau__b | ] //.
  move : IH__b (IH__b _ TO__b) => _ WT__b.
  move => tau.
  rewrite / isNaturalType.
  case p__a : (projectF tau__a) => [ [] | ] //.
  case p__b : (projectF tau__b) => [ [] | ] //.
  move => [] <- .
  have := !! projectF_injectF p__a => {}p__a.
  have := !! projectF_injectF p__b => {}p__b.
  have := !! wellTypedValueProjection WellTypedValue__Natural _ _ _ WT__a p__a.
  elim / @WellTypedValueInversionClear__Natural.
  have := !! wellTypedValueProjection WellTypedValue__Natural _ _ _ WT__b p__b.
  elim / @WellTypedValueInversionClear__Natural.
  rewrite /isNatural /projectF /mendlerFold.
  move => ? ? n__a [] -> -> -> _ .
  move => ? ? n__b [] -> -> -> _ .
  rewrite /natural /injectF.
  rewrite ! unwrapF_wrapF.
  rewrite ! project_inject /=.
  apply indexedWrapF.
  apply indexedInject.
  econstructor => //.
Defined.

Definition Induction__Natural
           {E} `{Functor E} `{E supports Natural}
           (P : Fix E -> Prop)
           (H__natural : forall b, P (natural b))
           (H__plus :
              forall (a b : sig P)
                (IH__a : P (proj1_sig a))
                (IH__b : P (proj1_sig b))
              ,
                P (plus (proj1_sig a) (proj1_sig b)))
  : Algebra Natural (sig P)
  := fun e =>
       match e with
       | MkNatural n => exist _ _ (H__natural n)
       | Plus a b =>
         exist _ _ (H__plus _ _ (proj2_sig a) (proj2_sig b))
       end.

Global Instance Soundness__Natural
      {T E V}
      `{Functor T} `{Functor E} `{Functor V}
      `{T supports NaturalType}
      `{E supports Natural}
      `{V supports Natural}
      `{V supports Stuck}
      (WTV : (TypedExpr T V)-indexedPropFunctor)
      `((WTV supports WellTypedValue__Natural)%IndexedSubFunctor)
      `{Eval__E         : ProgramAlgebra ForEval         E (EvalResult         V)}
      `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult       T)}

      `{! WellFormedCompoundProgramAlgebra ForEval   E Natural}
      `{! WellFormedCompoundProgramAlgebra ForTypeOf E Natural}

      `{! IndexedFunctor (TypedExpr T V) WTV}

      `{! IndexedProofAlgebra
          ForWellTypedValueProjection WTV
          (WellTypedValueProjectionStatement WellTypedValue__Natural
                                             naturalType
                                             WTV)
       }

  : ProofAlgebra ForSoundness
                 Natural
                 (sig (SoundnessStatement (E := E) WTV)).
Proof.

  constructor.
  apply Induction__Natural.

  { (* [natural] case *)
    rewrite /SoundnessStatement.
    eapply Soundness__natural => //.
  }

  { (* [plus] case *)
    rewrite /SoundnessStatement.
    move => a b _ _ /=.
    move => tau TO.
    apply (Soundness__plus WTV _ a b) => //.
  }

Defined.
