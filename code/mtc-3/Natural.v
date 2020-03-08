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
     WellTypedValueProj1Type
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
  : Functor Natural.
Proof.
  refine
    {|
      fmap :=
        fun _ _ f v =>
          match v with
          | MkNatural n => MkNatural n
          | Plus a b    => Plus (f a) (f b)
          end
    |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section Natural.

  Context
    {E}
    `{Functor E}
    `{E supports Natural}
  .

  Definition naturalExpression
             (n : nat)
    : Expression E
    := injectUP' (MkNatural n).

  Definition natural
             (n : nat)
    : Fix E
    := proj1_sig (naturalExpression n).

  Global Instance UP'__natural
         (n : nat)
    : UP' (natural n)
    := proj2_sig (naturalExpression n).

  Definition plusExpression
             (a b : Expression E)
    : Expression E
    := injectUP' (Plus a b).

  Definition plus
             (a b : Expression E)
    : Fix E
    := proj1_sig (plusExpression a b).

  Global Instance UP'__plus
             (a b : Expression E)
    : UP' (plus a b)
    := proj2_sig (plusExpression a b).

  Definition isNatural
    : Fix E -> option nat
    := fun v =>
         match projectUP' v with
         | Some (MkNatural n) => Some n
         | _                  => None
         end.

End Natural.

Global Instance Eval__Natural
       {R}
       `{Functor R}
       `{R supports Natural}
       `{R supports Stuck}
  : ProgramAlgebra ForEval Natural (EvalResult R)
  :=
    {|
      programAlgebra :=
        fun _ rec n =>
          match n with
          | MkNatural n => naturalExpression n
          | Plus a b    =>
            let v__a := proj1_sig (rec a) in
            let v__b := proj1_sig (rec b) in
            match (isNatural v__a, isNatural v__b) with
            | (Some na, Some nb) => naturalExpression (na + nb)
            | (None,    Some _)  => stuckExpression LeftAddendNotNatural
            | (Some _,  None)    => stuckExpression RightAddendNotNatural
            | (None,    None)    => stuckExpression NeitherAddendNatural
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
          | MkNatural _ => Some naturalTypeExpression
          | Plus a b =>
            match (rec a, rec b) with
            | (Some tau__a, Some tau__b) =>
              let tau__a := proj1_sig tau__a in
              let tau__b := proj1_sig tau__b in
              if (isNaturalType tau__a && isNaturalType tau__b)%bool
              then Some naturalTypeExpression
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
      proj1_sig e = natural b ->
      proj1_sig tau = naturalType ->
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
  move => A B i IH [] [t +] [v +] n /= EQ__v EQ__t.
  move : EQ__v -> .
  move : EQ__t -> .
  econstructor => //.
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
               proj1_sig v = natural b ->
               proj1_sig tau = naturalType ->
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
  move => tv [] t v n ? ? ?.
  eapply WellTypedValue__natural; eauto.
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

      `{! WellFormedCompoundProgramAlgebra Eval__E   Eval__Natural}
      `{! WellFormedCompoundProgramAlgebra TypeOf__E TypeOf__Natural}
  : forall (n : nat), SoundnessStatement WTV (natural n) (UP'__natural n).
Proof.
  rewrite /SoundnessStatement.
  move => n tau.
  rewrite /typeOf /eval /natural /=.
  rewrite /mendlerFold.
  rewrite /wrapF /=.
  rewrite wellFormedSubFunctor.
  rewrite ! wellFormedCompoundProgramAlgebra /=.
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
      `{(WTV supports WellTypedValue__Natural)%IndexedSubFunctor}
      `{Eval__E : ProgramAlgebra ForEval E (EvalResult V)}
      `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult T)}
      `{! WellFormedCompoundProgramAlgebra Eval__E Eval__Natural}
      `{! WellFormedCompoundProgramAlgebra TypeOf__E TypeOf__Natural}

      `{! IndexedFunctor (TypedExpr T V) WTV}

      `{! IndexedProofAlgebra
          ForWellTypedValueProjection
          WTV
          (WellTypedValueProjectionStatement WellTypedValue__Natural
                                             naturalType
                                             WTV)
       }

  : forall (a b : sig (PropUP' (SoundnessStatement WTV))),
    let expr__a := exist _ (proj1_sig a) (proj1_sig (proj2_sig a)) in
    let expr__b := exist _ (proj1_sig b) (proj1_sig (proj2_sig b)) in
    SoundnessStatement
      WTV
      (plus expr__a expr__b)
      _.
Proof.
  rewrite /=.
  move => [a [UP'__a IH__a]] [b [UP'__b IH__b]].
  rewrite /proj1_sig /proj2_sig.
  move : IH__a IH__b.
  rewrite {1 2}/SoundnessStatement.
  move => IH__a IH__b.
  rewrite /SoundnessStatement.
  rewrite /eval /typeOf /plus /mendlerFold /plusExpression.
  rewrite /injectUP' /wrapUP' /wrapF /=.
  rewrite wellFormedSubFunctor.
  rewrite ! wellFormedCompoundProgramAlgebra /=.
  rewrite -/eval -/typeOf.
  case TO__a : (typeOf a) => [ [tau__a UP'__tau__a] | ] //.
  move : IH__a (IH__a _ TO__a) => _ WT__a.
  case TO__b : (typeOf b) => [ [tau__b UP'__tau__b] | ] //.
  move : IH__b (IH__b _ TO__b) => _ WT__b.
  rewrite /isNaturalType /=.
  case p__a : (projectUP' tau__a) => [ [] | ] //=.
  case p__b : (projectUP' tau__b) => [ [] | ] //=.
  move => tau [] <- .
  have := !! projectSuccessUP' _ p__a => {}p__a.
  have := !! projectSuccessUP' _ p__b => {}p__b.
  have := !! wellTypedValueProjection WellTypedValue__Natural _ _ _ WT__a p__a.
  elim /@WellTypedValueInversionClear__Natural.
  have := !! wellTypedValueProjection WellTypedValue__Natural _ _ _ WT__b p__b.
  elim /@WellTypedValueInversionClear__Natural.
  move => ? ? n__a [] -> -> -> _ .
  move => ? ? n__b [] -> -> -> _ .
  rewrite /isNatural /projectUP' /natural /naturalExpression /=.
  rewrite !unwrapUP'_wrapF.
  rewrite !wellFormedSubFunctor.
  rewrite !project_inject /=.
  apply indexedWrapF.
  apply indexedInject.
  econstructor => //.
Defined.

Definition Induction__Natural
           {E} `{Functor E} `{E supports Natural}
           (P : forall (e : Fix E), UP' e -> Prop)
           (H__natural : forall b, PropUP' P (natural b))
           (H__plus :
              forall {a b : Fix E}
                (IH__a : PropUP' P a)
                (IH__b : PropUP' P b),
                PropUP' P (plus
                             (exist _ _ (proj1_sig IH__a))
                             (exist _ _ (proj1_sig IH__b))
                          )
           )
  : Algebra Natural (sig (PropUP' P))
  := fun e =>
       match e with
       | MkNatural n => exist _ _ (H__natural n)
       | Plus a b =>
         exist _ _ (H__plus (proj2_sig a) (proj2_sig b))
       end.

Global Instance Soundness__Natural
       {T E V}
       `{Functor T} `{Functor E} `{Functor V}
       `{T supports NaturalType}
       `{E supports Natural}
       `{V supports Natural}
       `{V supports Stuck}

       (WTV : (TypedExpr T V)-indexedPropFunctor)
       `{(WTV supports WellTypedValue__Natural)%IndexedSubFunctor}

       `{Eval__E         : ProgramAlgebra ForEval         E (EvalResult         V)}
       `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult       T)}

       `{! WellFormedCompoundProgramAlgebra Eval__E Eval__Natural}
       `{! WellFormedCompoundProgramAlgebra TypeOf__E TypeOf__Natural}

       `{! IndexedFunctor (TypedExpr T V) WTV}

       `{! IndexedProofAlgebra
           ForWellTypedValueProjection WTV
           (WellTypedValueProjectionStatement WellTypedValue__Natural
                                              naturalType
                                              WTV)
        }

  : ProofAlgebra ForSoundness
                 Natural
                 (sig (PropUP' (SoundnessStatement (E := E) WTV))).
Proof.

  constructor.
  apply Induction__Natural.

  { (* [natural] case *)
    rewrite /SoundnessStatement.
    rewrite /PropUP'.
    move => n.
    constructor.
    {
      apply (proj2_sig (naturalExpression n)).
    }
    {
      eapply Soundness__natural => //.
    }
  }

  { (* [plus] case *)
    rewrite /SoundnessStatement.
    move => a b IH__a IH__b /=.
    rewrite /PropUP'.
    constructor.
    {
      apply (proj2_sig (plusExpression
                          (exist _ _ (proj1_sig IH__a))
                          (exist _ _ (proj1_sig IH__b))
                       )
            ).
    }
    {
      apply : (Soundness__plus
                 WTV
                 (exist _ a IH__a)
                 (exist _ b IH__b)
              ).
    }
  }

Defined.

Global Instance WellTypedValueProj1Type__Natural
       {T V}
       `{Functor T} `{Functor V}
       `{T supports NaturalType}
       `{V supports Natural}
       (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
       `{IndexedFunctor (TypedExpr T V) WellTypedValue__V}
       `{! IndexedSubFunctor WellTypedValue__Natural WellTypedValue__V}
  : IndexedProofAlgebra
      ForWellTypedValueProj1Type
      WellTypedValue__Natural
      (WellTypedValueProj1TypeStatement WellTypedValue__V).
Proof.
  constructor.
  move => tv [] [] ? + ? n ? /= N.
  move : N => -> ??? /= ?.
  apply (indexedInjectF WellTypedValue__Natural).
  eapply WellTypedValue__natural; eauto.
Defined.
