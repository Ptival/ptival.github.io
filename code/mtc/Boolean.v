From Coq Require Import
     ssreflect
.

From MTC Require Import
     Algebra
     BooleanType
     Eval
     Functor
     Hacks
     IndexedAlgebra
     IndexedFunctor
     IndexedSubFunctor
     Soundness
     Stuck
     SubFunctor
     TypeEquality
     TypeOf
     WellTypedValue
     WellTypedValueProj1Type
     WellTypedValueProjection
.

Local Open Scope SubFunctor.

Inductive Boolean (E : Set) : Set :=
| MkBoolean (b : bool)
| IfThenElse (condition thenBranch elseBranch : E)
.
Arguments MkBoolean  {E}.
Arguments IfThenElse {E}.

Global Instance Functor__Boolean
  : Functor Boolean.
Proof.
  refine
    {|
      fmap :=
        fun _ _ f v =>
          match v with
          | MkBoolean b      => MkBoolean b
          | IfThenElse c t e => IfThenElse (f c) (f t) (f e)
          end
    |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section Boolean.

  Context
    {E}
    `{Functor E}
    `{E supports Boolean}
  .

  Definition booleanExpression
             (b : bool)
    : Expression E
    := injectUP' (MkBoolean b).

  Definition boolean
             (b : bool)
    : Fix E
    := proj1_sig (booleanExpression b).

  Global Instance UP'__boolean
         (b : bool)
    : UP' (boolean b)
    := proj2_sig (booleanExpression b).

  Definition ifThenElseExpression
             (c t e : Expression E)
    : Expression E
    := injectUP' (IfThenElse c t e).

  Definition ifThenElse
             (c t e : Expression E)
    : Fix E
    := proj1_sig (ifThenElseExpression c t e).

  Global Instance UP'__ifThenElse
         (c t e : Expression E)
    : UP' (ifThenElse c t e)
    := proj2_sig (ifThenElseExpression c t e).

  Definition isBoolean
    : Fix E -> option bool
    := fun v =>
         match projectUP' v with
         | Some (MkBoolean b) => Some b
         | _                  => None
         end.

End Boolean.

Global Instance Eval__Boolean
       {E}
       `{Functor E}
       `{E supports Boolean}
       `{E supports Stuck}
  : ProgramAlgebra ForEval Boolean (EvalResult E)
  :=
    {|
      programAlgebra :=
        fun _ rec b =>
          match b with
          | MkBoolean b      => booleanExpression b
          | IfThenElse c t e =>
            let v__c := proj1_sig (rec c) in
            match isBoolean v__c with
            | Some b => if b then rec t else rec e
            | _      => stuckExpression IfConditionNotBoolean
            end
          end
    |}.

Global Instance TypeOf__Boolean
       {T} `{Functor T} `{T supports BooleanType}
       {TypeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
  : ProgramAlgebra ForTypeOf Boolean (TypeOfResult T)
  :=
    {|
      programAlgebra :=
        fun _ (rec : _ -> option (Expression _)) v =>
          match v with
          | MkBoolean _ => Some booleanTypeExpression
          | IfThenElse c t e =>
            match rec c with
            | Some tau__c =>
              if isBooleanType (proj1_sig tau__c)
              then
                match (rec t, rec e) with
                | (Some tau__t, Some tau__e) =>
                  if typeEquality (proj1_sig tau__t) tau__e
                  then Some tau__t
                  else None
                | _ => None
                end
              else None
            | None => None
            end
          end
      ;
    |}.

Inductive WellTypedValue__Boolean
          {T E}
          `{Functor T} `{Functor E}
          `{! T supports BooleanType}
          `{! E supports Boolean}
          (WTV : TypedExpr T E -> Prop)
  : TypedExpr T E -> Prop
  :=
  | WellTypedValue__boolean : forall tau e b,
      proj1_sig e = boolean b ->
      proj1_sig tau = booleanType ->
      WellTypedValue__Boolean WTV {| type := tau; expr := e |}
.

Global Instance IndexedFunctor__WellTypedValue__Boolean
       {T V}
       `{Functor T} `{Functor V}
       `{T supports BooleanType}
       `{V supports Boolean}
  : IndexedFunctor (TypedExpr T V) WellTypedValue__Boolean.
Proof.
  constructor.
  move => A B i IH [] [tau +] [e +] b /= EQ__e EQ__tau.
  move : EQ__e -> .
  move : EQ__tau -> .
  econstructor => //.
Qed.

(**
This is a nice-to-have inversion principle for [WellTypedValue__Boolean].  It
gives us a little bit more control than using the [inversion] tactic.
 *)
Definition WellTypedValueInversionClear__Boolean
           {T V}
           `{Functor T} `{Functor V}
           `{T supports BooleanType}
           `{V supports Boolean}
           (WellTypedValue__V : (TypedExpr T V)-indexedProp)
           (tv : TypedExpr T V)
           (P : (TypedExpr T V)-indexedPropFunctor)
           (IH : forall tau v b,
               {| type := tau; expr := v |} = tv ->
               proj1_sig v = boolean b ->
               proj1_sig tau = booleanType ->
               P WellTypedValue__V {| type := tau; expr := v |})
           (WT : WellTypedValue__Boolean WellTypedValue__V tv)
  : P WellTypedValue__V tv
  :=
    match WT in (WellTypedValue__Boolean _ p) return (p = tv -> P WellTypedValue__V tv) with
    | WellTypedValue__boolean _ tau e b P__e P__tau =>
      fun EQ => eq_ind _ (fun p => P WellTypedValue__V p) (IH _ _ _ EQ P__e P__tau) tv EQ
    end eq_refl.

Global Instance WellTypedValueProjection__Boolean
       {T V}
       `{Functor T} `{Functor V}
       `{T supports BooleanType}
       `{V supports Boolean}
       (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
       `{(WellTypedValue__V supports WellTypedValue__Boolean)%IndexedSubFunctor}
  : IndexedProofAlgebra
      ForWellTypedValueProjection
      WellTypedValue__Boolean
      (WellTypedValueProjectionStatement
         WellTypedValue__Boolean
         booleanType
         WellTypedValue__V
      ).
Proof.
  constructor.
  move => tv [] t v b B BT +.
  rewrite /type => _.
  eapply WellTypedValue__boolean; eauto.
Qed.

Lemma Soundness__boolean
      {T E V}
      `{Functor T} `{Functor E} `{Functor V}
      `{T supports BooleanType}
      `{E supports Boolean}
      `{V supports Boolean}
      `{V supports Stuck}

      (WTV : (TypedExpr T V)-indexedPropFunctor)
      `{(WTV supports WellTypedValue__Boolean)%IndexedSubFunctor}

      `{Eval__E         : ProgramAlgebra ForEval         E (EvalResult   V)}
      `{TypeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
      `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult T)}

      `{! WellFormedCompoundProgramAlgebra Eval__E   Eval__Boolean}
      `{! WellFormedCompoundProgramAlgebra TypeOf__E TypeOf__Boolean}
  : forall (b : bool), SoundnessStatement WTV (boolean b) (UP'__boolean b).
Proof.
  rewrite /SoundnessStatement.
  move => b tau.
  rewrite /typeOf /eval /boolean /=.
  rewrite /mendlerFold.
  rewrite /wrapF /=.
  rewrite wellFormedSubFunctor.
  rewrite ! wellFormedCompoundProgramAlgebra /=.
  move => [] <- .
  apply indexedWrapF.
  apply indexedInject.
  econstructor => //.
Defined.

Lemma Soundness__ifThenElse
      {T E V}
      `{Functor T} `{Functor E} `{Functor V}
      `{T supports BooleanType}
      `{E supports Boolean}
      `{V supports Boolean}
      `{V supports Stuck}

      (WTV : (TypedExpr T V)-indexedPropFunctor)
      `{(WTV supports WellTypedValue__Boolean)%IndexedSubFunctor}

      `{Eval__E         : ProgramAlgebra ForEval         E (EvalResult V)}
      `{TypeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
      `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult T)}

      `{! WellFormedCompoundProgramAlgebra Eval__E   Eval__Boolean}
      `{! WellFormedCompoundProgramAlgebra TypeOf__E TypeOf__Boolean}

      `{! IndexedFunctor (TypedExpr T V) WTV}

      `{! IndexedProofAlgebra
          ForWellTypedValueProjection
          WTV
          (WellTypedValueProjectionStatement WellTypedValue__Boolean
                                             booleanType
                                             WTV)
       }

      `{! IndexedProofAlgebra
          ForWellTypedValueProj1Type
          WTV
          (WellTypedValueProj1TypeStatement WTV)
       }

      `{TypeEqualityCorrectness__T :
          ! ProofAlgebra
            ForTypeEqualityCorrectness
            T
            (sig (PropUP' TypeEqualityCorrectnessStatement))
       }
      `{! WellFormedProofAlgebra TypeEqualityCorrectness__T}

  : forall (c t e : sig (PropUP' (SoundnessStatement WTV))),
    let expr__c := exist _ (proj1_sig c) (proj1_sig (proj2_sig c)) in
    let expr__t := exist _ (proj1_sig t) (proj1_sig (proj2_sig t)) in
    let expr__e := exist _ (proj1_sig e) (proj1_sig (proj2_sig e)) in
    SoundnessStatement
      WTV
      (ifThenElse expr__c expr__t expr__e)
      _.
Proof.
  rewrite {7}/SoundnessStatement /=.
  move => [c [UP'__c IH__c]] [t [UP'__t IH__t]] [e [UP'__e IH__e]].
  rewrite /proj1_sig /proj2_sig.
  move : IH__c IH__t IH__e.
  rewrite {1 2 3}/SoundnessStatement.
  move => IH__c IH__t IH__e.
  rewrite /SoundnessStatement.
  rewrite /eval /typeOf /ifThenElse /mendlerFold /ifThenElseExpression.
  rewrite /injectUP' /wrapUP' /wrapF /=.
  rewrite wellFormedSubFunctor.
  rewrite ! wellFormedCompoundProgramAlgebra /=.
  rewrite -/eval -/typeOf.
  case TO__c : (typeOf c) => [ tau__c | ] //.
  move : IH__c (IH__c _ TO__c) => _ WT__c.
  case BT : (isBooleanType (proj1_sig tau__c)) => //.
  case TO__t : (typeOf t) => [ [tau__t UP'__tau__t] | ] //.
  move : IH__t (IH__t _ TO__t) => _ WT__t.
  case TO__e : (typeOf e) => [ [tau__e UP'__tau__e] | ] //.
  move : IH__e (IH__e _ TO__e) => _ WT__e.
  move => tau.
  case TE : (typeEquality tau__t (exist _ _ UP'__tau__e)) => //.
  move => [] <-.
  move : BT.
  rewrite /isBooleanType.
  case p__c : (projectUP' (proj1_sig tau__c)) => [ [] | ] // _.
  have := !! projectSuccessUP' (proj2_sig tau__c) p__c => {}p__c.
  have := !! wellTypedValueProjection WellTypedValue__Boolean _ _ _ WT__c p__c.
  elim /@WellTypedValueInversionClear__Boolean.
  move => ? ? b [] -> -> -> _ .
  rewrite /isBoolean /projectUP' /boolean /booleanExpression /=.
  rewrite unwrapUP'_wrapF.
  rewrite !wellFormedSubFunctor.
  rewrite project_inject /=.
  move : b => [] //.
  have := !! typeEqualityCorrectness (exist _ _ UP'__tau__t) _ TE => TEC.
  have := !! wellTypedValueProj1Type _ _ WT__e _ UP'__tau__t TEC => //.
Defined.

Definition Induction__Boolean
           {E} `{Functor E} `{E supports Boolean}
           (P : forall (e : Fix E), UP' e -> Prop)
           (H__boolean : forall b, PropUP' P (boolean b))
           (H__ifThenElse :
              forall {c t e : Fix E}
                (IH__c : PropUP' P c)
                (IH__t : PropUP' P t)
                (IH__e : PropUP' P e),
                PropUP' P (ifThenElse
                             (exist _ _ (proj1_sig IH__c))
                             (exist _ _ (proj1_sig IH__t))
                             (exist _ _ (proj1_sig IH__e))
                          )
           )
  : Algebra Boolean (sig (PropUP' P))
  := fun e =>
       match e with
       | MkBoolean b => exist _ _ (H__boolean b)
       | IfThenElse c t e =>
         exist _ _ (H__ifThenElse (proj2_sig c) (proj2_sig t) (proj2_sig e))
       end.

Global Instance Soundness__Boolean
       {T E V}
       `{Functor T} `{Functor E} `{Functor V}
       `{T supports BooleanType}
       `{E supports Boolean}
       `{V supports Boolean}
       `{V supports Stuck}

       (WTV : (TypedExpr T V)-indexedPropFunctor)
       `((WTV supports WellTypedValue__Boolean)%IndexedSubFunctor)

       `{Eval__E         : ProgramAlgebra ForEval         E (EvalResult         V)}
       `{TypeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
       `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult       T)}

      `{! WellFormedCompoundProgramAlgebra Eval__E   Eval__Boolean}
      `{! WellFormedCompoundProgramAlgebra TypeOf__E TypeOf__Boolean}

       `{! IndexedFunctor (TypedExpr T V) WTV}

       `{! IndexedProofAlgebra
           ForWellTypedValueProjection WTV
           (WellTypedValueProjectionStatement WellTypedValue__Boolean
                                              booleanType
                                              WTV)
        }

      `{! IndexedProofAlgebra
          ForWellTypedValueProj1Type
          WTV
          (WellTypedValueProj1TypeStatement WTV)
       }

      `{TypeEqualityCorrectness__T :
          ! ProofAlgebra
            ForTypeEqualityCorrectness T
            (sig (PropUP' TypeEqualityCorrectnessStatement))
        }
      `{! WellFormedProofAlgebra TypeEqualityCorrectness__T}

  : ProofAlgebra ForSoundness
                 Boolean
                 { e : Fix E | PropUP' (SoundnessStatement WTV) e }.
Proof.
  constructor.
  apply Induction__Boolean.

  { (* [boolean] case *)
    rewrite /SoundnessStatement.
    rewrite /PropUP' /=.
    move => b.
    constructor.
    {
      apply (proj2_sig (booleanExpression b)).
    }
    {
      eapply Soundness__boolean => //.
    }
  }

  { (* [ifThenElse] case *)
    rewrite /SoundnessStatement.
    move => c t e IH__c IH__t IH__e /=.
    rewrite /PropUP' /=.
    constructor.
    {
      apply (proj2_sig (ifThenElseExpression
                          (exist _ _ (proj1_sig IH__c))
                          (exist _ _ (proj1_sig IH__t))
                          (exist _ _ (proj1_sig IH__e))
                       )
            ).
    }
    {
      apply : (Soundness__ifThenElse
                 WTV
                 (exist _ c IH__c)
                 (exist _ t IH__t)
                 (exist _ e IH__e)
              ).
    }
  }

Defined.

Global Instance WellTypedValueProj1Type__Boolean
       {T V}
       `{Functor T} `{Functor V}
       `{T supports BooleanType}
       `{V supports Boolean}
       (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
       `{IndexedFunctor (TypedExpr T V) WellTypedValue__V}
       `{! IndexedSubFunctor WellTypedValue__Boolean WellTypedValue__V}
  : IndexedProofAlgebra
      ForWellTypedValueProj1Type
      WellTypedValue__Boolean
      (WellTypedValueProj1TypeStatement WellTypedValue__V).
Proof.
  constructor.
  move => tv [] [] ? + ? b ? /= B.
  move : B => -> ??? /= ?.
  apply (indexedInjectF WellTypedValue__Boolean).
  eapply WellTypedValue__boolean; eauto.
Defined.
