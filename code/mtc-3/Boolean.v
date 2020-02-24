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
  : Functor Boolean
  :=
    {|
      fmap :=
        fun _ _ f v =>
          match v with
          | MkBoolean b      => MkBoolean b
          | IfThenElse c t e => IfThenElse (f c) (f t) (f e)
          end
    |}.

Definition boolean
           {E} `{Functor E} `{E supports Boolean}
           (b : bool)
  : Fix E
  := injectF (MkBoolean b).

Definition ifThenElse
           {E} `{Functor E} `{E supports Boolean}
           (c t e : Fix E)
  : Fix E
  := injectF (IfThenElse c t e).

Definition isBoolean
           {E} `{Functor E} `{E supports Boolean}
  : Fix E -> option bool
  := fun v =>
       match projectF v with
       | Some (MkBoolean b) => Some b
       | _                  => None
       end.

Global Instance Eval__Boolean
       V `{Functor V}
       `{V supports Boolean}
       `{V supports Stuck}
  : ProgramAlgebra ForEval Boolean (EvalResult V)
  :=
    {|
      programAlgebra :=
        fun _ rec b =>
          match b with
          | MkBoolean b      => boolean b
          | IfThenElse c t e =>
            match isBoolean (rec c) with
            | Some b => if b then rec t else rec e
            | _      => stuck IfConditionNotBoolean
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
        fun _ rec v =>
          match v with
          | MkBoolean _ => Some booleanType
          | IfThenElse c t e =>
            match rec c with
            | Some tau__c =>
              if isBooleanType tau__c
              then
                match (rec t, rec e) with
                | (Some tau__t, Some tau__e) =>
                  if typeEquality tau__t tau__e
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
          `{T supports BooleanType}
          `{E supports Boolean}
          (WTV : TypedExpr T E -> Prop)
  : TypedExpr T E -> Prop
  :=
  | WellTypedValue__boolean : forall tau e b,
      e = boolean b ->
      tau = booleanType ->
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
  move => A B i IH [] t v b -> -> .
  econstructor => //; apply IH => //.
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
               v = boolean b ->
               tau = booleanType ->
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
  move => tv [] t v b ? ?.
  apply : (WellTypedValue__boolean _ _ _ b) => //.
Qed.

Lemma Soundness__boolean
      {T E V}
      `{Functor T} `{Functor E} `{Functor V}
      `{T supports BooleanType}
      `{E supports Boolean}
      `{V supports Boolean}
      `{V supports Stuck}

      (WTV : (TypedExpr T V)-indexedPropFunctor)
      `((WTV supports WellTypedValue__Boolean)%IndexedSubFunctor)

      `{Eval__E         : ProgramAlgebra ForEval         E (EvalResult   V)}
      `{TypeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
      `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult T)}

      `{! WellFormedCompoundProgramAlgebra ForEval   E Boolean}
      `{! WellFormedCompoundProgramAlgebra ForTypeOf E Boolean}
  : forall (b : bool), SoundnessStatement WTV (boolean b).
Proof.
  rewrite /SoundnessStatement.
  move => b tau.
  rewrite /typeOf /eval /boolean /=.
  rewrite /mendlerFold /injectF /=.
  rewrite /wrapF.
  rewrite wellFormedCompoundProgramAlgebra /=.
  rewrite wellFormedCompoundProgramAlgebra /=.
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
      `((WTV supports WellTypedValue__Boolean)%IndexedSubFunctor)
      `{Eval__E         : ProgramAlgebra ForEval         E (EvalResult V)}
      `{TypeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
      `{TypeOf__E       : ProgramAlgebra ForTypeOf       E (TypeOfResult T)}
      `{! WellFormedCompoundProgramAlgebra ForEval   E Boolean}
      `{! WellFormedCompoundProgramAlgebra ForTypeOf E Boolean}

      `{! IndexedFunctor (TypedExpr T V) WTV}

      `{! IndexedProofAlgebra
          ForWellTypedValueProjection
          WTV
          (WellTypedValueProjectionStatement WellTypedValue__Boolean
                                             booleanType
                                             WTV)
       }

      `{! ProofAlgebra
          ForTypeEqualityCorrectness
          T
          (sig TypeEqualityCorrectnessStatement)
       }

  : forall (c t e : sig (SoundnessStatement WTV)),
    let c := proj1_sig c in
    let t := proj1_sig t in
    let e := proj1_sig e in
    SoundnessStatement WTV (ifThenElse c t e).
Proof.
  rewrite {7}/SoundnessStatement /=.
  move => [c IH__c] [t IH__t] [e IH__e].
  move : IH__c IH__t IH__e.
  rewrite {1 2 3}/SoundnessStatement.
  move => IH__c IH__t IH__e.
  rewrite /eval /typeOf /ifThenElse /mendlerFold /injectF /wrapF.
  rewrite wellFormedCompoundProgramAlgebra => /=.
  rewrite wellFormedCompoundProgramAlgebra => /=.
  rewrite -/eval -/typeOf.
  case TO__c : (typeOf c) => [ tau__c | ] //.
  move : IH__c (IH__c _ TO__c) => _ WT__c.
  case BT : (isBooleanType tau__c) => //.
  case TO__t : (typeOf t) => [ tau__t | ] //.
  move : IH__t (IH__t _ TO__t) => _ WT__t.
  case TO__e : (typeOf e) => [ tau__e | ] //.
  move : IH__e (IH__e _ TO__e) => _ WT__e.
  move => tau.
  case TE : (typeEquality tau__t tau__e) => //.
  move => [] <-.
  move : BT.
  rewrite / isBooleanType.
  case p__c : (projectF tau__c) => [ [] | ] // _.
  have := !! projectF_injectF p__c => {}p__c.
  have := !! wellTypedValueProjection WellTypedValue__Boolean _ _ _ WT__c p__c.
  elim / @WellTypedValueInversionClear__Boolean.
  move => ? ? b [] -> -> -> _ .
  rewrite /isBoolean /projectF /mendlerFold.
  rewrite /boolean /injectF.
  rewrite unwrapF_wrapF.
  rewrite project_inject /=.
  move : b => [] //.
  have := !! typeEqualityCorrectness _ _ TE => -> .
  apply WT__e.
Defined.

Definition Induction__Boolean
           {E} `{Functor E} `{E supports Boolean}
           (P : Fix E -> Prop)
           (H__boolean : forall b, P (boolean b))
           (H__ifThenElse :
              forall (c t e : sig P),
                let c := proj1_sig c in
                let t := proj1_sig t in
                let e := proj1_sig e in
                P (ifThenElse c t e))
  : Algebra Boolean (sig P)
  := fun e =>
       match e with
       | MkBoolean b => exist _ _ (H__boolean b)
       | IfThenElse c t e =>
         exist _ _ (H__ifThenElse c t e)
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

      `{! WellFormedCompoundProgramAlgebra ForEval   E Boolean}
      `{! WellFormedCompoundProgramAlgebra ForTypeOf E Boolean}

      `{! IndexedFunctor (TypedExpr T V) WTV}

      `{! IndexedProofAlgebra
          ForWellTypedValueProjection WTV
          (WellTypedValueProjectionStatement WellTypedValue__Boolean
                                             booleanType
                                             WTV)
       }

      `{! ProofAlgebra
          ForTypeEqualityCorrectness T
          (sig TypeEqualityCorrectnessStatement)
       }

  : ProofAlgebra ForSoundness
                 Boolean
                 (sig (SoundnessStatement (E := E) WTV)).
Proof.
  constructor.
  apply Induction__Boolean.

  { (* [boolean] case *)
    rewrite /SoundnessStatement.
    eapply Soundness__boolean => //.
  }

  { (* [ifThenElse] case *)
    rewrite /SoundnessStatement.
    move => c t e /=.
    move => tau TO.
    apply (Soundness__ifThenElse WTV _ c t e) => //.
  }

Defined.
