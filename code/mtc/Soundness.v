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
     TypeOf
     WellTypedValue
.

Definition SoundnessStatement
           {T E V}
           `{Functor T} `{Functor E} `{Functor V}
           (WTV : (TypedExpr T V)-indexedPropFunctor)
           `{Eval__E   : ProgramAlgebra ForEval   E (EvalResult   V)}
           `{TypeOf__E : ProgramAlgebra ForTypeOf E (TypeOfResult T)}
           (e : Fix E) (UP'__e : UP' e)
  : Prop
  := forall (tau : Expression T),
    typeOf e = Some tau ->
    IndexedFix WTV {| type := tau; expr := eval e; |}.

Variant ForSoundness := .

Theorem Soundness
        {T E V}
        `{Functor T} `{Functor E} `{Functor V}
        (WTV : (TypedExpr T V)-indexedPropFunctor)
        `{Eval__E      : ProgramAlgebra ForEval      E (EvalResult   V)}
        `{TypeOf__E    : ProgramAlgebra ForTypeOf    E (TypeOfResult T)}
        `{Soundness__E : ProofAlgebra   ForSoundness E
                                      (sig (PropUP' (SoundnessStatement WTV)))}
        `{! WellFormedProofAlgebra Soundness__E}
  : forall (e : Fix E) (UP'__e : UP' e) (tau : Expression T),
    typeOf e = Some tau ->
    IndexedFix WTV
               {| type := tau; expr := eval e; |}.
Proof.
  move => e UP'__e tau TO.
  rewrite /eval.
  rewrite /mendlerFold.
  have := !! (Induction e UP'__e).
  move => [? S].
  move : (S tau TO) => //.
Qed.
