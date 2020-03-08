From Coq Require Import
     ssreflect
.

From MTC Require Import
     Algebra
     Boolean
     BooleanType
     Eval
     Functor
     IndexedAlgebra
     IndexedFunctor
     IndexedSubFunctor
     IndexedSum1
     Natural
     NaturalType
     Soundness
     SubFunctor
     Stuck
     Sum1
     TypeEquality
     TypeOf
     WellTypedValue
     WellTypedValueProj1Type
     WellTypedValueProjection
.

(**
We can create languages to instantiate all of our operations.
 *)

(** An extensible type language: *)
Definition TypeLanguage       := (BooleanType + NaturalType)%Sum1.

(** An extensible expression language: *)
Definition ExpressionLanguage := (Boolean + Natural)%Sum1.

(** And an extensible value language: *)
Definition ValueLanguage      := (Boolean + Natural + Stuck)%Sum1.

(** We can instantiate our operations: *)

Definition eval
  : Fix ExpressionLanguage -> EvalResult ValueLanguage
  := MTC.Eval.eval.
  (* ^ we need to fully qualify here because [Eval] is a Coq keyword... *)

Definition typeOf
  : Fix ExpressionLanguage -> TypeOfResult TypeLanguage
  := TypeOf.typeOf.

Definition WellTypedValue
  : (TypedExpr TypeLanguage ValueLanguage)-indexedPropFunctor
  := (WellTypedValue__Boolean + WellTypedValue__Natural)%IndexedSum1.

(**
Remember that [typeOf] returns an extensible type!  So it's not nice looking at,
as it is still a fold:
 *)
Compute typeOf (natural 42).

(**
If you look in there, you should see [inr1 MkNaturalType], which is the correct
answer.  But we can make it look nicer by translating into a concrete type when
we want to inspect results:
 *)

Variant InspectType :=
| InspectBooleanType
| InspectNaturalType
| InspectIllTyped
.

Definition inspectTypeOf
  : Fix ExpressionLanguage -> InspectType
  := fun e =>
       match typeOf e with
       | None   => InspectIllTyped
       | Some tau =>
         (proj1_sig tau)
           InspectType
           (fun _ rec =>
              (
                (fun 'MkBooleanType => InspectBooleanType)
                ||
                (fun 'MkNaturalType => InspectNaturalType)
              )%Sum1
           )
       end.

Compute inspectTypeOf (natural 42).

Variant InspectValue :=
| InspectBoolean  (b : bool)
| InspectNatural  (n : nat)
| InspectStuck    (why : Reason)
| InspectBadValue
.

Definition inspectEval
  : Fix ExpressionLanguage -> InspectValue
  := fun e =>
       (proj1_sig (eval e))
         InspectValue
         (fun _ rec =>
            (
              (fun e => match e with
                  | MkBoolean b => InspectBoolean b
                  | _           => InspectBadValue
                     end)
              ||
              (fun e => match e with
                  | MkNatural n => InspectNatural n
                  | _           => InspectBadValue
                     end)
              ||
              (fun '(MkStuck why) => InspectStuck why)
            )%Sum1
         ).

Definition someBooleanExpression
  : Fix ExpressionLanguage
  := boolean false.

Definition someNaturalExpression
  : Fix ExpressionLanguage
  := ifThenElse (booleanExpression true)
                (plusExpression (naturalExpression 2) (naturalExpression 3))
                (naturalExpression 4).

Definition someIllTypedExpression
  : Fix ExpressionLanguage
  := ifThenElse (booleanExpression true)
                (plusExpression (naturalExpression 2) (naturalExpression 3))
                (booleanExpression false).

(**
We can now inspect the result of running [typeOf]:
 *)
Compute inspectTypeOf someBooleanExpression.
Compute inspectTypeOf someNaturalExpression.
Compute inspectTypeOf someIllTypedExpression.

(**
We can now inspect the result of running [eval]:
 *)
Compute inspectEval someBooleanExpression.
Compute inspectEval someNaturalExpression.
(* Note that [eval] does not care about well-typedness: *)
Compute inspectEval someIllTypedExpression.

Hint Extern 0
     (WellFormedProofAlgebra _)
=> (constructor; move => [] //)
  : typeclass_instances.

(**
For some reason, the type class mechanism fails at this...  I seem to get all
sorts of trouble because of the [SubFunctorInversion__{Left, Right}] instances
 *)
Local Instance SoundnessAlgebra
  : ProofAlgebra
      ForSoundness
      ExpressionLanguage
      { x : Fix ExpressionLanguage | PropUP' (SoundnessStatement WellTypedValue) x }.
Proof.
apply ProofAlgebra__Sum1; try typeclasses eauto.
simple eapply Soundness__Boolean; try typeclasses eauto.
Defined.

Local Instance WellFormedProofAlgebra__SoundnessAlgebra
  : WellFormedProofAlgebra SoundnessAlgebra.
Proof.
typeclasses eauto.
Defined.

Theorem Soundness
  : forall (tau : Expression TypeLanguage) (e : Expression ExpressionLanguage),
    typeOf (proj1_sig e) = Some tau ->
    IndexedFix WellTypedValue {| type := tau; expr := eval (proj1_sig e); |}.
Proof.
  move => tau e.
  eapply Soundness.
  - typeclasses eauto.
  - exact (proj2_sig e).
Qed.
