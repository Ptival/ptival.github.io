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
         tau InspectType
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
       eval e
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
  := ifThenElse (boolean true)
                (plus (natural 2) (natural 3))
                (natural 4).

Definition someIllTypedExpression
  : Fix ExpressionLanguage
  := ifThenElse (boolean true)
                (plus (natural 2) (natural 3))
                (boolean false).

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

Theorem Soundness
  : forall (tau : Fix TypeLanguage) (e : Fix ExpressionLanguage),
    typeOf e = Some tau ->
    IndexedFix WellTypedValue {| type := tau; expr := eval e; |}.
Proof.
  move => tau e.
  apply Soundness.
  typeclasses eauto.
Qed.
