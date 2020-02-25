---
layout: post
title: "Deep dive into Meta-Theory à la Carte (part 3)"
date: 2020-02-25 12:00:00 +0100
permalink: deep-dive-meta-theory-carte-3
comments: true
categories:
---

NOTE: The code for this post is located
[here](TODO)

In the previous episode...
--------------------------

In the [previous episode](./deep-dive-meta-theory-carte-2), we saw how to define
extensible computations over extensible languages.  Today, we will see how to
define extensible properties of extensible computations over extensible languages!

There will be a lot of code, which I will try to cover in order of its
dependencies, though we might sometimes foray ahead before going back to
definitions, for the sake of our story.

Because we already have a lot to cover, some of the lemmas presented here will
be admitted: proving them will require adding a lot of extra information to our
data types, which will only make the presentation less readable.  In the
interest of keeping this post at a reasonable level of complexity, I am using a
simpler presentation and admitting those lemmas.  A subsequent post will show
how to enhance our data types and demonstrate those lemmas.

Review
------

We will also be making changes to pre-existing code, so let's review where we
are.  This time around, we will use the fact that our extensible language
features are proper `Functor`s, so we introduce a type class for those:

{% highlight coq %}
(* Functor.v *)

Class Functor (F : Set -> Set) :=
  {
    fmap : forall {A B : Set} (f : A -> B), F A -> F B;
  }.
{% endhighlight %}

Features being `Functor`s, a compound language will support a feature whenever
it is a super-functor of that feature.  We define a notion of `SubFunctor` to
capture this sub-typing relation:

{% highlight coq %}
(* SubFunctor.v *)

Class SubFunctor
      F E
      `{Functor F} `{Functor E}
  :=
    {
      inject  : forall {A : Set}, F A -> E A;
      project : forall {A : Set}, E A -> option (F A);
      ...
    }.
{% endhighlight %}

The actual `SubFunctor` class contains three extra properties of `inject`,
`project`, and `fmap`.  I will come back to those as they become relevant to our
proofs.  I will almost always write `G supports F` to indicate that `F` is a
sub-functor of `G` with all those nice properties.

Again, we have a notion of a sum of functors, usually noted `F + G`, with proper
sub-functor instances, such that `F supports F` unconditionally, and `(G + H)
supports F` whenever either `G supports F` or `H supports F`.

As in the previous post, we will reify the concepts of `Algebra` and
`MendlerAlgebra`, and will define a `Fix` type operator for some functor `F`
that stands for the set of all folds of its `MendlerAlgebra`s.

{% highlight coq %}
(* SubFunctor.v *)

Definition Algebra (F : Set -> Set) (A : Set) : Set :=
  F A -> A.

Definition MendlerAlgebra (F : Set -> Set) (A : Set) : Set :=
  forall (R : Set), (R -> A) -> F R -> A.

Definition Fix (F : Set -> Set) : Set :=
  forall (A : Set), MendlerAlgebra F A -> A.
{% endhighlight %}

As in the previous post, it will be useful to have a type class for tagged
Mendler algebras, so as to categorize them by the extensible operation that they
participate in creating.

{% highlight coq %}
(* Algebra.v *)

Class ProgramAlgebra (Tag : Set) F A :=
  {
    programAlgebra : MendlerAlgebra F A;
  }.
{% endhighlight %}

Mendler algebras and F-algebras each give rise to a folding operation, crunching
down a fixed point of their functor (for our purposes, a nested expression) into
a result.

{% highlight coq %}
(* Algebra.v *)

Definition mendlerFold
           {E A} (alg : MendlerAlgebra E A)
  : Fix E -> A
  := fun e => e A alg.

Definition fold
           {E A} `{Functor E} (alg : Algebra E A)
  : Fix E -> A
  := mendlerFold (fun r rec fa => alg (fmap rec fa)).
{% endhighlight %}

We can use those folds to define the usual wrapping and unwrapping operations
that are standard in iso-recursive presentations of recursive types: the
wrapping operator wraps a `E (Fix E)` into a `Fix E`, while the unwrapping
operation does the reverse.

{% highlight coq %}
(* Algebra.v *)

Definition wrapF
           {E} (unwrapped : E (Fix E))
  : Fix E
  := fun A f => f _ (mendlerFold f) unwrapped.

Definition unwrapF
           {E} `{Functor E}
  : Fix E -> E (Fix E)
  := fold (fmap wrapF).
{% endhighlight %}

In general, however, we will want to wrap values of type `F (Fix E)`, for `F`
some feature of `E`.  Think of `E` as the compound language of `Boolean +
Natural`, and `F` being just the `Boolean` language feature.  It is pretty easy
to define such a generalized wrappping function: because `F` is a sub-functor of
`E`, there exists an `inject` function that turns `F A` into `E A`, for any `A`.

{% highlight coq %}
(* Algebra.v *)

Definition injectF
           {E F}
           `{Functor E} `{Functor F}
           `{E supports F}
           (f : F (Fix E))
  : Fix E
  := wrapF (inject f).
{% endhighlight %}

The unwrapping function, on the other hand, is not guaranteed to succeed: if you
wrapped a `Boolean (Fix E)` into a `Fix E`, asking for it to be unwrapped as a
`Natural (Fix E)` should not succeed!  As such, it returns an option type.

{% highlight coq %}
(* Algebra.v *)

Definition projectF
           {E F}
           `{Functor E} `{Functor F}
           `{E supports F}
           (e : Fix E)
  : option (F (Fix E))
  := project (unwrapF e).
{% endhighlight %}

Evaluation algebras
-------------------

Like in the last post, we will define a class of extensible program algebras
that implement an evaluation function for our language features.  So that all
such algebras agree on the type of the operation they implement, we define its
return type in one central location.

{% highlight coq %}
(* Eval.v *)

Definition EvalResult V := Fix V.
{% endhighlight %}

In the previous post, we were targetting a concrete type of results for our
evaluation algebra.  Here, we will rather target an extensible language of
results, since we want to allow adding new language features that may evaluate
to new values.  So we just ask for the compound language of result values `R`,
and return an extensible term for said language.

We also define the tag `ForEval` for this operation (again, to help type class
resolution pick instances based on tags), and we define the overloaded `eval`
operation, to be realized for any language `E` that has a corresponding program
algebra available.

{% highlight coq %}
(* Eval.v *)

Variant ForEval := .

Definition eval
           {E V}
           {eval__E : ProgramAlgebra ForEval E (EvalResult V)}
  : Fix E -> EvalResult V
  := mendlerFold programAlgebra.
{% endhighlight %}

Note that all extensible functions will be defined as `mendlerFold
programAlgebra`, given that the proper program algebra is in scope:
`programAlgebra` is the overloaded type class member that gets resolved
according to the signature of the operation.

Let us now focus on our `Boolean` language feature, and implement a program
algebra for evaluation its boolean expressions.

{% highlight coq %}
Global Instance Eval__Boolean
       V `{Functor V}
  : ProgramAlgebra ForEval Boolean (EvalResult V)
  :=
    {|
      programAlgebra :=
        fun A rec b =>
          match b with
          | MkBoolean b      => (* ... *)
          | IfThenElse c t e => (* ... *)
          end
    |}.
{% endhighlight %}

If the expression is `MkBoolean b`, well, that's a boolean value, so we'd like
to leave it as is.  This will require adding the constraint `V supports
Boolean`, since we must inject the result into this abstract `V`.

{% highlight coq %}
Global Instance Eval__Boolean
       V `{Functor V}
       `{V supports Boolean}
  : ProgramAlgebra ForEval Boolean (EvalResult V)
  :=
    {|
      programAlgebra :=
        fun A rec b =>
          match b with
          | MkBoolean b      => boolean b
          | IfThenElse c t e => (* ... *)
          end
    |}.
{% endhighlight %}

Let's now focus on the `IfThenElse` case:

{% highlight coq %}
          | IfThenElse c t e => (* ... *)
{% endhighlight %}

Evaluating this requires, first, recursively evaluating the condition, then,
branching on it, and either evaluating the `t` branch, or the `e` branch.  But
the result of evaluating the condition, `rec c`, is an extensible result, of
type `Fix V`.  While we demand that `V supports Boolean`, we cannot guarantee
that what we get back is a `Boolean` expression, after all, this language is
currently untyped, and `V` could admit other values!

We will build a convenient "pattern-matching" construct, that will not only
check whether a given extensible term can be successfully projected in the
`Boolean` feature, and if so, check whether it has the `MkBoolean` constructor,
and if this also succeeds, it will extract the `boolean` within.  That's pretty
nifty, and not too hard to write.

{% highlight coq %}
(* Boolean.v *)

Definition matchBoolean
           {E} `{Functor E} `{E supports Boolean}
  : Fix E -> option bool
  := fun v =>
       match projectF v with
       | Some (MkBoolean b) => Some b
       | _                  => None
       end.
{% endhighlight %}

Indeed, `projectF` does half the job, returning an `option (Boolean (Fix E))`.
If it fails, we fail.  If it succeeds, we check whether it is the `MkBoolean`
constructor, otherwise we fail.  If everything succeeds, we successfully return
the extracted `b`.  With this operation, we are one step closer to implementing
our branch.

{% highlight coq %}
          | IfThenElse c t e =>
            match isBoolean (rec c) with
            | Some b => if b then rec t else rec e
            | _      => (* ... *)
            end
{% endhighlight %}

But what to return if the condition was not a boolean (this may happen), or a
boolean yet not a value (this may not happen, but the type-checker can not
realize that)?  We will need some language feature in our result type to hold
failures.  We define such a feature called `Stuck` (see `Stuck.v`), and can
finish our implementation by adding an extra `V supports Stuck` condition.

{% highlight coq %}
(* Boolean.v *)

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
{% endhighlight %}

Pretty cool, no?  The implementation of evaluation for the `Natural` feature is
very similar to this one, so I will not go over it.  Let's move on to the second
piece of our puzzle.

Type inference algebras
-----------------------

Now would be a good time to let you in on the end goal of this post: we will try
and prove type soundness for a compound language.  We will write an extensible
operation `typeOf` that infers a type for an expression, when it admits one.
We will write an extensible relation `WellTypedValue`, that captures only those
expressions we consider values, and relates them to the type we want them to
have.  Given those, we'd like to show that if `typeOf e` succeeds, inferring a
type `tau`, then the result of `eval e` is a value of type `tau`, according to
our extensible relation.

Let us prepare the terrain for our `typeOf` operation.  Again, this means
defining its return type, creating a tag for its `ProgramAlgebra`s, and defining
the overloaded operation.

{% highlight coq %}
(* TypeOf.v *)

Definition TypeOfResult T := option (Fix T).

Variant ForTypeOf := .

Definition typeOf
           {E T}
           {typeOf__E : ProgramAlgebra ForTypeOf E (TypeOfResult T)}
  : Fix E -> TypeOfResult T
  := mendlerFold programAlgebra.
{% endhighlight %}

We will have two new extensible languages, `BooleanType` and `NaturalType`, that
are our two base types, with smart constructors `booleanType` and `naturalType`.
Let's now look at the implementation of `typeOf` for `Boolean`.

{% highlight coq %}
(* Boolean.v *)

Global Instance TypeOf__Boolean
       {T} `{Functor T} `{T supports BooleanType}
  : ProgramAlgebra ForTypeOf Boolean (TypeOfResult T)
  :=
    {|
      programAlgebra :=
        fun _ rec v =>
          match v with
          | MkBoolean _      => Some booleanType
          | IfThenElse c t e => (* ... *)
          end
      ;
    |}.
{% endhighlight %}

For `ifThenElse`, we want to check whether the condition is indeed a `boolean`
condition.  This is done with another "pattern-matching" helper,
`isBooleanType`, though this one does not have anything useful to bind,
therefore it just returns a `bool`.

{% highlight coq %}
          | IfThenElse c t e =>
            match rec c with
            | Some tau__c =>
              if isBooleanType tau__c
              then
                match (rec t, rec e) with
                | (Some tau__t, Some tau__e) => (* ... *)
                | _                          => None
                end
              else None
{% endhighlight %}

Now what to do when we have the type `tau__t` of expression `t`, and the type
`tau__e` of expression `e`?  The branches of boolean expressions must have the
same type for the expression to be well-typed.  We'd like to know whether they
are the same type, but those are extensible types (they have type `TypeResult
T`, which means `Fix T`, for some abstract `T`), so how to compare them?  We
will need a new extensible operation: a check for type equality.

Interlude: algebras for type equality
-------------------------------------

Once more, a return type, a tag, and an overloaded operation.

{% highlight coq %}
(* TypeEquality.v *)

Definition TypeEqualityResult T := Fix T -> bool.

Variant ForTypeEquality := .

Definition typeEquality
           {T}
           {typeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
  : Fix T -> TypeEqualityResult T
  := mendlerFold programAlgebra.
{% endhighlight %}

Of note, because [typeEquality] is a binary operation, we see a curried return
type, `Fix T -> bool`, expecting the second type to compare against.  This time
around, we have an operation on types, so we will have to implement it for our
type features, `BooleanType` and `NaturalType`.  The implementations are very
straightforward: because we are in a given feature, we can get the curried
argument (the second type, to compare against), and make sure that it is the
same as the current type, using respectively `isBooleanType` and
`isNaturalType`.  For instance, in `BooleanType`:

{% highlight coq %}
(* BooleanType.v *)

Global Instance TypeEquality__BooleanType
           T `{Functor T} `{T supports BooleanType}
  : ProgramAlgebra ForTypeEquality BooleanType (TypeEqualityResult T)
  :=
    {| programAlgebra :=
         fun _ _ '(MkBooleanType) => fun t => isBooleanType t;
    |}.
{% endhighlight %}

Back to type inference
----------------------

It now suffices to use the overloaded `typeEquality` operation to finish
implementing `typeOf` for `Boolean`.  Of course, we must require the existence
of a `ProgramAlgebra` for the `typeEquality` operation.  Our final
implementation is:

{% highlight coq %}
(* Boolean.v *)

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
{% endhighlight %}

The implementation for `Natural` is strictly simpler, so we won't spend time
examining it here.  We have defined `eval` and its evaluation algebras, as well
as `typeOf` and its type inference algebras.  The third piece necessary to be
able to state our theorem of interest is the aforementioned extensible relation
`WellTypedValue`, defining which expressions are considered values, and what
their type is.

Indexed algebras for relations
------------------------------

In a non-extensible setting, we would define this relation as an indexed family,
`WellTypedValue : Type -> Expr -> Prop`.  To deal with the indexing, we will
need to define indexed versions of functors, sub-functors, algebras, etc.  I
will use some notations to try and keep things concise.  An `I-indexedProp` will
simply be a proposition indexed by some type `I`.  An `I-indexedPropFunctor`
will be a functor taking an `I-indexedProp` to an `I-indexedProp`.  In practice,
it will mean one of our extensible `I`-indexed relations.

{% highlight coq %}
(* IndexedFunctor.v *)

Notation "I '-indexedProp'" := (I -> Prop) (at level 50, only parsing).
Notation "I '-indexedPropFunctor'" := (I-indexedProp -> I-indexedProp) (at level 50).
{% endhighlight %}

This lets us have one index, but `WellTypedValue` would really like to have two
indices: a type, and an expression.  To reconcile this, we will worked with
uncurried versions of our multi-indexed relations.  Instead of simply packing
together our indices with anonymous pairs, it will be nicer to define a record
type to use as the uncurried index.  For `WellTypedValue`, we will therefore
use the following type for index:

{% highlight coq %}
(* WellTypedValue.v *)

Record TypedExpr T E : Set :=
  {
    type : Fix T;
    expr : Fix E;
  }.
{% endhighlight %}

With this, we can define `WellTypedValue` by components, as a bunch of
`(TypedExpr T E)-indexedPropFunctor`.  We can combine those in an analog way to
program algebras, using a sum of indexed functors.  The implementation of this
relation for `Boolean` is fairly trivial:

{% highlight coq %}
(* Boolean.v *)

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
{% endhighlight %}

A `Boolean` value is one built with the `boolean` constructor, and its type is
`booleanType`.  Expressions constructed with `ifThenElse` are not considered
values, until they are evaluated.  The implementation for `Natural` is
analogous, with only `natural` being a value.

Type soundness statement
------------------------

We now have all the pieces ready to state our theorem!  Without further ado:

{% highlight coq %}
(* Soundness.v *)

Definition SoundnessStatement
           {T E V}
           `{Functor T} `{Functor E} `{Functor V}
           (WTV : (TypedExpr T V)-indexedPropFunctor)
           `{Eval__E   : ProgramAlgebra ForEval   E (EvalResult   V)}
           `{TypeOf__E : ProgramAlgebra ForTypeOf E (TypeOfResult T)}
           (e : Fix E)
  : Prop
  := forall (tau : Fix T),
    typeOf e = Some tau ->
    IndexedFix WTV {| type := tau; expr := eval e; |}.
{% endhighlight %}

For some given type language `T`, expression language `E`, "value" language `V`,
well-typed relation `WTV`, evaluation algebra `Eval__E`, and type inference
algebra `TypeOf__E`, the soundness statement for some expression `e` states that
if its type is inferred to be `tau`, then `eval e` is a well-typed value of type
`tau`.

Note that the language `V` may contain non-values, to be more precise, it is the
target language of our evaluator.  Also notice that we weirdly placed `e` within
the parameters, but `tau` within the proposition: this will come in handy to
build an extensible proof, but rest assured that we will prove the statement for
all `e`!

If we have an algebra for our `SoundnessStatement`, we would like to be able to
conclude soundness for all expressions!  But because `Prop` is not
computationally relevant, it would be somewhat silly to build a
`ProgramAlgebra`, we don't need the power of Mendler algebras for proofs.  Let
us have a `ProofAlgebra` type class for tagged F-algebras, meant for proofs.

{% highlight coq %}
(* Algebra.v *)

Class ProofAlgebra (Tag : Set) F A :=
  {
    proofAlgebra : Algebra F A;
  }.
{% endhighlight %}

With such a proof algebra, our theorem for soundness will be:

{% highlight coq %}
(* Soundness.v *)

Theorem Soundness
        {T E V}
        `{Functor T} `{Functor E} `{Functor V}
        (WTV : (TypedExpr T V)-indexedPropFunctor)
        `{Eval__E      : ProgramAlgebra ForEval      E (EvalResult   V)}
        `{TypeOf__E    : ProgramAlgebra ForTypeOf    E (TypeOfResult T)}
        `{Soundness__E : ProofAlgebra   ForSoundness E (sig (SoundnessStatement WTV))}
  : forall (e : Fix E) (tau : Fix T),
    typeOf e = Some tau ->
    IndexedFix WTV {| type := tau; expr := eval e; |}.
{% endhighlight %}

Hmmm, what's this `sig (SoundnessStatement WTV)` business?  Well, as part of the
proof, we will need to instantiate our inductive hypothesis of soundness for a
variety of expressions.  Unfortunately, our algebras don't have a way of making
the type of their output depend on the value they are folding over.  However,
there is a roundabout way of doing so: the algebra could return a dependent pair
`{ e : Fix E | SoundnessStatement WTV e }`, whose first component is the very
expression that was passed in, and the second component is the proof that our
property holds for that expression.  Of course, this signature does not enforce
that the expression we get out is the same that was folded over: the proof
algebra could be cheeky and pick some arbitrary `e` and build the proof for that
one only!  In the subsequent post, we will add a well-formedness condition for
our proof algebras so that they may not cheat so.  For now, we will simply be
diligent in building proof algebras, and assume that all proof algebras are well
behaved.

The proof of our `Soundness` theorem will follow from a lemma asserting that
well-formed proof algebras let us reason by induction over them:

{% highlight coq %}
Lemma Induction
      {Tag F} `{Functor F}
      {P : Fix F -> Prop}
      `{ProofAlgebra Tag F (sig P)}
  : forall (f : Fix F),
    P f.
Admitted. (* similar lemma to be proven in another blog post *)
{% endhighlight %}

Of course we won't be able to prove this lemma until we describe well-formedness
for proof algebras.  So for today, we admit it.

Type soundness algebras
-----------------------

While we glossed over some of the theory, building proof algebras for our couple
language features will provide plenty enough entertainment for this blog post.
Let's start with the `Boolean` language feature.  I like to define an induction
principle for each language feature: we will use it to build proof algebras
piece wise, constructor by constructor.

{% highlight coq %}
(* Boolean.v *)

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
{% endhighlight %}

The `H__boolean` hypothesis must prove the base case, while the `H__ifThenElse`
hypothesis receives condition `c`, then-branch `t` and else-branch `e`, packed
with their induction hypothesis (remember, `sig P` stands for `{ x : Fix E | P
x }`, a pair of an expression and its `P` proof).

Let's start by proving the base case `boolean` for `Soundness`.  The lemma we want is:

{% highlight coq %}
(* Boolean.v *)

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
  : forall (b : bool), SoundnessStatement WTV (boolean b).
(* This unfolds to:

    forall (b : bool),
      forall tau,
        typeOf (boolean b) = Some tau ->
        IndexedFix WTV {| type := tau; expr := eval (boolean b); |}.

*)
{% endhighlight %}

Why should this hold?  Well, `typeOf (boolean b)` better give us `Some
booleanType`, so `tau` should be equal to `booleanType`.  On the other hand,
`eval (boolean b)` should reduce to `boolean b`.  And indeed, because `WTV
supports WellTypedValue__Boolean`, it should agree that `boolean b` is a value,
and that its type is `booleanType`.  Let's see how this plays out in practice.

As we begin the proof, we can start unfolding `typeOf` and `eval`, revealing
which overloaded definition is being used.  After unfolding several definitions,
the goal is stuck at:

{% highlight coq %}
programAlgebra (Fix E) (mendlerFold programAlgebra) (inject (MkBoolean b)) = Some tau ->
  IndexedFix WTV
    {|
    type := tau;
    expr := programAlgebra (Fix E) (mendlerFold programAlgebra)
              (inject (MkBoolean b)) |}
{% endhighlight %}

Both the `typeOf` and the `eval` operations are stuck trying to dispatch,
because they're supposed to use the algebra for `E`, which is an abstract
super-functor.  But the term they receive is `inject (MkBoolean b)`, so we'd
expect the dispatch to go to the `Eval__Boolean` and `TypeOf__Boolean` algebras,
respectively.  However, this is only true if the super-functor has been
correctly built, and Coq cannot guarantee this without us explicitly stating
it.  What we need now is a property stating that a program algebra for a
super-functor correctly dispatches to its sub-functors.

{% highlight coq %}
(* Algebra.v *)

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
{% endhighlight %}

Given two ambient program algebras for some operation, one operating over a
super-functor `E`, and the other one operating about one of its sub-functors
`F`, the super-algebra is a well-formed compound algebra when the result of
running the super-algebra over a `F`-expression upcasted into an `E`-expression
is the same as the result of running the algebra for `F` over the initial
`F`-expression.  No shenanigans when injecting expressions into larger languages!

We can automatically build proof of well-formed compoundness via type class
instances, since we will always create larger algebras using sums of functors.
Having done so, we can now add a `WellFormedCompoundProgramAlgebra` condition to
our `Soundness__boolean`, which will let us make progress from our stuck goal:

{% highlight coq %}
programAlgebra (Fix E) (mendlerFold programAlgebra) (inject (MkBoolean b)) = Some tau ->
  IndexedFix WTV
    {|
    type := tau;
    expr := programAlgebra (Fix E) (mendlerFold programAlgebra)
              (inject (MkBoolean b)) |}
{% endhighlight %}

We can now rewrite with `wellFormedCompoundProgramAlgebra`, and simplify this
goal!

{% highlight coq %}
Some booleanType = Some tau ->
IndexedFix WTV {| type := tau; expr := boolean b |}
{% endhighlight %}

The first equality can be inverted to show that `tau` is equal to `booleanType`,
and so our final goal is:

{% highlight coq %}
IndexedFix WTV {| type := booleanType; expr := boolean b |}
{% endhighlight %}

Clearly this ought to be true!  In general, to prove a result of a fixed point
type, we need to use the wrapping function for that fixed point (here,
`indexedWrapF`).  It asks us to provide an unwrapped value:

{% highlight coq %}
WTV (IndexedFix WTV) {| type := booleanType; expr := boolean b |}
{% endhighlight %}

One of our preconditions was that this abstract `WTV` was a super-functor of our
concrete `WellTypedValue__Boolean`.  As such, we can create a `WTV` value by
injecting a `WellTypedValue__Boolean` value into it.  Our final goal is:

{% highlight coq %}
WellTypedValue__Boolean (IndexedFix WTV) {| type := booleanType; expr := boolean b |}
{% endhighlight %}

This is exactly the case that's handled by the `WellTypedValue__boolean`
constructor, and so the proof is concluded!

Alright, but this was the easy, base case right?  Let's now turn to the
`ifThenElse` case, as it will bring up more challenges!  Learning from the base
case, we can start stating this lemma as:

{% highlight coq %}
(* Boolean.v *)

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
  : forall (c t e : sig (SoundnessStatement WTV)),
    let c := proj1_sig c in
    let t := proj1_sig t in
    let e := proj1_sig e in
    SoundnessStatement WTV (ifThenElse c t e).
(* This unfolds to:

forall (c t e : sig (SoundnessStatement WTV)),
    let c := proj1_sig c in
    let t := proj1_sig t in
    let e := proj1_sig e in
    forall tau,
      typeOf (ifThenElse c t e) = Some tau ->
      IndexedFix WTV {| type := tau; expr := eval (ifThenElse c t e); |}.

*)
{% endhighlight %}

Because this is an inductive case, we can ask for `c`, `t`, and `e`, to come
bundled with a proof that they themselves satisfy the soundness statement (that
is, that they each evaluate to a well-typed value).  This is, again, achieved
via `sig`, a dependent pair type.  After some unfolding, more uses of our
well-formed dispatching lemma, and some re-folding, the goal is:

{% highlight coq %}
  forall tau : Fix T,
  match typeOf c with
  | Some tau__c =>
      if isBooleanType tau__c
      then
       match typeOf t with
       | Some tau__t =>
           match typeOf e with
           | Some tau__e =>
               if typeEquality tau__t tau__e then Some tau__t else None
           | None => None
           end
       | None => None
       end
      else None
  | None => None
  end = Some tau ->
  IndexedFix WTV
    {|
    type := tau;
    expr := match isBoolean (eval c) with
            | Some true => eval t
            | Some false => eval e
            | None => stuck IfConditionNotBoolean
            end |}
{% endhighlight %}

The long pre-condition is the inlining of the implementation of `typeOf` for
`ifThenElse`.  Similarly, the `match` in the conclusion is the inlining of
`eval` for `ifThenElse`.  Nothing should be surprising here.  Notice that most
branches of the hypothesis produce a `None`, yet the pre-condition wants a `Some
tau`, so we can destruct the discriminees of those `match` statements and
immediately disregard all but the one `Some`-producing case.  So we destruct
`typeOf c`, and find it to be equal to `Some tau__c`, which we retain as an
equation!  Indeed we can use it to instantiate the induction hypothesis for `c`,
form which we derive `IndexedFix WTV {| type := tau__c; expr := eval c |}`!
Same goes for `typeOf t` and `typeOf e`.

Along the way, we also picked up two extra equations, `isBooleanType tau__c =
true`, and `typeEquality tau__t tau__e = true`.  After unifying `tau` with
`tau__t` by inversion, the goal to be proven is:

{% highlight coq %}
IndexedFix WTV
    {|
    type := tau__t;
    expr := match isBoolean (eval c) with
            | Some true => eval t
            | Some false => eval e
            | None => stuck IfConditionNotBoolean
            end |}
{% endhighlight %}

Now this is a little more involved than our base case.  There are three ways
this could go, based on the evaluation of `isBoolean (eval c)`:

1. If it evaluates to `Some true`, then we'd need to show that `eval t` is a
   value of type `tau__t`.  This is easy, we have an inductive assumption
   stating it!

2. If it evaluates to `Some false`, then we'd need to show that `eval e` is a
   value of type `tau__t`... huh, our induction hypothesis tells us it's a value
   of type `tau__e` though.  But remember we picked up this `typeEquality tau__t
   tau__e = true` assumption?  We will need to work with this to show that
   indeed `tau__t` and `tau__e` are equal.

3. If it evaluates to a `None`, that is, it was either not a value, or not a
   boolean one... well, that can **not** happen, and this can be demonstrated
   thanks to our induction hypothesis on `c`, and the `isBooleanType tau__c =
   true` we picked up along the way.

Let's go ahead and show that case 3 may not happen, by proving that `isBoolean
(eval c)` evaluates to `Some b` for some `b`.  Let me give you the big
picture.  Because `isBooleanType tau__c = true`, we should be able to show that
`tau__c = booleanType`.  Now, this should let us transform our induction
hypothesis on `c` to look like `IndexedFix WTV {| type := booleanType; expr :=
eval c; |}`.  Just like we wanted to know that compound program algebras
dispatched to the appropriate sub-functor, we would also like to know that
compound inductive relations invert into the appropriate indexed sub-functor.
In particular, we set things up here so that values of the `booleanType` type
are described by the `WellTypedValue__Boolean` indexed functor.  We would like
to be able to invert `IndexedFix WTV {| type := booleanType; expr := eval c; |}`
into the concrete `WellTypedValue__Boolean (IndexedFix WTV) {| type :=
booleanType; expr := eval c; |}`, which itself should be invertible into
demonstrating that `eval c = boolean b` for some `b`.

Of course, it could be that `WTV` is made up of another indexed functor that
tries and add other values of `booleanType`!  So we should only be able to
perform such an inversion under some well-formedness conditions for `WTV`,
namely, that it only allows `booleanType` via `WellTypedValue__Boolean`.
This property looks like this:

{% highlight coq %}
(* WellTypedValueProjection.v *)

Definition WellTypedValueProjectionStatement
           {T V}
           (WellTypedValue__F : (TypedExpr T V)-indexedPropFunctor)
           (tau : Fix T)
           (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
           (tv : TypedExpr T V)
  : Prop
  := type tv = tau ->
     WellTypedValue__F (IndexedFix WellTypedValue__V) tv.
{% endhighlight %}

Given an indexed functor `WellTypedValue__F`, and a concrete type `tau`, an
indexed functor `WellTypedValue__V` projects correctly if whenever the type of
some typed expression `tv` is `tau`, we can conclude that this typed expression
satisfies `WellTypdeValue__F`, with its sub-expressions satisfying the
(hypothetically larger) `WellTypedValue__V`.  We can now add the following
pre-condition to our proof:

{% highlight coq %}
      `{! IndexedProofAlgebra
          ForWellTypedValueProjection
          WTV
          (WellTypedValueProjectionStatement WellTypedValue__Boolean
                                             booleanType
                                             WTV)
       }
{% endhighlight %}

stating that `WTV` can be inverted into `WellTypedValue__Boolean` whenever the
type of some typed expression is `booleanType`.  Implementing instances of this
proof algebra is almost trivial, so let's move on.

We still have to show that we can invert `isBooleanType tau__c = true` into
`tau__c = booleanType`.  If you look up the implementation of `isBooleanType`,
it tries to project its input from whichever super-functor it lives in, down to
`BooleanType`.  If this succeeds, well, given there's only one `BooleanType`
constructor, we've pretty much concluded that it was indeed `booleanType`.  So
we have `projectF tau__c = Some MkBooleanType`, and we'd like to conclude
`tau__c = inject MkBooleanType`.  For today, we will take this as an axiom, stay
tuned for some rigorous proof!

Combining our two previous insights lets us deduce `WellTypedValue__Boolean
(IndexedFix WTV) {| type := tau__c; expr := eval c |}` at last!  We can now
invert this concrete inductive predicate to deduce that `eval c = boolean b` for
some `b : bool`.  I don't quite like Coq's `inversion` tactic in this case, so I
like to roll my own inversion lemma.

{% highlight coq %}
(* Boolean.v *)

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
{% endhighlight %}

Of particular note, I place the inversion equation `{| type := tau; expr := v |}
= tv` right at the beginning of my induction hypothesis, so that I can use
ssreflect's rewriting mechanism to immediately clean up my goal.  After this
inversion, our goal is:

{% highlight coq %}
IndexedFix WTV
    {|
    type := tau__t;
    expr := match isBoolean (boolean b) with
            | Some true => eval t
            | Some false => eval e
            | None => stuck IfConditionNotBoolean
            end |}
{% endhighlight %}

This is tantalizingly close!  Surely `isBoolean (boolean b)` must evaluate to
`Some b`, right?...  Well, not so fast.  `isBoolean` essentially boils down to
`project . unwrapF`, where I use `.` for function composition.  On the other
hand, `boolean` boils down to `wrapF . inject . MkBoolean`.  Once unfolded,
`isBoolean (boolean b)` is actually `project (unwrapF (wrapF (inject (MkBoolean
b))))`.

So let's take this slowly: we start with `MkBoolean b`, of type `Boolean (Fix
E)`.  We `inject` it into `E`, yielding a value of type `E (Fix E)`.  We then
`wrapF` this value into a `Fix E`.  Now we `unwrapF` it, back to an `E (Fix E)`,
and we try and `project` that down into `Boolean`, resulting in an `option
(Boolean (Fix E))` (remember, `project` has to defend against projecting in the
wrong sub-functor with `option`).

But clearly we know that this is the correct sub-functor, since we just came
from it!  We're going to want a lemma stating that `unwrapF . wrapF` is an
identity.  Again, we will axiomatize this lemma for today.  Second, we'd like to
know that for any expression `e`, `project (inject e) = Some e`, where `project`
and `inject` are operating with the same sub-functor.  To make our life easier,
we can add this as a requirement to our `SubFunctor` type class.

{% highlight coq %}
(* SubFunctor.v *)

Class SubFunctor
      F E
      `{Functor F} `{Functor E}
  :=
    {
      inject  : forall {A : Set}, F A -> E A;
      project : forall {A : Set}, E A -> option (F A);
      (* NEW: *)
      project_inject : forall {A} {fa : F A},
        project (inject fa) = Some fa;
    }.
{% endhighlight %}

That's enough tooling to conclude that `isBoolean (boolean b) = Some b`, and our
goal finally reduces to:

{% highlight coq %}
IndexedFix WTV {| type := tau__t; expr := if b then eval t else eval e |}
{% endhighlight %}

We can destruct the `bool` value `b`, and in the `true` case, immediately use
our induction hypothesis for `t` to conclude.  In the `false` case however, as I
warned earlier, we must show that `eval e` is a value of type `tau__t`, while
our induction hypothesis guarantees it has type `tau__e`.  But we have not yet
used our equation `typeEquality tau__t tau__e = true`.  We would like to show
that we can invert it into a proof of equality `tau__t = tau__e`, which means,
we must prove that the type equality operation is correct.

Interlude : algebras for the correctness of type equality algebras
------------------------------------------------------------------

You must be used to it by now, we define the property statement for correctness
of type equality, as well as a fold of of a proof algebra yielding proofs for
some abstract implementation (again, we currently rely on the axiomatized
`Induction`).

{% highlight coq %}
(* TypeEquality.v *)

Definition TypeEqualityCorrectnessStatement
           {T} `{Functor T}
           {typeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
           (tau : Fix T)
  : Prop
  := forall tau',
    typeEquality tau tau' = true ->
    tau = tau'.

Variant ForTypeEqualityCorrectness := .

Lemma typeEqualityCorrectness
      {T} `{Functor T}
      {typeEquality__T : ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
      `{PA : ! ProofAlgebra ForTypeEqualityCorrectness T (sig TypeEqualityCorrectnessStatement)}
  : forall tau, TypeEqualityCorrectnessStatement tau.
Proof.
  move => tau.
  apply (Induction tau).
Qed.
{% endhighlight %}

Let's implement this proof algebra for `BooleanType` to get a feel for how it
goes.

{% highlight coq %}
(* BooleanType.v *)

Global Instance TypeEqualityCorrectness__BooleanType
       {T} `{Functor T}
       `{! T supports BooleanType}
       `{! ProgramAlgebra ForTypeEquality T (TypeEqualityResult T)}
       `{! WellFormedCompoundProgramAlgebra ForTypeEquality T BooleanType}
  : ProofAlgebra
      ForTypeEqualityCorrectness
      BooleanType
      (sig TypeEqualityCorrectnessStatement).
{% endhighlight %}

The proof requires us to provide a dependent pair `{x : Fix T |
TypeEqualityCorrectnessStatement x}`.  Because we are not trying to cheat here,
we instantiate `x` to `booleanType`, equal to the input we are folding, and show
that indeed it satisfies the correctness property.  In the next post, we will
forbid cheating altogether, of course.  The goal is therefore to show:

{% highlight coq %}
forall tau' : Fix T, typeEquality booleanType tau' = true -> booleanType = tau'
{% endhighlight %}

That is, if some other type `tau'` is found to be equal to `booleanType` by our
decision procedure, then it is indeed propositionally equal to `booleanType`.
By virtue of unfolding and properly dispatching to the program algebra for
`typeEquality`, this reduces to:

{% highlight coq %}
isBooleanType tau' = true -> booleanType = tau'
{% endhighlight %}

Some more unfolding and rewriting reveals:

{% highlight coq %}
project (unwrapF tau') = Some MkBooleanType -> booleanType = tau'
{% endhighlight %}

If this `project` succeeds, it must be that the value that was injected was
`MkBooleanType`.  This is not guaranteed for ill-formed sub-functors, so once
again, we will enrich our definition of `SubFunctor` to guarantee this:

{% highlight coq %}
(* SubFunctor.v *)

Class SubFunctor
      F E
      `{Functor F} `{Functor E}
  :=
    {
      inject  : forall {A : Set}, F A -> E A;
      project : forall {A : Set}, E A -> option (F A);
      (* NEW: *)
      project_success : forall {A} {ea : E A} {fa : F A},
          project ea = Some fa -> ea = inject fa;
      project_inject : forall {A} {fa : F A},
          project (inject fa) = Some fa;
    }.
{% endhighlight %}

This lets us proceed to:

{% highlight coq %}
unwrapF tau' = inject MkBooleanType -> booleanType = tau'
{% endhighlight %}

This is pretty close to being over.  `booleanType` is defined as `injectF
MkBooleanType`, which itself means `wrapF (inject MkBooleanType)`.  We can apply
`wrapF` to both sides of our hypothesis, to obtain, after unfolding:

{% highlight coq %}
wrapF (unwrapF tau') = wrapF (inject MkBooleanType) ->
wrapF (inject MkBooleanType) = tau'
{% endhighlight %}

All that's left to do is to show that `wrapF` and `unwrapF` are inverses.  Sorry
to disappoint, but that's also a subject for the next post.  Assuming it to be
true, the proof is now over.

Concluding soundness for `Boolean`
----------------------------------

Back to our `Soundness__ifThenElse` proof, we needed correctness of type
equality.  We can add this pre-condition:

{% highlight coq %}
      `{! ProofAlgebra
          ForTypeEqualityCorrectness
          T
          (sig TypeEqualityCorrectnessStatement)
       }
{% endhighlight %}

and finish the proof by instantiating `typeEqualityCorrectness` with this proof algebra!

The proof of soundness for `Boolean` follows immediately.  The proof of
soundness for `Natural` is very similar to that of `Boolean`, so we won't go
into details here.

Instantiating our languages, operations, and proofs
---------------------------------------------------

If you've followed this far, you must be dying for some concrete instantiation
of all those overloaded operations and theorems!  In fact, a lot of our theorems
have pretty complex, overloaded pre-conditions, that we better be sure we can
instantiate fully.  So let's build a small language, made of both `Boolean` and
`Natural`, derive its evaluation and type inference, and prove their soundness.

{% highlight coq %}
(* Demo.v *)

Definition TypeLanguage       := (BooleanType + NaturalType        )%Sum1.
Definition ExpressionLanguage := (Boolean     + Natural            )%Sum1.
Definition ValueLanguage      := (Boolean     + Natural     + Stuck)%Sum1.
{% endhighlight %}

Our type language and expression language are straightforward.  Because
evaluation may fail, our value language also has to support `Stuck`.  Type
soundness will guarantee that well-typed programs don't get stuck though!

We now instantiate our program algebras and indexed relation algebras.

{% highlight coq %}
(* Demo.v *)

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
{% endhighlight %}

`eval` and `typeOf` are derived by type class instantiation of the overloaded
operation, guided by their input and output type.  We manually craft
`WellTypedValue` to be the indexed sum of its `Boolean` and `Natural`
components.

Before starting our proofs, it'd be nice to run some examples of `typeOf` and
`eval`, just to see that they behave according to our expectations.  You may
try:

{% highlight coq %}
(* Demo.v *)

Compute typeOf (natural 42).

(* OUTPUT: *)
= Some
         (fun (A : Set) (x : MendlerAlgebra TypeLanguage A) =>
          x
            (forall x0 : Set,
             (forall x1 : Set,
              (x1 -> x0) -> (BooleanType + NaturalType)%Sum1 x1 -> x0) -> x0)
            (fun
               x0 : forall x0 : Set,
                    (forall x1 : Set,
                     (x1 -> x0) -> (BooleanType + NaturalType)%Sum1 x1 -> x0) ->
                    x0 => x0 A x) (inr1 MkNaturalType))
     : TypeOfResult TypeLanguage
{% endhighlight %}

Oof!  Whereas in the previous post, I made our evaluation algebras compute into
a concrete type, now they compute into the extensible type `ValueLanguage`.  Our
result is represented as a fold, and quite hard to read, though if you look deep
within, you'll see a reassuring `inr1 MkNaturalType`.  To make inspection of
results less painful, it pays off to define a small concrete type for the
results we expect, and a small algebra to reduce extensible results into
concrete results.

{% highlight coq %}
(* Demo.v *)

Variant InspectType :=
| InspectBooleanType
| InspectNaturalType
| InspectIllTyped
.

Definition inspectTypeOf
  : Fix ExpressionLanguage -> InspectType
  := fun e =>
       match typeOf e with
       | None     => InspectIllTyped
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
{% endhighlight %}

The algebra converts the constructor of each extensible type language into the
matching constructor in our concrete type language.  Note that I am using a
helper dispatch function that sends handlers to their respective sub-functor:

{% highlight coq %}
(* Sum1.v *)

Definition sum1Dispatch
           {A} {L R : Set -> Set} {O}
           (fl : L A -> O) (fr : R A -> O) (v : (L + R)%Sum1 A)
  : O
  :=
    match v with
    | inl1 l => fl l
    | inr1 r => fr r
    end.

Notation "f || g" := (sum1Dispatch f g) : Sum1.
{% endhighlight %}

And here it is:

{% highlight coq %}
Compute inspectTypeOf (natural 42).

(* OUTPUT: *)
     = InspectNaturalType
     : InspectType
{% endhighlight %}

The demo file contains a similar concrete type for values and inspection
algebra, with some examples of running `eval` on some terms.  Note that `eval`
is entirely untyped, and so it will happily evaluate ill-typed terms to some
value.

We can finally state the soundness theorem for those languages and operations!
Here it is, and its proof should be simple by apply `Soundness` from the
`Soundness` module...

{% highlight coq %}
(* Demo.v *)

Theorem Soundness
  : forall (tau : Fix TypeLanguage) (e : Fix ExpressionLanguage),
    typeOf e = Some tau ->
    IndexedFix WellTypedValue {| type := tau; expr := eval e; |}.
Proof.
  move => tau e.
  apply Soundness.
{% endhighlight %}

This, unfortunately, does not finish the proof.  We are left with the goal:

{% highlight coq %}
ProofAlgebra ForSoundness ExpressionLanguage
    {x : Fix ExpressionLanguage | SoundnessStatement WellTypedValue x}
{% endhighlight %}

Something went wrong in instantiating this type class.  Let us try to manually
instantiate it to find out the culprit.  Because `ExpressionLanguage` is a
compound language, this algebra should be built by gluing together sub-algebras
for each component.  We try to apply the indexed sum program algebra
constructor, and to dispatch all obligations using type class automation:

{% highlight coq %}
  apply ProofAlgebra__Sum1; try typeclasses eauto.
{% endhighlight %}

Two goals remain:

{% highlight coq %}
(* 1 *)
  ProofAlgebra ForSoundness Boolean
    {x : Fix ExpressionLanguage | SoundnessStatement WellTypedValue x}

(* 2 *)
  ProofAlgebra ForSoundness Natural
    {x : Fix ExpressionLanguage | SoundnessStatement WellTypedValue x}
{% endhighlight %}

We'd hope the first goal to resolve by appealing to `Soundness__Boolean`.

{% highlight coq %}
  eapply Soundness__Boolean; try typeclasses eauto.

(* GOAL: *)
  IndexedProofAlgebra ForWellTypedValueProjection WellTypedValue
    (WellTypedValueProjectionStatement WellTypedValue__Boolean booleanType WellTypedValue)
{% endhighlight %}

`WellTypedValue` is a compound relation, so its proof algebra should be a sum of
indexed functors.

{% highlight coq %}
  apply IndexedProofAlgebra__Sum1; try typeclasses eauto.

(* GOAL: *)
  IndexedProofAlgebra ForWellTypedValueProjection WellTypedValue__Natural
    (WellTypedValueProjectionStatement WellTypedValue__Boolean booleanType WellTypedValue)
{% endhighlight %}

And here's the problem!

This algebra tries to fold proofs of `WellTypedValue` into proofs of
`WellTypedValueProjectionStatement`.  In the case where the folded proof was of
the `WellTypedValue__Boolean` sub-functor, it uses the
`WellTypedValueProjection__Boolean` sub-algebra, and all is well.  But when the
folded proof was of the `WellTypedValue__Natural` sub-functor, what happens?

Does it even make sense to prove `WellTypedValueProjectionStatement` in such
cases!?  Luckily, we set it up such that it does.  Remember,
`WellTypedValueProjectionStatement` was phrased as:

{% highlight coq %}
(* WellTypedValueProjection.v *)

Definition WellTypedValueProjectionStatement
           {T V}
           (WellTypedValue__F : (TypedExpr T V)-indexedPropFunctor)
           (tau : Fix T)
           (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
           (tv : TypedExpr T V)
  : Prop
  := type tv = tau ->
     WellTypedValue__F (IndexedFix WellTypedValue__V) tv.
{% endhighlight %}

If we have a proof that `WellTypedValue__Natural (IndexedFix WellTypedValue)
tv`, can we deduce `WellTypedValueProjectionStatement WellTypedValue__Boolean
booleanType WellTypedValue tv`?  Indeed we can, thank to the pre-condition in
the statement!  Because `tv` is a `Natural` value, `type tv` will be equal to
`naturalType`, and as such, cannot possibly be equal to `booleanType`.  The
pre-condition is therefore false, and so the proof is over!

But do we really want to create a lemma for this fact?  If we add more types to
our type language, will we really want to create a lemma saying that this type
does not interfere with `booleanType`?  This would quickly lead to an unpleasant
quadratic number of lemmas, as we would need to show non-intereference for all
pairings of features!  Let's automate this task away: if we ever need to provide
an `IndexedProofAlgebra ForWellTypedValueProjection`, we can try and
automatically solve it whenever the source indexed algebra (here
`WellTypedValue__Natural`) does not match the target indexed algebra (here
`WellTypedValue__Boolean`).

{% highlight coq %}
(* WellTypedValueProjection.v *)

Ltac wellTypedValueProjection__Other :=
  constructor;
  rewrite /IndexedAlgebra;
  move => i [];
  rewrite /WellTypedValueProjectionStatement /=;
  move => *;
  match goal with
  | [ A : @eq (Fix ?T) ?tau _
    , B : @eq (Fix ?T) ?tau _
    |- _
    ] => move : A B
  end;
  move ->;
  move /(wrapF_inversion (inject _) (inject _));
  move /(discriminate_inject _ _ _) => //.

Hint Extern 5
     (IndexedProofAlgebra ForWellTypedValueProjection _ _)
=> wellTypedValueProjection__Other : typeclass_instances.
{% endhighlight %}

The unreadable tactic `wellTypedValueProjection__Other` does just that.  Its
code searches the context to derive two contradicting equalities, e.g. `tau =
booleanType` and `tau = naturalType`, then performs some inversion to derive a
contradiction.  We then register this tactic as a solver for type classes, so
that it may be tried every time such an obligation arises.  This requires two
new lemmas, `wrapF_inversion`, which is derived from the axiomatized
`unwrapF_wrapF`, and `discriminate_inject`, which we will prove next time!

With this, the proof of `Soundness` for our concrete langage is finally
complete.

To be continued...
------------------

Alright, that was a lot of information!  While the proof is over, we introduced
many axioms along the way.  Solving those axioms requires modifying all of our
algebras slightly, which will make the presentation quite more inscrutable, but
the overall structure of the proofs will be the same.
