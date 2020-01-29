---
layout: post
title: "Deep dive into Meta-Theory à la Carte (part 1)"
date: 2020-01-28 14:02:00 -0700
permalink: deep-dive-meta-theory-carte-1
comments: true
categories:
---

Meta-Theory à la Carte
----------------------

I have been quite interested in "Meta-Theory à la Carte", published at POPL 2013
by Benjamin Delaware, Bruno C. d. S. Oliveira, and Tom Schrijvers.
Unfortunately, the paper is quite complicated, contains a couple typos in the
code fragments, and the associated code base is very sparsely commented, and
does not compile with modern versions of the Coq proof assistant.

Fortunately, the paper is written well enough that it was not too complicated to
rebuild a subset of their results, with the help of their code base.  In the
process, I have learned a lot about the design philosophy of the paper, and will
try to convey a deeper understanding to anyone reading this series of posts.

Let's get started with a motivating example.

Open recursion for extensibility
--------------------------------

Say you want to study two languages and their respective expressivity.  For a
contrived example, say the simply-typed lambda calculus with boolean constants
and operations, versus the simply-typed lambda calculus with natural number
constants and operations.  You could define these two languages as:

{% highlight coq %}
Inductive Lang1 :=
| Lambda ...
| App ...
| Var ...
| Number (n : nat)
| Plus (m n : Lang1)
.

Inductive Lang2 :=
| Lambda ...
| App ...
| Var ...
| Boolean (b : bool)
| IfThenElse (condition thenBranch elseBranch : Lang2)
.
{% endhighlight %}

But you now have two full-fledged, unconvertible copies of the simply-typed
lambda calculus: you will most likely need to implement its static and dynamic
semantics twice, resulting in frustrating code duplication.  The dream would
be to be able to define the lambda calculus package once, and reuse it in two
larger languages.  What would this look like?  Let's focus on the easier case of
the boolean sub-language (the lambda calculus will add extra noise due to
variable binding).  If we had to define a standalone data type for just the
boolean constructors, it would look like:

{% highlight coq %}
Inductive Boolean :=
| MkBoolean (b : bool)
| IfThenElse (condition thenBranch elseBranch : ...)
.
{% endhighlight %}

But how to fill the ellipsis?  Clearly, putting `Boolean` is unsatisfactory,
because this would create a closed language of just the boolean constructor and
the if-then-else operation, no other constants or operations allowed in!

In order to allow any expression of a given larger language `E`, we must take as
an argument the type of this yet-to-be-determined larger expression language:

{% highlight coq %}
Inductive Boolean (E : Set) : Set :=
| MkBoolean (b : bool)
| IfThenElse (condition thenBranch elseBranch : E)
.
{% endhighlight %}

Note that the `MkBoolean` constructor does not make use of the type `E` in its
arguments: it asks for a `bool` value `b`, and is happy being a value of type
`Boolean E` with no other condition.  On the other hand, the `IfThenElse`
constructor wants its three arguments to be values of type `E`, the expression
language we will eventually construct.

What type to give extensible terms?
-----------------------------------

At this point, we should expect to be able to create values that only require
features of the `Boolean` language, for instance, we ought to be able to encode
the expression:

```
if true then false else true
```

in our language.  Naively, it should be:

{% highlight coq %}
Definition e := IfThenElse (MkBoolean true) (MkBoolean false) (MkBoolean true).

(* NOTE: you will need to make the `E` argument to those constructors implicit. *)
{% endhighlight %}

but what type should this expression have?  It actually admits an infinity of
types, of the form:

{% highlight coq %}
Boolean (Boolean _)
{% endhighlight %}

where `_` can be any type.  This may seem extremely surprising!  But if you
think about the type constraints, because `e` is constructed with `IfThenElse`,
it must have type `Boolean ?E1` for some `E1`.  Because the `condition` argument
is built using `MkBoolean`, said `E1` must be equal to `Boolean ?E2` for some
`E2`.  The other two arguments to `IfThenElse` add the exact same constraint,
and so we are left with the conclusion that `e` must have type `Boolean (Boolean
?E2)` for any type `E2`.

This is flexible, but also problematic.  While we could give the expression the
following type:

{% highlight coq %}
Definition e {R} : Boolean (Boolean R)
  := IfThenElse (MkBoolean true) (MkBoolean false) (MkBoolean true).
{% endhighlight %}

it would quickly become irritating to annotate every concrete term with an
explicit description of its layers.  We can do better, by creating a fixed point
for types, that is, given `Boolean : Set -> Set`, we would like to build a type
`BooleanFix : Set`, such that `BooleanFix` behaves just as if it were the
infinite type `Boolean (Boolean (Boolean (Boolean ...)))`.  Coq's type system
will not let us "simply" (that is, equi-recursively) define such a `BooleanFix`
as `Boolean BooleanFix`.  Instead, we have to use what is called an
iso-recursive encoding:

{% highlight coq %}
Inductive BooleanFix : Set
  := Wrap { unwrap : Boolean BooleanFix; }.
{% endhighlight %}

It's almost the same, except the user is left to call `Wrap` and `unwrap`
appropriately to indicate their intent to the type system.  Given such a
type operator, we can finally define expressions of different depths with a
unifying type, `BooleanFix`:

{% highlight coq %}
Definition smallExpression : BooleanFix
  := Wrap (MkBoolean true).

Definition largerExpression : BooleanFix
  := Wrap
       (IfThenElse
          (Wrap (MkBoolean true))
          (Wrap (MkBoolean false))
          (Wrap (MkBoolean true))
       ).
{% endhighlight %}

The price to pay is the presence of `Wrap` at every stage.  This can be
alleviated with smart constructors:

{% highlight coq %}
Definition boolean b : BooleanFix
  := Wrap (MkBoolean b).

Definition ifThenElse c t e : BooleanFix
  := Wrap (IfThenElse c t e).

Definition smallExpression : BooleanFix
  := boolean true.

Definition largerExpression : BooleanFix
  := ifThenElse (boolean true) (boolean false) (boolean true).
{% endhighlight %}

While this `Wrap` business may sound annoying, we will soon replace it with a
more abstract concept that will prove necessary to making the language
extensible.  So don't fret too much about it!

Abstracting to extensible languages
-----------------------------------

Recall `BooleanFix`'s definition:

{% highlight coq %}
Inductive BooleanFix : Set
  := Wrap { unwrap : Boolean BooleanFix; }.
{% endhighlight %}

It let us inject as many layers of `Boolean` inside an outer layer of `Boolean`
as we need.  However, if we intend for our language to be extensible, we should
not inject a copy of the language feature `Boolean` itself, but rather a copy of
the entire expression language!  We would like to generalize `BooleanFix` so
that it accepts as an argument the expression language `E`, and uses it for its
sub-terms:

{% highlight coq %}
Inductive Fix (E : Set -> Set) : Set
  := Wrap { unwrap : E (Fix E); }.
{% endhighlight %}

Unfortunately, Coq will not accept this generalization, as `Fix E` is being
passed as an argument to an abstract `E : Set -> Set`, which is considered an
unsafe occurrence in negative position.  If you do not understand what this
means, you don't need to for the purpose of everything we are doing here, no
worries!  Luckily, there are tricks we can use to get something morally
equivalent.

Instead of requiring the type to be explicitly recursive, we can use its Church
encoding, which is:

{% highlight coq %}
Definition Fix (F : Set -> Set) : Set :=
  forall (A : Set), (F A -> A) -> A.
{% endhighlight %}

This may look very familiar to people having studied abstract algebra.  Indeed,
if `F` is a `Functor`, the encoding of the constructor, of type `F A -> A`
looks exactly like an F-algebra, and this whole type looks like it is performing
a fold with this algebra.

{% highlight coq %}
Definition boolean b : Fix Boolean
  := fun _ alg => alg (MkBoolean b).
{% endhighlight %}

As you see, a value of type `Fix Boolean` is now a function that receives two
arguments: first, the carrier type of the algebra (which we discard here with
`_`), then, the algebra `alg : Boolean A -> A`, that carries the knowledge of
what to do to produce a `A` for all possible `Boolean` values, as long as the
recursive occurrences have themselves been replaced with results of type `A`.
We will later see that this algebra can be used to describe a large class of
recursive computations over extensible data types.

Let us now actually achieve our goal of extensibility: instead of returning a
value of type `Fix Boolean`, we would like to return a value of type `Fix E` for
some language `E`.  Of course, this will require that the language `E` has some
means of storing `Boolean` expressions.  It is therefore reasonable to ask for
such means as an argument to our smart constructor: tell me how to store boolean
expressions, and I will build boolean expressions.

{% highlight coq %}
Definition boolean
           {E : Set -> Set}
           (inject : forall {A : Set}, Boolean A -> E A)
           (b : bool)
  : Fix E
  := fun _ wrap => wrap (inject (MkBoolean b)).
{% endhighlight %}

This takes care of `MkBoolean`, but `IfThenElse` is more complicated.  When the
constructor has recursive occurrences, the smart constructor must do additional
work.  We would like to pass in sub-expressions of the full language, that is,
values of type `Fix E`.  But because our encoding of `Fix` abstracts over the
concrete type of the language, there is a loss of information.  It is no longer
known that the type of the arguments to `IfThenElse` is `Fix E`: it instead
requires arguments of type `S`, where `S` is the universally-quantified type in
the definition of `Fix` (confusingly, it is the type named `E` in the definition
of `Fix`).

Let this not dissuade us: we have access to the function `wrap : E S -> S`, and
our argument `c : Fix E`, is, by definition, capable of targetting any language
when given the appropriate wrapper.  In particular, `c S` has type `(E S -> S)
-> S`, and so providing it with `wrap` will allow `c` to convert itself into a
value of this abstract type `S`.

{% highlight coq %}
Definition ifThenElse
           {E : Set -> Set}
           (inject : forall {A : Set}, Boolean A -> E A)
           (c t e : Fix E)
  : Fix E
  := fun _ wrap => wrap (inject (IfThenElse (c _ wrap) (t _ wrap) (e _ wrap))).
{% endhighlight %}

We now have enough infrastructure to define complex extensible terms, for
instance:

{% highlight coq %}
Definition extensibleTerm
           {E : Set -> Set}
           (inject : forall (A : Set), Boolean A -> E A)
  : Fix E
  := (ifThenElse inject
        (boolean inject true)
        (boolean inject false)
        (boolean inject true)).
{% endhighlight %}

As you can see, it is pretty verbose to manually pass `inject` to every smart
constructor.  This calls for turning it into a type class method, and have our
smart constructors be ad-hoc polymorphic.

{% highlight coq %}
Class SupportsFeature (E F : Set -> Set) :=
  {
    inject : forall (A : Set), F A -> E A;
  }.
Arguments inject {E F _}.
Notation "E 'supports' F" := (SupportsFeature E F) (at level 50).

Definition ifThenElse
           {E : Set -> Set}
           `{E supports Boolean}
           (c t e : Fix E)
  : Fix E
  := fun _ wrap => wrap (inject (IfThenElse (c _ wrap) (t _ wrap) (e _ wrap))).

(* elided: [boolean], [natural], [plus] redefined accordingly... *)

Definition extensibleTerm
           {E : Set -> Set}
           `{E supports Boolean}
           `{E supports Natural}
  : Fix E
  := (ifThenElse (boolean true) (natural 0) (plus (natural 1) (natural 2))).
{% endhighlight %}

Combining two languages into one
--------------------------------

So far, we have seen that we can define extensible language features as
parameterized inductive types that receive the full language as input.
What we have not covered is how to combine two such language features into a
language containing both.  To do so, we will use a type-level sum:

{% highlight coq %}
Delimit Scope Sum1_scope with Sum1.
Open Scope Sum1_scope.

Variant Sum1 (F G : Set -> Set) (A : Set) : Set :=
| inl1 : F A -> (F + G)%Sum1 A
| inr1 : G A -> (F + G)%Sum1 A
where
"F + G" := (Sum1 F G) : Sum1_scope.
Arguments inl1 {F G A}.
Arguments inr1 {F G A}.
{% endhighlight %}

Try and ignore the idiosyncracies of defining nice notations in Coq, and focus
on the definition of the variant `Sum1`.  It takes two extensible languages `F`
and `G`, and creates a new extensible language `F + G`.  To be an expression of
the language `F + G`, you can either be a `F` expression, stored in the `inl1`
constructor, or a `G` expression, stored in the `inr1` constructor.  Remember
that `A` will eventually be instantiated to be the full language, so you can
think of it as being itself `F + G` (or an even larger sum of features if we
were to nest additional language features).

We can now define a compound language, comprised of both `Boolean` and
`Natural`:

{% highlight coq %}
Inductive Natural (E : Set) : Set :=
| MkNatural (n : nat)
| Plus (m n : E)
.
Arguments MkNatural {E}.
Arguments Plus      {E}.

Definition BooleanAndNatural : Set -> Set
  := Boolean + Natural.
{% endhighlight %}

Let's put this to the test by instantiating our extensible term from the
previous section!  Remember, we need to provide two injections, one from
`Natural` into `BooleanAndNatural`, and one from `Boolean` into
`BooleanAndNatural`.  We could provide them as:

{% highlight coq %}
Global Instance BooleanAndNatural_supports_Boolean
  : BooleanAndNatural supports Boolean
  := {| inject := fun _ b => inl1 b; |}.
{% endhighlight %}

but notice that this does not actually depend on the concrete
`BooleanAndNatural` or `Boolean` types, just on the presence of the `inl1`
constructor.  Therefore, it is more clever to define two generic instances to
cover all possible combinations:

{% highlight coq %}
Global Instance Sum1_supports_Left F G
  : (F + G) supports F
  := {| inject := fun _ l => inl1 l; |}.

Global Instance Sum1_supports_Right F G
  : (F + G) supports G
  := {| inject := fun _ r => inr1 r; |}.
{% endhighlight %}

To convince ourselves that this indeed covers our needs, let's put it to the
test:

{% highlight coq %}
Goal BooleanAndNatural supports Boolean.
  typeclasses eauto.
Qed.

Goal BooleanAndNatural supports Natural.
  typeclasses eauto.
Qed.
{% endhighlight %}

Indeed, these two generic instances can provide injections from any language
feature into a larger language of which it is one summand.  And so, with all
we've seen so far, we can now define a concrete term, of type `Fix
BooleanAndNatural`, by instantiating the `extensibleTerm` from the previous
section:

{% highlight coq %}
Definition concreteTerm : Fix BooleanAndNatural
  := extensibleTerm.
{% endhighlight %}

If you would like to try this for yourself, [here is the accompanying
code](https://gist.github.com/Ptival/28dece5499112e44b071ddf1f2f6c610), tested
in Coq v8.9.

To be continued...
------------------

This post is getting quite long already, yet we just scratched the surface.  So
far, we have seen:

- that language features can be defined as extensible inductive types, whose
type is `Set -> Set`, taking for input the extended language that they are to be
part of,

- how to turn such an extensible inductive type into a concrete type via a `Fix`
operator,

- and how to define smart constructors, that inject any language feature
construct into any language that supports such feature.

Now here is a teaser of what remains to be seen:

- how to use the algebra in our `Fix` encoding to compute a whole class of
recursive functions over extensible data types,

- how this `Fix` encoding, however, is not up to the task of defining appopriate
semantics for interesting language features (like our if-then-else operation),

- how to define properties of extensible data types, and how to prove those
properties.
