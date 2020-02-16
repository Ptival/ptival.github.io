---
layout: post
title: "Deep dive into Meta-Theory à la Carte (part 2)"
date: 2020-02-15 14:08:00 +0100
permalink: deep-dive-meta-theory-carte-2
comments: true
categories:
---

NOTE: The code for this post is located
[here](https://gist.github.com/Ptival/24eeb5519ba703811a12d6905fd82072).

In the previous episode...
--------------------------

In the [previous episode](./deep-dive-meta-theory-carte-1), we saw how one can
define an extensible language feature as a functor parameterized by the
to-be-built language of type `Set`.  For instance, we defined the `Boolean`
language feature as:

{% highlight coq %}
Inductive Boolean (E : Set) : Set :=
| MkBoolean (b : bool)
| IfThenElse (condition thenBranch elseBranch : E)
.
{% endhighlight %}

(NOTE: I did not mention that those are functors then, because we have not
needed this fact yet.)

We saw that we can combine multiple such language features using a type-level
sum of functors: `Boolean + Natural` is a compound language made of the two
features `Boolean`, and `Natural`.

We also went through the trouble of defining a type-level fixed point operator,
allowing us to close and tie the know for a given extensible language, turning
it into a proper concrete language.  Our final candidate for this operator was:

{% highlight coq %}
Definition FAlgebra (F : Set -> Set) (A : Set) : Set :=
  F A -> A.

Definition Fix (F : Set -> Set) : Set :=
  forall (A : Set), FAlgebra F A -> A.

(* i.e.
  Fix F = forall (A : Set), (F A -> A) -> A
 *)
{% endhighlight %}

I am separating the definition of a `FAlgebra` from the definition of `Fix`,
unlike last time, because we will soon change the former.  Let's dissect what
this does some more.

F-algebras
----------

The type `Fix F` makes a strong claim: let's assume we have an expression `e` of
type `Fix F`.  For any type `A`, if you give `e` a function whose type is `F A
-> A`, `e` will return an `A`.  Surely `e` cannot be closed over a value of type
`F A`, since the client gets to choose whichever `A` they want!  Yet, `e` is
able to produce an `A`, when the only way to produce an `A` is to call this
function of type `F A -> A`.  Somehow, `e` is able to call this
function...  Let's recall how it does so.

In the previous post, we used this in a loopy way to build values of type `Fix
E`.  Remember how we defined smart constructors:

{% highlight coq %}
Definition boolean
           {E : Set -> Set}
           `{E supports Boolean}
           (b : Boolean)
  : Fix E (* i.e. forall (A : Set), (E A -> A) -> A *)
  := fun A wrap => wrap (inject (MkBoolean b)).
{% endhighlight %}

A-ha! Because `MkBoolean` does not contain any value of the type it is
parameterized with, it can inhabit `Boolean X` for any `X`, in particular, it
can pretend to be a `Boolean A` for our `wrap` function .  Here we then inject
the result of `MkBoolean` into `E` via `inject`, giving us a value of type `E
A`, which `wrap` is happy to fold into our output of type `A`.

{% highlight coq %}
Definition ifThenElse
           {E : Set -> Set}
           `{E supports Boolean}
           (c t e : Fix E)
  : Fix E
  := fun A wrap => wrap (inject (IfThenElse (c _ wrap) (t _ wrap) (e _ wrap))).
{% endhighlight %}

In `ifThenElse`, the situation is more complicated since the three arguments to
`IfThenElse` are three values of type `Fix E`, but we can fold them into values
of type `A` by using the very same function `wrap`, after which we have
`IfThenElse (c _ wrap) (t _ wrap) (e _ wrap)`, a value of type `Boolean A`,
ready to be injected and wrapped itself!

I was being intentionally misleading by calling the argument `wrap` in the
previous blog post, since there we were using it to wrap values of type `E (Fix
E)` into values of type `Fix E`.  But remember that `Fix E` stands for values
that can be folded into any resulting type `A`: what is going on in `ifThenElse`
is much more powerful than simply creating expressions!  To convince yourself,
let me demonstrate.

Remember, if a value has type `Fix E`, it has type `forall (A : Set), (F A -> A)
-> A`.  Let's plug in `Boolean` for `E`, and `(nat * nat)` for `A`.  Assume I
have a value `someTerm : Fix Boolean`, it follows that `someTerm (nat * nat)`
has type `(Boolean (nat * nat) -> (nat * nat)) -> (nat * nat)`.

```
someTerm             : Fix Boolean
   (* unfold Fix and FAlgebra *)
someTerm             : forall (A : Set), (Boolean      A      ->      A     ) ->      A
   (* instantiate A into (nat * nat) *)
someTerm (nat * nat) :                   (Boolean (nat * nat) -> (nat * nat)) -> (nat * nat)
```

Let us build a function to pass here as input:

{% highlight coq %}
Definition countFalsesAndTrues (b : Boolean (nat * nat)) : (nat * nat) :=
  match b with
  | MkBoolean false                        => (1, 0)
  | MkBoolean true                         => (0, 1)
  | IfThenElse (cf, ct) (tf, tt') (ef, et) => (cf + tf + ef, ct + tt' + et)
  end.
{% endhighlight %}

This function takes as input a `Boolean` extensible expression whose recursive
occurrences contain values of type `(nat * nat)`.  It tries and counts the
occurrences of the constant `false` and `true` respectively:

- when the expression is `false`, that's 1 `false` and 0 `true`,
- when the expression is `true`, that's 0 `false` and 1 `true`,
- when the expression is `if ... then ... else ...`, let's assume (for now, we
  will get to this) that each sub-expression has been replaced with its two
  counts, we can return the sum of the appropriate pairing of counts.

Lo and behold:

{% highlight coq %}
Definition someTerm : Fix Boolean :=
  ifThenElse (boolean true)
             (ifThenElse (boolean true) (boolean true) (boolean false))
             (boolean false).

Compute (someTerm (nat * nat)%type countFalsesAndTrues).
(*
  = (2, 3)
  : nat * nat
*)
{% endhighlight %}

Indeed there are 2 `false`s and 3 `true`s in `someTerm`!  `countFalsesAndTrues`
is what is called a **F-algebra** for the `Boolean` functor, and
`ifThenElse`/`boolean` are effectively defining a fold with this algebra.  Let
us look at the definition of `ifThenElse` with this new perspective:

{% highlight coq %}
fun _ wrap => wrap (inject (IfThenElse (c _ wrap) (t _ wrap) (e _ wrap))).
{% endhighlight %}

In fact, let's rename this `wrap` into `alg` now that we think of it in more
operational terms:

{% highlight coq %}
fun _ alg => alg (inject (IfThenElse (c _ alg) (t _ alg) (e _ alg))).
{% endhighlight %}

As you can see, `ifThenElse` first recursively folds its three arguments, `c`,
`t`, and `e`, with the algebra `alg`.  Then, it runs `alg` on `IfThenElse c' t'
e'`, where `c'` is the result of folding `c`, and respectively for `t'` and
`e'`.  This explains why, in the definition of the `countFalsesAndTrues`
algebra, I said we could assume that the `IfThenElse` constructor contained the
recursive results!  (NOTE: because we are not using a compound language,
`inject` here goes from `Boolean` to `Boolean` and is an identity.)

If this does not make sense, I encourage you to read the excellent series of
blog posts on recursion schemes
[here](https://blog.sumtypeofway.com/posts/introduction-to-recursion-schemes.html),
and then come back to this post with your algebraically-opened eyes!

F-algebras are too greedy
-------------------------

Great, our extensible terms are folds for whatever F-algebras we throw at them.
Let's assume that we have an evaluation algebra for a complex language.  Think
about what happens when I evaluate:

```
if true then 42 else expensiveComputation
```

or:

```
(fix rec n => if n = 0 then 1 else n * rec (n - 1)) 3
```

In both cases, our `ifThenElse` extensible term will receive its three
arguments, run the evaluation algebra on all three, and then, ... Wait a second,
even though the branch taken is `true`, our extensible term is evaluating
`expensiveComputation`!  Even worse, in the second case, evaluating the
expression will require evaluating `rec 2`, which will want to evaluate `rec 1`,
which will want to evaluate `rec 0`, which, even though the branch taken will be
the true branch, will still go and evaluate `rec (-1)`, and `rec (-2)`, and...
This will never terminate!

Mendler algebras
----------------

F-algebras have this problem: because all they ask of their client is a function
to combine the recursive results, there is no way to stage the recursive
computations and delay or ignore some of them.  In order to allow for this
fine-tuning, we must give a means for the client to describe the order of
evaluation.  This can be done with the following modified algebra signature:

{% highlight coq %}
Definition MendlerAlgebra (F : Set -> Set) (A : Set) : Set :=
  forall (R : Set), (R -> A) -> F R -> A.

(* And [Fix] can be re-defined as: *)
Definition Fix (F : Set -> Set) : Set :=
  forall (A : Set), MendlerAlgebra F A -> A.
{% endhighlight %}

Whereas the client used to be given a copy of `F A`, containing concrete results
of the recursive calls, they are now given a copy of `F R` for an abstracted
`R`.  They cannot possibly interact with the `R`s they may find in there, except
by applying the function of type `R -> A` we provide them with.  Indeed, this
function is how they will indicate that they would like to perform a recursive
call, after which we gladly give them the result of type `A`.

Do notice that this is a generalization of `FAlgebra`: if you pass in `A` for
`R`, and the identity function, to a Mendler algebra, it boils down to a
F-algebra.

Let's see how this updated definition affects our smart constructors:

{% highlight coq %}
Definition ifThenElse
           {E : Set -> Set}
           `{E supports Boolean}
           (c t e : Fix E)
  : Fix E
  := fun A malg =>
       malg (Fix E) (fun e => e A malg) (inject (IfThenElse c t e)).
{% endhighlight %}

It's almost the same, except that we must instantiate `R` and the function `R ->
A`.  Because we are allowed to pick any `R`, we choose `R` to be `Fix E`, the
type of expressions from our language: indeed, they will remain unevaluated
until they reach the "recursive call" function, of abstract type `R -> A`, which
in our case will therefore be `Fix E -> A`.

Said function receives the term `e`, still unevaluated, and only then passes
`malg` to it, so that it may start evaluating.  Importantly, the type `Fix E`
contains a universal quantification on all `Set`, so the code shown here needs
impredicative `Set` to work.  You can add the line `-arg -impredicative-set` in
your `_CoqProject`, or use local environment variables, or find some other
solution on your own.

The attached code contains some tests to try and show how this indeed makes it
so that the recursive calls are only performed when needed (though Coq's caching
mechanism sometimes gets in the way of testing this safely).

(NOTE: I initially had the wrong code here, passing `malg` directly to `c`, `t`,
and `e`, which made them start evaluating.  It should not be corrected in the
post and the attached code.  Props to /u/Syrak for noticing!)

Compound algebras for compound languages
----------------------------------------

Let us now add some more machinery, so that we can define functions of compound
languages by parts.  That is, given two language features, say `Boolean` and
`Natural`, I'd like to define some function of type `Fix (Boolean + Natural) ->
ResultType`, not monolithically, but rather, by defining its two components of
type `Boolean ResultType -> ResultType` and `Natural ResultType -> ResultType`,
and by combining those together.

To capture what we want to do, it will help to define a type class for such
program algebras.  Because the type class resolution is type-driven, and because
we may want to define multiple functions with the same type signature, we will
help the type class mechanism by annotating every program algebra component with
tag, describing what operation it is a component of.  The `ProgramAlgebra` type
class will therefore be:

{% highlight coq %}
Class ProgramAlgebra (Tag : Set) F A :=
  {
    programAlgebra : forall (R : Set), (R -> A) -> F R -> A;
  }.
{% endhighlight %}

Nothing new here, the class `ProgramAlgebra Tag F A` contains a Mendler Algebra
for functor `F`, returning results of type `A`, and tagged for the operation
indicated with `Tag`.  Let's look at an instance right away, for an evaluation
algebra.  Because we will evaluate a language with `Boolean` and `Natural`, the
values we can obtain as a result of evaluation will either be a boolean, a
natural, or an error (say if someone tried to add a number to a boolean).  While
in general, the output type can also be extensible, we will set it in stone here:

{% highlight coq %}
Inductive EvalResult :=
| ValueBoolean (b : bool)
| ValueNatural (n : nat)
| Stuck
.
{% endhighlight %}

And here is the component of evaluation at the `Boolean` feature:

{% highlight coq %}
Variant ForEval := . (* tag for all program algebras of [Eval] *)

Global Instance Eval__Boolean
  : ProgramAlgebra ForEval Boolean EvalResult
  :=
    {|
      programAlgebra :=
        fun _ rec b =>
          match b with
          | MkBoolean b      => ValueBoolean b
          | IfThenElse c t e =>
            match rec c with
            | ValueBoolean b   => if b then rec t else rec e
            | _                => Stuck
            end
          end
    |}.
{% endhighlight %}

A boolean expression evaluates to a boolean value.  An if-then-else expression
requires recursive, properly delayed evaluation.  If the condition does not
evaluate to a boolean, we're stuck.  Note that because we don't have a type
system yet, we happily evaluate ill-typed terms like `if true then 2 else
false`.

Recalling our `Natural` feature from the previous blog post, we can also define
the component of the evaluation algebra at it:

{% highlight coq %}
Global Instance Eval__Natural
  : ProgramAlgebra ForEval Natural EvalResult
  :=
    {|
      programAlgebra :=
        fun _ rec n =>
          match n with
          | MkNatural n => ValueNatural n
          | Plus a b    =>
            match (rec a, rec b) with
            | (ValueNatural a, ValueNatural b) => ValueNatural (a + b)
            | _                                => Stuck
            end
          end
    |}.
{% endhighlight %}

And recalling how we built compound languages out of the type-level sum of the
features, we will now describe how to build compound program algebras:

{% highlight coq %}
Global Instance ProgramAlgebra__Sum1
       (Tag : Set) (F G : Set -> Set)
       (A : Set)
       `{ProgramAlgebra Tag F A}
       `{ProgramAlgebra Tag G A}
  : ProgramAlgebra Tag (F + G) A
  :=
    {
      programAlgebra :=
        fun _ rec s =>
          match s with
          | inl1 l => programAlgebra _ rec l
          | inr1 r => programAlgebra _ rec r
          end
    }.
{% endhighlight %}

Given two features `F` and `G`, and their respective `A`-producing program
algebra for a given `Tag`, we can build a program algebra for the compound
language `F + G`.  It suffices to dispatch to the appropriate program algebra.
With this, we can define an `eval` function for `Boolean + Natural` simply as:

{% highlight coq %}
Definition eval
           (e : Fix (Boolean + Natural))
  : EvalResult
  := e _ (programAlgebra (Tag := ForEval)).
{% endhighlight %}

Note that `programAlgebra` in this definition is overloaded.  The type class
mechanism is looking for a `ProgramAlgebra` with tag `ForEval` and language
`Boolean + Natural`.  It uses `ProgramAlgebra__Sum1` to build such a program
algebra out of the two components we defined earlier.  Here, we don't **have**
to pass in the `ForEval` tag, because there is no ambiguity, but in general,
it's good to put it, so that we don't accidentally run another algebra with
identical type to the one we are targetting.

Finally, we can demonstrate that indeed evaluation is now working, jumping
between evaluation of `Boolean` and evaluation of `Natural` as needed:

{% highlight coq %}
Compute (
    eval
      (plus
         (ifThenElse (boolean false) (natural 22) (natural 41))
         (natural 1)
      )
  ).

(**
  = ValueNatural 42
  : EvalResult
 *)
{% endhighlight %}

To be continued...
------------------

We now have the means of building programs by components over our extensible
language features, and combining them into programs for larger languages.

Of course, the fun really begins when we want and reason about such extensible
programs.  But that's for another post!
