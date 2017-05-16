---
layout: post
title: "Parser generators and function application"
date: 2017-05-15 23:00:00 -0700
comments: true
categories:
---

**TLDR**: If you want to parse function application `f a b` correctly,
you need to, counter-intuitively, give some precedence to tokens such
as `LPAREN`, `VAR`, `NUM`, `LAMBDA`, etc.

I promised this
post [two posts ago](/2017/02/25/modular-parser-combinators), but it's
this time of the year where our students need it, so here comes!

The rest of this post is somewhat generic in what parser generator in
the `yacc` family you use, for instance, OCaml's `ocamlyacc` and
Haskell's `happy`.

As I mentioned in the earlier post, there are two ways to deal with
precedence when building parser generators.  I called them the
"stratified grammar" and the "parser directives" approaches.

When showing toy programs, both methods work pretty well.  But in my
opinion, the "parser directives" approach is much better, as it keeps
the grammar easy to read and separates the concerns of precedence and
associativity.  But when comes the time to implement a language with
token-less function application, things become weird:

{% highlight ocaml %}
expr:
  | VAR       { ... }
  | expr expr { ... }
{% endhighlight %}

This will parse `a b c` as `a (b c)`, contrary to the wanted `(a b)
c`.  Now if you try to find a solution to this online, you might
find
[people discouraging you from using the "parser directives" approach](http://stackoverflow.com/a/27631191/553003),
or
[wrong answers to beginners](http://ocaml_beginners.yahoogroups.narkive.com/kA4IYGjU/parser-for-a-simple-formula-left-associative#post4),
or
[non-solutions](https://github.com/danielmoore/Lambda-Calculator/blob/master/NorthHorizon.LambdaCalculator.Languages.SystemF/Parsing.fsp).

Most answers usually tell you to add a ghost `%token APP`, and to add
`%prec APP` to the production `expr expr`.  Often, they will suggest
to add a `%left APP` line to the precedence list, which is useless by
itself, and also misleading.  This is all on the right way to the
correct solution, but not enough.

The correct solution
--------------------

Unfortunately, to find the correct solution, I had to read
the
[documentation](https://caml.inria.fr/pub/docs/manual-ocaml/lexyacc.html) carefully,
and understand some low-level details of the implementation.

If you do so, you will learn that shift-reduce conflicts are resolved
by comparing the declared precedence of the token to be shifted with
the declared precedence of the production rule to be reduced.  It is
not really mentioned in the documentation, but in the absence of
declaring a token's precedence, they will have maximum precedence.
You will also learn that a rule's precedence is that of its rightmost
non-terminal.

Therefore when presented with the shift-reduce conflict:

{% highlight ocaml %}
expr expr . VAR
{% endhighlight %}

The parser will compare the declared precedence of token `VAR` with
the declared precedence of the application rule, which the `%prec APP`
phrase lets you override to be that of the ghost token `APP`.

So if you never declared a precedence for `VAR` or made it higher than
that of `APP`, the parser will **not** do what you want.

So the correct solution is the following:

{% highlight ocaml %}
%token APP LPAREN RPAREN VAR

%nonassoc VAR LPAREN /* list ALL other tokens that start an expr */
%nonassoc APP
/* /!\ if you write %left APP, it will NOT make the rule left-associative */

expr:
  | VAR                          { ... }
  | LPAREN expr RPAREN           { ... }
  | expr expr          %prec APP { ... }
{% endhighlight %}

It is pointless to write `%left APP` (instead of `%nonassoc APP`), as
the `left` is only used to resolve a conflict between a token (or set
of tokens at the same precedence level) and itself (themselves), as
in:

{% highlight ocaml %}
expr PLUS expr . PLUS VAR
{% endhighlight %}

where the `PLUS` token is in shift-reduce conflict with itself, in
which case `%left` means "reduce" and `%right` means "shift".  But we
know there will NEVER be a conflict like:

{% highlight ocaml %}
expr APP expr . APP VAR
{% endhighlight %}

since `APP` is a ghost token! So `%nonassoc APP` is enough, and will
not mislead people into thinking that this annotation decides the
associativity of the function application rule.

Now, the reason why you have to list all the other tokens, is that
there will be one shift-reduce conflict per token appearing at the
start of an `expr`.  For instance, if you only have the partial
solution:

{% highlight ocaml %}
%token APP LPAREN RPAREN VAR

%nonassoc APP
%nonassoc VAR

expr:
  | VAR                          { ... }
  | LPAREN expr RPAREN           { ... }
  | expr expr          %prec APP { ... }
{% endhighlight %}

Then `a b c` will **correctly** parse to `(a b) c`, but `a b (c d)`
will **incorrectly** parse to `a (b (c d))`, because in the following
shift-reduce conflict:

{% highlight ocaml %}
expr expr . LPAREN VAR VAR RPAREN
{% endhighlight %}

the parser had to choose between the precedence of the application
rule `APP`, and the precedence of the incoming token `LPAREN`.  Since
you never declared it, it had higher precedence.

That's it for parsing function application!

**EDIT:** To be clear, you might also have tokens that need to be at
higher precedence than `APP`.  For instance, if you want `f a -> b` to
parse as `(f a) -> b` rather than `f (a -> b)`, you will want:

{% highlight ocaml %}
%nonassoc LPAREN VAR /* etc. */
%nonassoc APP
%left ARROW
{% endhighlight %}

Those tokens should not be valid start tokens for an expression.

One caveat of the "parser directives" approach
----------------------------------------------

Even though I advocate strongly for the "parser directives" approach,
it still has one issue that prevents us from being as modular as we'd
hope.  Consider the following:

{% highlight ocaml %}
expr:
  | expr PLUS  expr { Binop(Plus,  $1, $3) }
  | expr MINUS expr { Binop(Minus, $1, $3) }
  | expr TIMES expr { Binop(Times, $1, $3) }
  | expr DIV   expr { Binop(Div,   $1, $3) }
{% endhighlight %}

A functional programmer would see this repetition, and want to
abstract this away into a new non-terminal:

{% highlight ocaml %}
expr:
  | expr binop expr { Binop($2, $1, $3) }

binop:
  | PLUS  { Plus  }
  | MINUS { Minus }
  | TIMES { Times }
  | DIV   { Div   }
{% endhighlight %}

This looks really cool! Unfortunately, this breaks our parser.  The
reason is that, earlier, each rule had its own precedence, determined
by its rightmost terminal (`PLUS` for the plus rule, etc.).  But now,
our general `binop` production only contains non-terminals.  So the
parser has no way to distinguish `PLUS` from `TIMES` at this level of
abstraction, and will therefore do the same thing on such shift-reduce
conflicts as:

{% highlight ocaml %}
expr binop expr . PLUS expr
expr binop expr . TIMES expr
{% endhighlight %}

But it should decide differently depending on what the `binop` was!

The only solution I can think of to mitigate this is to stop halfway
through this refactoring:

{% highlight ocaml %}
%nonassoc PLUS MINUS
%nonassoc PLUSMINUS
%nonassoc TIMES DIV
%nonassoc TIMESDIV

expr:
  | expr plusminus expr %prec PLUSMINUS { Binop($2, $1, $3) }
  | expr timesdiv  expr %prec TIMESDIV  { Binop($2, $1, $3) }

plusminus:
  | PLUS  { Plus  }
  | MINUS { Minus }

timesdiv:
  | TIMES { Times }
  | DIV   { Div   }
{% endhighlight %}

Now our shift-reduce conflicts look like:

{% highlight ocaml %}
expr plusminus expr . PLUS expr
expr plusminus expr . TIMES expr
{% endhighlight %}

In the first case, the `plusminus` rule has precedence `PLUSMINUS`,
which is higher than that of `PLUS`, so the parser correctly reduces
(ensuring left-associativity of addition and subtraction).

In the second case, the `plusminus` rule (still) has precedence
`PLUSMINUS`, but it is lower than that of `TIMES`, ensuring the
precedence of multiplication over addition and subtraction.

But honestly, this halfway refactoring makes the grammar look more
complicated that the redundant original one, so I don't think it's
really worth it.

That's all for today!
