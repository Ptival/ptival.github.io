---
layout: post
title: "Modular parser combinators"
date: 2017-02-24 18:29:00 -0700
comments: true
categories:
---

When students learn about parser generators, they are often told that associativity and precedence issues can be solved in one of two ways.

The "stratified grammar" approach
---------------------------------

{% highlight haskell %}

expr:
  | plusminus { ... }

plusminus:
  | plusminus PLUS  timesdiv { ... }
  | plusminus MINUS timesdiv { ... }
  | timesdiv                 { ... }

timesdiv:
  | timesdiv TIMES atom { ... }
  | timesdiv DIV   atom { ... }
  | atom                { ... }

atom:
  | VAR                { ... }
  | NUM                { ... }
  | LPAREN expr RPAREN { ... }

{% endhighlight %}

In the stratified grammar approach, one tediously stratifies their grammar by creating a non-terminal per precedence level.

The stratification handles precedence by forcing operators binding less tightly to recognize the outermost structure of the input, before tighter operators get to split the smaller parts of the expression.  For instance here, an expression is split at the outermost `plusminus` level, according to its `PLUS`s and `MINUS`s.  Then, each operand of those is split into products and divisions according to the non-terminal `timesdiv`.

Associativity is handled by imbalancing each rule: a left-associative binary operator would try to parse something at its level for its left operand, while it would try to parse something at the next level for its right operand.  Symmetrically for a right-associative binary operator.  A non-associative binary operator would parse something at the next level for both its operands.

The "parser directives" approach
--------------------------------

{% highlight haskell %}

%left PLUS MINUS
%left TIMES DIV

expr:
  | expr PLUS  expr    { ... }
  | expr MINUS expr    { ... }
  | expr TIMES expr    { ... }
  | expr DIV   expr    { ... }
  | VAR                { ... }
  | NUM                { ... }
  | LPAREN expr RPAREN { ... }

{% endhighlight %}

The keyword `%left` indicates that the binary operators are left-associative.  Tokens mentioned on the same line have the same precedence (for instance, `PLUS` and `MINUS`), while tokens on different lines have different precedence (for instance, `TIMES` has higher precedence than `PLUS`).

Modularity 101
--------------

I have always found the stratified grammar approach inelegant:

- the actual grammar of the language is scattered around,

- switching the precedence or associativity of two operators forces multiple non-local rewrites,

- so does introducing a new operator at a different level.

Contrast the directives approach, where:

- the actual grammar is as readable as it gets,

- switching associativity is a keyword away and switching precedences a line switch away,

- introducing a new operator is a simple as finding the proper precedence line in which to declare it, and adding a line for it in the grammar wherever we see fit.

Unfortunately, the "parser directives" approach comes with a couple caveats as soon as one introduces a token-less function application, and coming up with a solution for it requires reading the documentation of the parser generator, and understanding the solution basically requires understanding the algorithm running behind the scenes (my next post will be exactly on this subject).

Therefore, when we teach parser generators to our students, many of them end up choosing the "stratified approach", to my great dismay, while the ones who choose my preferred approach struggle for hours trying to get function application to associate correctly.

On to parser combinators
------------------------

Unfortunately, parser generators don't seem very helpful when one wants to write extensible parsers.  By "extensible", I mean the kind of parser that languages like Haskell, Coq, Agda use, wherein a user may define new operators, that the compiler is subsequently expected to parse appropriately.

For this, one often turns to parser combinator libraries, which provide ways to build parsers as functions of the host language (here we will use Haskell).  They then google "parsec tutorial" or "parsec lambda calculus" or one such query, and find a trove of simple examples.  Unfortunately, most examples are too simple to actually demonstrate the intricacies of parsing a complex language.  They will often:

- explain that one can deal with function application by creating a parser for "terms that are not applications":

{% highlight haskell %}

nonApp :: Parser Term
nonApp = var <|> abs term <|> parens term

term = chainl1 nonApp $ space *> App

{% endhighlight %}

- explain that one can deal with binary operators using a library function and an operator table (for instance, [Text.MegaParsec.Expr](https://hackage.haskell.org/package/megaparsec-5.2.0/docs/Text-Megaparsec-Expr.html)):

{% highlight haskell %}

table =
  [ [ binary  "*"  (*)
    , binary  "/"  div
    ]
  , [ binary  "+"  (+)
    , binary  "-"  (-)
    ]
  ]

{% endhighlight %}

Now, I was trying to build the following dependently-typed language:

{% highlight haskell %}

data Term
  = Annot Term Term      -- x : τ
  | App   Term Term      -- f x
  | Lam   Name Term      -- λ x . t
  | Let   Name Term Term -- let x = t1 in t2
  | Pi    Name Term Term -- (x : τ1) → τ2
  | Var   Name           -- x

{% endhighlight %}

and I wanted to introduce the notation `τ1 → τ2`, standing for `Pi "" τ1 τ2`, where the empty string indicates the non-binding.  I considered putting it in an operator table with right-associativity, and I ended up with something like:

{% highlight haskell %}

operators =
  [ [ InfixL (App   <$ symbol "")  ]
  , [ InfixR (Pi "" <$ symbol "→") ]
  , [ InfixN (Annot <$ symbol ":") ]
  ]

{% endhighlight %}

But I should also be able to parse binding `Pi`s (i.e. `(x : τ1) → τ2`), at the same precedence as the non-binding variant.  But it's not quite a binary operator (here, my syntax almost makes it look like one, but if you wanted to use `Π` or `∀` it would become problematic).  So you'd want to remove `→` from your operator table, but then you'd need to either remove everything before it or after it and to manually order parsers for those operators somewhere else.

---

Somewhere else, the parts of your parser dealing with `λ` and `let` might look like:

{% highlight haskell %}

lambdaletP :: Parser Term
lambdaletP = choice [lambdaP, letP, whateverComesNextP]

letP :: Parser Term
letP = do
  try $ do
    rword "let"
  n <- nameP
  rword "="
  t1 <- termP
  rword "in"
  t2 <- lambdaletP
  return $ Let n t1 t2

lambdaP :: Parser Term
lambdaP = do
  try $ do
    rword "λ"
  n <- nameP
  rword "."
  t <- lambdaletP
  return $ Lam n t

{% endhighlight %}

(Note: we try to follow the discipline demonstrated in ["try a <\|> b" considered harmful](http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/).)

We need to introduce `lambdaletP` to be able to recognize `let x = 1 in λ y . 2` or `λ x . let y = 1 in 2` without adding parentheses.  Can you see how similar to our "stratified grammar" approach this looks?  We have to create extra parsers per precedence level, and inner parsers refer to their "level parser" explicitly.  This code suffers from the very same issues as the stratified parser generator grammar: switching precedences or introducing new levels will require tedious editing and reordering, and the structure of the parser is lost in the code.

A more modular approach
-----------------------

If we take a step back, we can see that our issues arise from our parsers needing to call:

- the parser at their own precedence level,

- and the parser at the next precedence level.

Abstracting away the latter is easy: we can take it as input, and our caller will have to tell us who's next.

Abstracting away the former might seem hard: if our parser explicitly calls itself recursively, it prevents other parsers from existing at its own level.  So we would like to receive a parser for the things at our level as input, but we would like to be part of this parser too!

There is a classic trick to achieve this, called explicit open recursion: our parser will pass itself as input to its components!  Let's see how this works on a simple example, making `letP` and `lambdaP` receive `letlambdaP` as an input (they call it `selfP`):

{% highlight haskell %}

letP :: Parser Term -> Parser Term
letP selfP = do ... t <- selfP ...

lambdaP :: Parser Term -> Parser Term
lambdaP selfP = do ... t <- selfP ...

{% endhighlight %}

Now we can define:

{% highlight haskell %}

lambdaletP :: Parser Term
lambdaletP = choice [lambdaP lambdaletP, letP lambdaletP, whateverComesNextP]

{% endhighlight %}

Therefore, to define parsers that are modular in what exists at their precedence level and what exists at their next precedence level, we adopt the discipline of parameterizing our parsers by two parsers:

{% highlight haskell %}

type ModularParser a =
  Parser a ->             -- "self"-precedence parser
  Parser a ->             -- "next"-precedence parser
  Parser a

{% endhighlight %}

From now on, a parser should (in general) not call itself recursively, but rather use the parser received as first argument.  Similarly, it should not call the parser for the next precedence construct, but rather use the parser received as second argument.  This is best demonstrated by the parser for the syntactic construct `τ1 → τ2`:

{% highlight haskell %}

arrowP :: ModularParser Term
arrowP selfP nextP = do
  τ1 <- try $ do
    τ1 <- nextP
    symbol "→"
    return τ1
  τ2 <- selfP
  return $ Pi "" τ1 τ2

{% endhighlight %}

The `→` operator is right-associative.  This means, `τ1 → τ2 → τ3` is to be parsed as `τ1 → (τ2 → τ3)`, and **not** as `(τ1 → τ2) → τ3`.  To achieve this, one must make sure not to allow parsing "naked" arrows on the left, by only parsing things at the next precedence level.  This is why we call `nextP` before the call to `symbol`.  However, we want to allow parsing "naked" arrows on the right side, for instance `τ2 → τ3` in our example.  So, we call `selfP` to achieve this.  We don't want to call `arrowP` recursively here, because we might later want to have other parsers at the same level.  It is in fact the case here, since the parser for the binding arrow will be at this level, allowing us to parse `τ1 → (x : τ2) → τ3 → τ4`.

Note that modular parsers can call both parsers received as input, but may also call only one of them, or neither, as illustrated in the following examples.  For instance, a non-associative binary operator will only call `nextP`:

{% highlight haskell %}

annotP :: ModularParser Term
annotP _selfP nextP = do
  t <- try $ do
    t <- nextP
    symbol ":"
    return t
  τ <- nextP
  return $ Annot t τ

{% endhighlight %}

Constructs that are allowed to appear without parentheses within themselves will only call `selfP`, for instance `let x = 1 in let y = 2 in 3`:

{% highlight haskell %}

letP :: ModularParser Term
letP selfP _nextP = do
  try $ do
    rword "let"
  n <- nameP
  symbol "="
  t1 <- termP
  rword "in"
  t2 <- selfP
  return $ Let n t1 t2

{% endhighlight %}

And parsers for atoms will not call either:

{% highlight haskell %}

atomP :: Parser a -> ModularParser a
atomP p _selfP _nextP = p

varP :: Parser Term
varP = Var <$> identifier

{% endhighlight %}

Now, for our tour de force, we will combine all those parsers into a parser for the full language.  A language will be defined by a list of list of modular parsers, where rows are precedence levels:

{% highlight haskell %}

parserTable :: [[ModularParser Term]]
parserTable =
  -- low precedence
  [ [letP, lambdaP]
  , [annotP]
  , [piP, arrowP]
  , [appP]
  , [atomP varP]
  ]
  -- high precedence

{% endhighlight %}

Each row should be turned in a parser for the given precedence level, which tries all the options on the row, or falls back to the next row:

{% highlight haskell %}

choiceOrNextP :: [ModularParser a] -> Parser a -> Parser a
choiceOrNextP ps nextP =
  fix $ \ selfP -> choice $ map (\ p -> p selfP nextP) ps ++ [nextP]

-- If you're unsure about fix, this is the same as:
choiceOrNextP ps nextP =
  choice $ map (\ p -> p (choiceOrNextP ps nextP) nextP) ps ++ [nextP]
--                       ^^^^^^^^^^^^^^^^^^^^^^^^ this is ourself!
{% endhighlight %}

Given a row `ps`, and a handle on the next precedence parser `nextP`, we want to choose among all `ModularParser`s.  But remember that they need to receive the parser for the current precedence level as their first input, that is, the parser we are currently in the process of building.  Thanks to the open recursion trick and the fixpoint operator, we can obtain a handle to the very parser we are building as `selfP`, and pass it to each modular parser `p` as their first argument.  `nextP` is simply passed along too.  Note that we also append `nextP` to our list of choices, thus defaulting to the next row when all else fails.

We should now be able to fold the entire table by:

- applying `choiceOrNextP` on each row, transforming our table into a list `[\nextP -> firstRow, \nextP -> secondRow, \nextP -> thirdRow, ...]`,

- then chaining all these parsers together,

- and making sure that the final parser is allowed to call the first parser, as long as it's done between parentheses.

We write a function `foldP` to do so:

{% highlight haskell %}

foldP :: [[ModularParser a]] -> Parser a
foldP ps = fix $ \ selfP -> foldr ($) (parens selfP) (map choiceOrNextP ps)

-- If you're still confused about `fix`, this is the same as:
foldP ps = foldr ($) (parens (foldP ps)) (map choiceOrNextP ps)

{% endhighlight %}

Symbolically unfolding `foldr`, we can see that we are building the expression:

{% highlight haskell %}

fix $ \selfP -> firstRow (secondRow (thirdRow (... (lastRow (parens selfP)))))
--              ^^^^^^^^ try the parsers in the first row

--                        ^^^^^^^^^ else/next try the parsers in the second row

--                                   ^^^^^^^^ else/next try the parsers in the third row

--                                                           ^^^^^^^^^^^^
--      else/next try to parse parentheses and start again from first row

{% endhighlight %}

And that's it, we can now build our parser:

{% highlight haskell %}

termP :: Parser Term
termP = foldP parserTable

{% endhighlight %}

All you need to do to change the precedence of operators is reorder lines in `parserTable`.  All you need to do to introduce a new precedence level is create a new line in the table.  The overall structure of the language is immediately readable from the `parserTable`.

One step further
----------------

It's still not simple to recognize what productions are binary operators, and to change their associativity.  We had to make this decision within `arrowP` by plugging `selfP` and `nextP` according to our intent.  We can lift this decision into the parser table by creating three operators for left-, right-, and non-associative binary operators:

{% highlight haskell %}

-- These type aliases will come in handy
type Parser1 a = Parser a -> Parser  a
type Parser2 a = Parser a -> Parser1 a
-- For now, Parser2 is the same as ModularParser

-- The `String` is the operator, for instance ":", "→"
-- The `a -> a -> a` is the constructor to use for this operator
binOpLP, binOpRP, binOpNP :: String -> (a -> a -> a) -> Parser2 a

binOpLP s k _selfP nextP = chainl1 nextP (symbol s *> return k)

binOpRP s k selfP nextP = do
  l <- try $ do
    l <- nextP
    symbol s
    return l
  r <- selfP
  return $ k l r

binOpNP s k _selfP nextP = binOpRP s k nextP nextP

{% endhighlight %}

`binOpRP` is the easiest to start with: it attemps to parse something at the next level for the left operand, then to parse the infix symbol, after which it can commit and parse the right operand.  It calls the output constructor with `l` and `r` (for instance, `Pi "" l r`).

`binOpLP` would look like `binOpRP`, where the `l` line would read `l <- selfP` and the `r` line would read `r <- nextP`.  However, this would result in a infinite loop of calls to `selfP`.  The usual trick is to use `chainl1` instead.

`binOpNP` would look like `binOpRP`, where the `l` line would read `l <- nextP` and the `r` line would remain unchanged.  I cheat here by reusing the existing code of `binOpRP`, plugging in `nextP` for both arguments.

We can finally rewrite our parser table as:

{% highlight haskell %}

parserTable :: [[ModularParser Term]]
parserTable =
  -- low precedence
  [ [letP, lambdaP]
  , [binOpNP ":" Annot]
  , [piP, binOpRP "→" (Pi "")]
  , [binOpLP "" App]
  , [atomP varP]
  ]
  -- high precedence

{% endhighlight %}

We can even package this all up into a neat data type:

{% highlight haskell %}

data Associativity = LeftAssociative | RightAssociative | NonAssociative

-- From now no, `ModularParser` will refer to this data type,
-- and `Parser2` will be used to talk about the old parameterized parser
data ModularParser a
  = SelfNextParser (Parser2 a)
  | BinaryOpParser Associativity String (a -> a -> a)
  | AtomParser (Parser a)
  -- etc.

{% endhighlight %}

It is then easy to define a function:

{% highlight haskell %}

unModularP :: ModularParser a -> Parser2 a
unModularP (SelfNextParser p) = p
unModularP (BinaryOpParser LeftAssociative  s p) = binOpL s p
unModularP (BinaryOpParser RightAssociative s p) = binOpR s p
unModularP (BinaryOpParser NonAssociative   s p) = binOpN s p
unModularP (AtomParser p) = \ _selfP _nextP -> p

{% endhighlight %}

and to update `choiceOrNextP`:

{% highlight haskell %}

choiceOrNextP :: [ModularParser a] -> Parser1 a
choiceOrNextP ps nextP =
  fix $ \ selfP -> choice $ map (\ p -> unmodularP p selfP nextP) ps ++ [nextP]
--                                      ^^^^^^^^^^
--                                      added this

{% endhighlight %}

so that we can finally write our parser table as:

{% highlight haskell %}

binOpL, binOpR, binOpN :: String -> (a -> a -> a) -> ModularParser a
binOpL = BinaryOpParser LeftAssociative
binOpR = BinaryOpParser RightAssociative
binOpN = BinaryOpParser NonAssociative

parserTable :: [[ModularParser Term]]
parserTable =
  -- low precedence
  [ [SelfNextParser letP, SelfNextParser lambdaP]
  , [binOpN ":" Annot]
  , [SelfNextParser piP, binOpR "→" (Pi "")]
  , [binOpL "" App]
  , [Atom varP]
  ]
  -- high precedence

{% endhighlight %}

We are almost back to what was provided by `Text.MegaParsec.Expr`, except that we have additional constructors for arbitrary `SelfNextParser`, for `Atom` parsers, and we can extend it with constructors to fit our future needs.

About this approach
-------------------

In this post, I assumed that all the parsers in the table fail without consuming input.  You might need to sprinkle some carefully-chosen `try`s if that's not the case for your parsers.

You might wonder why I put the `parens` case in `foldP`, rather than add a line `SelfNextParser $ \ _selfP nextP -> parens nextP` at the end of the table.  The issue is that for this final line of the parser, we don't want to run `choiceOrNextP` on it, because it should not default to `nextP`!  One could deal with this though, for instance by mapping `choiceOrNextP` on all but the last entries in the table.  The two approaches are equivalent.

I have not seen this technique mentioned in literature or in code or blogs in the wild.  If this was already documented elsewhere, please leave me a pointer in the comments.

I am also interested in pushing this further and having one declarative structure used for generating both the parser and the pretty-printer.  I am currently exploring a language which uses this idea [here](https://github.com/Ptival/chick) (a more complex version of the running example is in [lib/Parsing.hs](https://github.com/Ptival/chick/blob/5b68c4e4830e2f161f30f8e117945e502f5a5580/lib/Parsing.hs#L16-L57), and you can see that the generated parser is tested against the pretty-printer with HUnit, SmallCheck and QuickCheck in [test/Main.hs](https://github.com/Ptival/chick/blob/5b68c4e4830e2f161f30f8e117945e502f5a5580/test/Main.hs)).

I'm not sure this is worthy of a publication, but I might write this all up nicely in an article format and upload it to arXiv in the future.
