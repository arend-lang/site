---
title: Signature Search
nav: signature-search
---

Nearly each proof assistant has a problem of discoverability for proven theorems. For instance, try to recall how a lemma for commutativity of addition in your favorite proof assistant is called. Is it `add_comm`? Or `+-comm`?

IntelliJ Arend provides a possibility to search for functions by definitions they are talking about. We call this functionality _signature search_. Its closest relatives are the [Search](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Search) vernacular command of Coq and [Type Directed Search](http://docs.idris-lang.org/en/latest/reference/type-directed-search.html) of Idris.

# Overview

Signature search can be invoked by `Find Action` > `Signature Search` or via predefined hotkey `Ctrl + Alt + P` (`⌥ ⌘ P` on macOS).

![User interface](ui.png)

Here we can see an input field for patterns, settings of the search, button for moving the search results to the "Find Usages" toolwindow and a link to this webpage.

Simply put, Signature Search will show all definitions that have a specified pattern as a subexpression of their result type.

{%arend%}
-- The following definitions can be found by pattern `List`:
\func foo : List Nat
\func bar : \Sigma (List Bool) Nat
\func baz {A : \Type} : List A
{%endarend%}

It is possible to specify a `_` as a pattern for an arbitrary term. Also, patterns can be provided in their infix form.
{%arend%}
-- The following definitions can be found by pattern `_ + _ = _ + _`.
\func foo (a b : Nat) : a + b = b + a
\func bar (a b : Int) : a + b = b + a
{%endarend%}


# Query Language

Results of the search can be refined by specifying a restrictive query.
Signature Search Query admits the following grammar:

```
query               ::= (conjunctive_pattern '->')* conjunctive_pattern
conjunctive_pattern ::= (applicative_pattern '\and')* applicative_pattern
applicative_pattern ::= atom_pattern+ 
atom_pattern        ::= '_' | (IDENTIFIER '.')* IDENTIFIER | '(' applicative_pattern ')'
```

IntelliJ Arend provides highlighting of queries, so syntax errors will be easily discoverable.

## Parameters and result type

If there is a `->` in a query (i.e. it has several `conjunctive_pattern`s), then the last `conjunctive_pattern` will be matched against a codomain of the definition and the rest patterns delimited by `->` will be matched against parameters of the definition.

{%arend%}
-- The pattern is `Foo -> Bar`
\func foo (f : Foo) : Bar -- matched
\func bar :    Foo -> Bar -- matched
\func baz :           Bar -- rejected
{%endarend%}

The order of the first `conjunctive_pattern`s is not important.

{%arend%}
-- The pattern is `Nat -> Bool -> List Nat`
\func foo (n : Nat)  (b : Bool) : List Nat -- matched
\func foo (b : Bool) (n : Nat)  : List Nat -- matched
{%endarend%}

## Matching multiple patterns in the same term

If there is a `\and` in a `conjunctive_pattern` (i.e. it has several `applicaive_pattern`s), then the term matches the `conjunctive_pattern` if it maches all its `applicative_pattern`s at once. This is useful when you want to find a function that tells something about several definitions, but you don't recall their exact interaction structure.

{%arend%}
-- The query is `Nat \and Bool`
\func foo : \Sigma (List Nat) Bool -- matched
\func foo : List Bool = Nat        -- matched
{%endarend%}

Certainly, it is possible to use `\and` in patterns for parameters:
{%arend%}
-- The query is `Nat \and Bool -> _`
\func foo (e : \Sigma (List Nat) Bool) : 1 = 1 -- matched
{%endarend%}

There is a difference between `Nat -> Bool -> _` and `Nat \and Bool -> _`: the former will match all definitions that have not necessarily distinct parameters of types mentioning `Nat` and `Bool`, while the latter require existence of a parameter, that mentions `Nat` _and_ `Bool` at the same time.

## Restricting namespaces

`applicative_pattern` resembles an application of a function. It can represent a tree of a function call. Application in arguments should be surrounded by `()`. An `_` can be specified when an arbitrary term is suitable here. It is not necessary to consider exact arity of a function in pattern.

{%arend%}
\func foo (n : Nat) (m : Bool) : \Type
\func bar (n : Nat) : Nat
\func baz : Nat

-- The following matches the queries `foo (bar baz) _`, 
-- `foo (bar baz)`, `foo _`, `foo`
\func f : List (foo (bar baz) true) -- matched
{%endarend%}

It is possible to specify a prefix of module path for the identifier. Also note, that IntelliJ Arend provides code completion for Signature Search.
{%arend%}
\module Foo \where \func foo : Nat
\module Bar \where \func foo : Nat

-- The query is `foo`
\func f : Foo.foo -- matched
\func g : Bar.foo -- matched
\func h : \Sigma (Foo.foo = Bar.foo) -- matched

-- The query is `Foo.foo`
\func f : Foo.foo -- matched
\func g : Bar.foo -- rejected
\func h : \Sigma (Foo.foo = Bar.foo) -- matched

-- The query is `Foo.foo \and Bar.foo`
\func f : Foo.foo -- rejected
\func g : Bar.foo -- rejected
\func h : \Sigma (Foo.foo = Bar.foo) -- matched
 
{%endarend%}
