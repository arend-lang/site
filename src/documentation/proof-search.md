---
title: Arend Proof Search
nav: proof-search
---

Nearly every proof assistant has a problem of the discoverability for proven theorems. For instance, try to recall how a lemma describing the commutativity of addition is called in your favorite proof assistant. Is it `add_comm`? Or `+-comm`?

IntelliJ Arend provides a possibility to search for functions by definitions they are talking about. We call this functionality the _Proof Search_. Its closest relatives are the [Search](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Search) vernacular command of Coq and [Type Directed Search](http://docs.idris-lang.org/en/latest/reference/type-directed-search.html) of Idris.

# Overview

Signature search can be invoked by `Find Action` > `Proof Search` or via the predefined hotkey `Ctrl + Alt + P` (`⌥ ⌘ P` on macOS).

![User interface](ui.png)

The user interface is clear: you can just type the proof search query in the input field.

Simply put, the _Proof Search_ will show all definitions that have a specified pattern as a subexpression of their result type.

{%arend%}
-- The following definitions can be found by the pattern `List`:
\func foo : List Nat
\func bar : \Sigma (List Bool) Nat
\func baz {A : \Type} : List A
{%endarend%}

It is possible to specify a `_` as a pattern for an arbitrary term. Also, patterns can be provided in their infix form.
{%arend%}
-- The following definitions can be found by the pattern `_ + _ = _ + _`.
\func foo (a b : Nat) : a + b = b + a
\func bar (a b : Int) : a + b = b + a
{%endarend%}

Apart from displaying the search results, it is possible to show the definition in the proof search popup (by pressing `Enter` on the selected entry), navigate to the selected definition in the source code (`F4`), and insert the selected definition in the editor (`Ctrl + Enter`). 

# Query Language

Results of the search can be refined by specifying a restrictive query.
_Proof Search Queries_ admit the following grammar:

```
query        ::= (and_pattern '->')* and_pattern
and_pattern  ::= (app_pattern '\and')* app_pattern
app_pattern  ::= atom_pattern+ 
atom_pattern ::= '_' | (IDENTIFIER '.')* IDENTIFIER | '(' app_pattern ')'
```

IntelliJ Arend provides highlighting of the queries, so syntax errors will be easily discoverable.

## Parameters and result type

If there is an `->` in a query (i.e. it has several `and_pattern`s), then the rightmost `and_pattern` will be matched with the codomain of the definition and the rest patterns delimited by `->` will be matched with parameters of the definition.

{%arend%}
-- The pattern is `Foo -> Bar`
\func foo (f : Foo) : Bar -- matched
\func bar :    Foo -> Bar -- matched
\func baz :           Bar -- rejected
{%endarend%}

The order of the left `and_pattern`s is not important.

{%arend%}
-- The pattern is `Nat -> Bool -> List Nat`
\func foo (n : Nat)  (b : Bool) : List Nat -- matched
\func bar (b : Bool) (n : Nat)  : List Nat -- matched
{%endarend%}

## Matching multiple patterns in the same term

If there is a `\and` in a `and_pattern` (i.e. it has several `app_pattern`s), then the term matches the `and_pattern` iff it matches all its `app_pattern`s at once. This is useful when you want to find a function that tells something about several definitions, but you don't recall their exact interaction structure.

{%arend%}
-- The query is `Nat \and Bool`
\func foo : \Sigma (List Nat) Bool -- matched
\func bar : List Bool = Nat        -- matched
{%endarend%}

Certainly, it is possible to use `\and` in patterns for parameters:
{%arend%}
-- The query is `Nat \and Bool -> _`
\func foo (e : \Sigma (List Nat) Bool) : 1 = 1 -- matched
{%endarend%}

There is a difference between `Nat -> Bool -> _` and `Nat \and Bool -> _`: the former will match all definitions that have (not necessarily distinct) parameters of types mentioning `Nat` and `Bool`, while the latter requires the existence of a parameter, that mentions `Nat` _and_ `Bool` at the same time.

## Restricting namespaces

`app_pattern` resembles an application of a function. It can represent a tree of a function call, where subtrees (nested applications) should be surrounded by `()`. An `_` can be specified when an arbitrary term is acceptable here. It is not necessary to consider the exact arity of a function in a pattern.

{%arend%}
\func foo (n : Nat) (m : Bool) : \Type
\func bar (n : Nat) : Nat
\func baz : Nat

-- The following matches the queries `foo (bar baz) _`, 
-- `foo (bar baz)`, `foo _`, `foo`
\func f : List (foo (bar baz) true) -- matched
{%endarend%}

It is possible to specify a prefix of a module path for the identifier. Also note that IntelliJ Arend provides code completion for the queries.
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
