---
title: Lexical Structure
---

## Keywords

All Arend's _keywords_ begin with `\`.
Here's the complete list of keywords:

[\open](definitions/modules#open-commands) [\import](definitions/modules#import-commands) [\hiding](definitions/modules#open-commands) [\as](definitions/modules#open-commands) [\using](definitions/modules#open-commands)
[\truncated](definitions/data#truncation) [\data](definitions/data) [\cons](definitions/data#constructor-synonyms) [\func](definitions/functions) [\lemma](definitions/functions#lemmas) [\axiom](definitions/functions#lemmas) [\sfunc](definitions/functions#sfunc) [\type](definitions/types) [\class](definitions/classes) [\record](definitions/records) [\meta](definitions/metas)
[\classifying](definitions/classes#classifying-fields) [\noclassifying](definitions/classes#classifying-fields) [\strict](definitions/parameters#strict-parameters) [\alias](definitions#aliases)
[\field](definitions/records) [\property](definitions/records#properties) [\override](definitions/records#override) [\default](definitions/records#default) [\extends](definitions/records) [\module](definitions/modules#modules) [\instance](definitions/classes)
[\use](definitions/coercion) [\coerce](definitions/coercion) [\level](definitions/level) [\levels](expressions/universes#level-polymorphism) [\plevels](expressions/universes#level-parameters) [\hlevels](expressions/universes#level-parameters) [\box](expressions/box) [\eval](definitions/functions#sfunc) [\peval](definitions/functions#sfunc)
[\with](definitions/functions#pattern-matching) [\elim](definitions/functions#elim) [\cowith](definitions/functions#copattern-matching) [\where](definitions/modules#where-blocks)
[\infix](definitions#infix-operators) [\infixl](definitions#infix-operators) [\infixr](definitions#infix-operators) [\fix](definitions#precedence) [\fixl](definitions#precedence) [\fixr](definitions#precedence)
[\new](expressions/class-ext) [\this](definitions/records) [\Pi](expressions/pi) [\Sigma](expressions/sigma) [\lam](expressions/pi) [\let](expressions/let) [\let!](expressions/let) [\have](expressions/let) [\have!](expressions/let) [\in]((expressions/let)) [\case](expressions/case) [\scase](expressions/case#scase) [\return](expressions/case)
[\lp](expressions/universes#level-polymorphism) [\lh](expressions/universes#level-polymorphism) [\suc](expressions/universes#level-polymorphism) [\max](expressions/universes#level-polymorphism) [\oo](expressions/universes#level-polymorphism)
[\Prop](expressions/universes) [\Set](expressions/universes) [\Type](expressions/universes).

## Numerals

A _positive numeral_ is a non-empty sequence of digits.
A _negative numeral_ consists of symbol `-` followed by a non-empty sequence of digits.

## Identifiers

An _identifier_ consists of a non-empty sequence of lower and upper case letters, digits, and characters from the list `'~!@#$%^&*-+=<>?/|[]:_`.
Exceptions are sequences that begin with a digit or symbol `'`, numerals, and reserved names such as `->`, `=>`, `_`, `:`, and `|`.

Examples:

* Valid identifiers: `xxx`, `+`, `$^~]!005x`, `::`, `->x`, `x:Nat`, `-5b`, `-33+7`, `--xxx`, `f'`.
* Invalid identifiers: `5b`, `-33`, `=>`, `α`.

## Infix and postfix notation

A _postfix notation_ is an identifier which follows `` ` ``.
An _infix notation_ is an identifier surrounded by `` ` ``.
Both of these notations are described in [Definitions](definitions).

## Comments

_Multi-line comments_ are enclosed in `{-` and `-}` and can be nested.
_Single-line comments_ consist of a sequence of symbols `-` of length at least 2 followed by a whitespace followed by an arbitrary text until the end of the line.
To give an example, `--`, `--------`, `-- foo`, and `------- foobar` are comments but `--foo`, `foo--bar`, and `------foobar` are not.
