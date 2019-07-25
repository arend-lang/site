---
title: Modules
---

Every top-level definition is visible throughout the file it is contained, the order of definitions does not matter.
The module system allows you to provide definitions in other namespaces.

## Modules

A module consists of a name and a list of definitions:

{% arend %}
\module Mod \where {
  def_1
  ...
  def_n
}
{% endarend %}

You can refer to definitions {%ard%} def_1 ... def_n {%endard%} inside module {%ard%} Mod {%endard%} by their names.
To refer to them outside this module, you need to use their full names {%ard%} Mod.def_1 ... Mod.def_n {%endard%}.
For example, consider the following code:

{% arend %}
\func f2 => Mod.f1
\module Mod \where {
  \func f1 => f2
  \func f2 => 0
  \func f3 => f4
}
\func f4 => f2
{% endarend %}

You cannot refer to {%ard%} f1 {%endard%} in {%ard%} f2 {%endard%} without {%ard%} Mod. {%endard%} prefix.
Function {%ard%} f4 {%endard%} refers to {%ard%} f2 {%endard%} defined on the top level.
Function {%ard%} Mod.f2 {%endard%} hides the top level {%ard%} f2 {%endard%} inside module {%ard%} Mod {%endard%}, so {%ard%} Mod.f1 {%endard%} refers to {%ard%} Mod.f2 {%endard%}.
You can refer to top level functions inside modules as shown in the example where {%ard%} Mod.f3 {%endard%} refers to {%ard%} f4 {%endard%}.

If a {%ard%} \where {%endard%} block contains only one definition, curly braces around it can be omitted.

{% arend %}
\module Mod \where
  \func f1 => 0
{% endarend %}

## Where blocks

Every definition has an associated module with the same name.
To add definitions to this module, you can write the {%ard%} \where {%endard%} block at the end of this definition.
Definitions defined in the associated module of a definition are visible inside this definition.

{% arend %}
\func f => g \where \func g => 0
\func h => f.g \where
  \data D \where {
    \func k => D
    \func s => M.g.N.s
  }
\module M \where
  \func g => N.s \where {
    \module N \where {
      \func s => E
    }
    \data E
  }
{% endarend %}

Constructors of a {%ard%} \data {%endard%} definition and fields of a {%ard%} \class {%endard%} or a {%ard%} \record {%endard%} definition are defined inside the module associated to the definition, but they are also visible outside this module.
In particular, in the following example {%ard%} f1 {%endard%} and {%ard%} f2 {%endard%} are defined by identical expressions.

{% arend %}
\data d
  | a
  | b d

\func f1 => b a
\func f2 => d.b a
{% endarend %}

Normally the members of a where block do not interact with the definition to which the block is attached.
However, where blocks of {%ard%} \data {%endard%} and {%ard%} \class {%endard%} definitions may contain special instructions that do modify the type of parent definition
 (or e. g. introduce an automatic type coercion for it). 
Such instructions begin with the keyword {%ard%} \use {%endard%} and are discussed in greater detail in [Coercion](coercion) and [Level](level).

## Open commands

The contents of a given module can be added to the current scope by means of {%ard%} \open {%endard%} command (this is called 'opening' a module).
The {%ard%} \open {%endard%} command affects all definitions in the current scope.

{% arend %}
\func h1 => f
\module M \where {
  \func f => 0
  \func g => 1
}
\open M
\func h2 => g
{% endarend %}

The command {%ard%} \open M (def_1, ... def_n) {%endard%} adds only definitions {%ard%} def_1, ... def_n {%endard%} to the current scope.
Other definitions must be refered to by their full names.

The command {%ard%} \open M \hiding (def_1, ... def_n) {%endard%} adds all the definitions of {%ard%} M {%endard%} except for {%ard%} def_1, ... def_n {%endard%}.
These definitions still can be refered to by their full names.

The command {%ard%} \open M (def_1 \as def_1', ... def_n \as def_n') {%endard%} adds definitions {%ard%} def_1, ... def_n {%endard%} under the names {%ard%} def_1', ... def_n' {%endard%}, respectively.

The command {%ard%} \open M \using (def_1 \as def_1', ... def_n \as def_n') {%endard%} can be used to add to the current scope all of the definitions of {%ard%} M {%endard%} while renaming some of them.

{% arend %}
\module M \where {
  \func f => 0
  \func g => 1
  \func h => 2
}
\module M1 \where {
  \open M (f,g)
  \func h1 => f
  \func h2 => g
  \func h3 => M.h -- we can refer to M.h only by its full name.
}
\module M2 \where {
  \open M \hiding (f,g)
  \func h1 => M.f -- we can refer to M.f and M.g only by their full names.
  \func h2 => M.g
  \func h3 => h
}
\module M3 \where {
  \open M1 (h1 \as M1_h1, h2)
  \open M2 \using (h2 \as M2_h2) \hiding (h3)
  \func k1 => M1_h1 -- this refers to M1.h1
  \func k2 => h1 -- this refers to M2.h1
  \func k3 => h2 -- this refers to M1.h2
  \func k4 => M2_h2 -- this refers to M2.h2
  \func k5 => M1.h3 -- we can refer to M1.h3 only by its full name.
}
{% endarend %}

Note that if you open a module {%ard%} M {%endard%} inside a module {%ard%} M' {%endard%} and then open {%ard%} M' {%endard%} inside {%ard%} M'' {%endard%}, then definitions from {%ard%} M {%endard%} will not be visible in {%ard%} M'' {%endard%}.
You need to explicitly open {%ard%} M {%endard%} inside {%ard%} M'' {%endard%} to make them visible.

## Import commands

If you have several files, you can use the {%ard%} \import {%endard%} command to make one of them visible in another.
For example, suppose that we have files {%ard%} A.ard {%endard%}, {%ard%} B.ard {%endard%}, a directory {%ard%} Dir {%endard%}, and a file {%ard%} Dir/C.ard {%endard%} with the following content:

{% arend %}
-- A.ard
\func a1 => 0
\func a2 => 0
  \where \func a3 => 0
{% endarend %}

{% arend %}
-- Dir/C.ard
\import A

\func c1 => a1
\func c2 => a2.a3
{% endarend %}

{% arend %}
-- B.ard
\import Dir.C

\func b1 => c1
-- \func b2 => a1 -- definitions from file A are not visible
-- \func b3 => A.a1 -- you cannot refer to definitions from file A by their full names.
\func b4 => Dir.C.c2 -- you can refer to definitions from file Dir/C.ard by their full names.
{% endarend %}

The {%ard%} \import {%endard%} command also opens the content of the imported file.
You can use the same syntax as for {%ard%} \open {%endard%} commands to control which definitions will be opened.
If you want only to import a file and not to open any definitions, you can write {%ard%} \import X () {%endard%}.
Then you can refer to definitions from the file {%ard%} X {%endard%} by their full names:

{% arend %}
-- X.ard
\func f => 0
{% endarend %}

{% arend %}
-- Y.ard
\import X()

\func f => X.f
{% endarend %}
