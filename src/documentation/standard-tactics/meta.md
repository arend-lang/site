---
title: \module Meta
---

# Scope metas

Meta {%ard%} using {%endard%}, {%ard%} usingOnly {%endard%}, and {%ard%} hiding {%endard%} controls the scope.

+ {%ard%} using (e_1, ... e_n) e {%endard%} adds {%ard%} e_1, ... e_n {%endard%} to the context before checking {%ard%} e {%endard%}.
  {%ard%} using (e_1, ... e_n) {%endard%} is sometimes used in other context-manipulating metas,
  that adds {%ard%} e_1, ... e_n {%endard%} to the context it uses.
+ {%ard%} usingOnly (e_1, ... e_n) e {%endard%} replaces the context with {%ard%} e_1, ... e_n {%endard%} before checking {%ard%} e {%endard%}.
  {%ard%} usingOnly (e_1, ... e_n) {%endard%} is sometimes used in other context-manipulating metas,
  that replaces the context is uses with {%ard%} e_1, ... e_n {%endard%}.
+ {%ard%} hiding (e_1, ... e_n) e {%endard%} hides local bindings {%ard%} e_1, ... e_n {%endard%} from the context before checking {%ard%} e {%endard%}.
  {%ard%} hiding (e_1, ... e_n) {%endard%} is sometimes used in other context-manipulating metas,
  that hides {%ard%} e_1, ... e_n {%endard%} from the context it uses.

# cases

{%ard%} cases args default {%endard%} works just like {%ard%} mcases args default {%endard%}, but does not search for {%ard%} \case {%endard%} expressions or definition invocations.
Each argument has a set of parameters that can be configured.
Parameters are specified after keyword 'arg' which is written after the argument.
Available parameters are 'addPath' and 'name'.
The latter can be used to specify the name of the argument which can be used in types of subsequent arguments.
The type of an argument is specified as either {%ard%} e : E {%endard%} or {%ard%} e arg parameters : E {%endard%}.
The flag 'addPath' indicates that argument {%ard%} idp {%endard%} with type {%ard%} e = x {%endard%} should be added after the current one, where {%ard%} e {%endard%} is the current argument and {%ard%} x {%endard%} is its name.
That is, {%ard%} cases (e arg addPath) {%endard%} is equivalent to {%ard%} cases (e arg (name = x), idp : e = x) {%endard%}.

# mcases

{%ard%} mcases {def} args default \with { ... } {%endard%} finds all invocations of definition {%ard%} def {%endard%} in the expected type and generate a {%ard%} \case {%endard%} expression that matches arguments of those invocations.
It matches only those arguments which are matched in {%ard%} def {%endard%}.
If the explicit argument is omitted, then {%ard%} mcases {%endard%} searches for {%ard%} \case {%endard%} expressions instead of definition invocations.
{%ard%} default {%endard%} is an optional argument which is used as a default result for missing clauses.
The list of clauses after {%ard%} \with {%endard%} can be omitted if the default expression is specified.
{%ard%} args {%endard%} is a comma-separated list of expressions (which can be omitted) that will be additionally matched in the resulting {%ard%} \case {%endard%} expressions.
These arguments are written in the same syntax as arguments in {%ard%} cases {%endard%}.
{%ard%} mcases {%endard%} also searches for occurrences of {%ard%} def {%endard%} in the types of these additional expressions.
Parameters of found arguments can be specified in the second implicit argument.
The syntax is similar to the syntax for arguments in {%ard%} cases {%endard%}, but the expression should be omitted.
If the first implicit argument is {%ard%} _ {%endard%}, it will be skipped.
{%ard%} mcases {def_1, ... def_n} {%endard%} searches for occurrences of definitions {%ard%} def_1, ... def_n {%endard%}.
{%ard%} mcases {def, i_1, ... i_n} {%endard%} matches arguments only of {%ard%} i_1 {%endard%}-th, ... {%ard%} i_n {%endard%}-th occurrences of {%ard%} def {%endard%}.
For example,
* {%ard%} mcases {(def1,4),def2,(def3,1,2)} {%endard%} looks for the 4th occurrence of {%ard%} def1 {%endard%}, all occurrences of {%ard%} def2 {%endard%}, and the first and the second occurrence of {%ard%} def3 {%endard%}.
* {%ard%} mcases {(1,2),(def,1)} {%endard%} looks for the first and the second occurrence of a {%ard%} \case {%endard%} expression and the first occurrence of {%ard%} def {%endard%}.
* {%ard%} mcases {(def1,2),(),def2} {%endard%} looks for the second occurrence of {%ard%} def1 {%endard%}, all occurrences of {%ard%} \case {%endard%} expressions, and all occurrences of {%ard%} def2 {%endard%}.
* {%ard%} mcases {_} {arg addPath, arg (), arg addPath} {%endard%} looks for case expressions and adds a path argument after the first and the third matched expression.

# unfold

{%ard%} unfold (f_1, ... f_n) e {%endard%} unfolds functions {%ard%} f_1, ... f_n {%endard%} in the expected type before type-checking of {%ard%} e {%endard%} and returns {%ard%} e {%endard%} itself.
If the first argument is omitted, it unfold all fields.
If the expected type is unknown, it unfolds these function in the result type of {%ard%} e {%endard%}.

# unfold_let

{%ard%} unfold_let {%endard%} unfolds {%ard%} \let {%endard%} expressions
