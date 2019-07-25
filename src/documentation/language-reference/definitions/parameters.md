---
title: Parameters
---

The syntax of a number of language constructions in Arend includes parameter declarations.
Parameter declarations can be named or unnamed, typed or untyped and explicit or implicit.

Some of the language constructions allow unnamed parameter declarations at the same time requiring them to be typed
 (examples are definitions of data or its constructors, {%ard%} \Pi {%endard%} or {%ard%} \Sigma {%endard%} expressions).
Most of the other constructions require their parameter declarations to be named while allowing them to be untyped
 (exceptions to this rule are functions, records and instances which require parameter declarations to be named and typed at the same time).

{% arend %}
\data d
  | c1 (a : Nat)   -- typed named explicit
  | c2 Nat         -- typed unnamed explicit
  | c3 {a : Nat}   -- typed named implicit
  | c4 {Nat}       -- typed unnamed implicit
{-| c5 b           -- untyped parameter declarations are not allowed in constructors -}

\func g1 => 
  \lam a => suc a  -- untyped named explicit

\func g2 =>
  \lam {a} =>      -- untyped named implicit
    suc a

{-
\func f a => a     -- parameters of functions must be named and typed
\func f Nat => 1
 -}
{% endarend %}

## Syntax

A named explicit parameter has the form {%ard%} (x : T) {%endard%}, where {%ard%} x {%endard%} is the name of the parameter and {%ard%} T {%endard%} is its type expression.
An implicit parameter has the form {%ard%} {x : T} {%endard%}, where {%ard%} x {%endard%} and {%ard%} T {%endard%} are the same as before.

Parameters are specified after the name of a definition.
For example, all of the definitions below have three parameters: {%ard%} x1 {%endard%} of type {%ard%} A1 {%endard%}, {%ard%} x2 {%endard%} of type {%ard%} A2 {%endard%}, and {%ard%} x3 {%endard%} of type {%ard%} A3 {%endard%}.

{% arend %}
\func f {x1 : A1} {x2 : A2} {x3 : A3} => 0
\data D (x1 : A1) (x2 : A2) (x3 : A3)
\class C (x1 : A1) {x2 : A2} (x3 : A3)
{% endarend %}

Multiple parameters of the same type can be specified via the following syntax: {%ard%} x_1 ... x_n : T {%endard%}.
For example, the following function has two implicit parameters of type {%ard%} A1 {%endard%}, three explicit parameters of type {%ard%} A2 {%endard%}, and one explicit parameter of type {%ard%} A3 {%endard%}:

{% arend %}
\func f {x1 x2 : A1} (y1 y2 y3 : A2) (z : A3) => B
{% endarend %}

This definition is equivalent to the following one:

{% arend %}
\func f {x1 : A1} {x2 : A1} (y1 : A2) (y2 : A2) (y3 : A2) (z : A3) => B
{% endarend %}

The types of subsequent parameters may depend on the previous ones.
In the example above, parameters {%ard%} x1 {%endard%} and {%ard%} x2 {%endard%} may appear in {%ard%} A2 {%endard%} and {%ard%} A3 {%endard%},
parameters {%ard%} y1 {%endard%}, {%ard%} y2 {%endard%}, and {%ard%} y3 {%endard%} may appear in {%ard%} A3 {%endard%}, and all of the parameters may appear in {%ard%} B {%endard%}.

If a parameter is never used, its name can be replaced with {%ard%} _ {%endard%}.
Such a name cannot be refered to, so this simply indicated that this parameter is ignored.

## Implicit arguments

Let {%ard%} f {%endard%} be a definition with parameters of types {%ard%} A_1, ... A_n {%endard%}.
If all of the parameters are explicit, then we can form an expression of the form {%ard%} f a_1 ... a_n {%endard%}, where {%ard%} a_i {%endard%} is an expression of type {%ard%} A_i {%endard%}.
Such an expression invokes {%ard%} f {%endard%} with the specified arguments.
If some of the parameters of {%ard%} f {%endard%} are implicit, then corresponding arguments must be omitted.
For example, consider the following code:

{% arend %}
\func f (x : A1) {y y' : A2} (z : A3) {z : A4} => 0
\func g => f a1 a3
{% endarend %}

In the expression {%ard%} f a1 a3 {%endard%}, arguments corresponding to parameters {%ard%} y {%endard%}, {%ard%} y' {%endard%}, and {%ard%} z {%endard%} are omitted.
The typechecker tries to infer these parameters and reports an error if it fails to do so.
We can ask typechecker to try to infer an explicit parameter by writing {%ard%} _ {%endard%} instead of the corresponding argument:

{% arend %}
\func f (x : A1) {y y' : A2} (z : A3) {z : A4} => 0
\func g => f _ a3
{% endarend %}

In the example above, the typechecker will try to infer the argument corresponding to {%ard%} x {%endard%}.
Actually, the expression {%ard%} _ {%endard%} can be written anywhere at all.
The typechecker infers the omitted expression only if there is a unique solutions to the inference problem 
 (i. e. there is only one expression with which {%ard%} _ {%endard%} can be replaced so that the surrounding definition typechecks correctly).

Finally, if the typechecker cannot infer an implicit argument, it can be specified explicitly by writing {%ard%} {e} {%endard%}.
For example, to specify explicitly the second and the last arguments of {%ard%} f {%endard%}, we can write the following code:

{% arend %}
\func f (x : A1) {y y' : A2} (z : A3) {z : A4} => 0
\func g => f _ {a2} a3 {a4}
{% endarend %}

In this example, arguments corresponding to {%ard%} x {%endard%} and {%ard%} y' {%endard%} are left implicit and other arguments are explicitly specified.

If {%ard%} op {%endard%} is an infix operator, then we can write {%ard%} x op {a_1} ... {a_n} y {%endard%}, which is equivalent to {%ard%} op {a_1} ... {a_n} x y {%endard%}.
In other words, implicit arguments which are written immediately after an infix operator are considered to be its first arguments.

{% arend %}
\func f (A : \Type) => \lam a b => a = {A} b
{% endarend %}
