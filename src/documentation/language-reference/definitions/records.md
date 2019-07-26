---
title: Records
---

A _record_ is a [Sigma type](../expressions/sigma) with named projections.
The basic syntax looks like this:

{% arend %}
\record R (p_1 : A_1) ... (p_n : A_n) {
  | f_1 : B_1
  ...
  | f_k : B_k
}
{% endarend %}

where {%ard%} f_1, ... f_k {%endard%} and {%ard%} p_1, ... p_n {%endard%} are _fields_ of {%ard%} R {%endard%}.
Note that records do not have parameters and {%ard%} p_1, ... p_n {%endard%} are also fields of {%ard%} R {%endard%}.
The only difference between {%ard%} p_i {%endard%} and {%ard%} f_j {%endard%} is that {%ard%} f_j {%endard%} are visible in the scope of {%ard%} R {%endard%} and {%ard%} p_i {%endard%} are not:

{% arend %}
\func test1 => f_1
\func test2 => R.f_1
\func test3 => R.p_1

-- p_1 is not in scope in the following function:
-- \func test4 => p_1
{% endarend %}

It is also possible to write {%ard%} \field f_i : B_i {%endard%} instead of {%ard%} | f_i : B_i {%endard%}, but there is a difference between these notations, which is discussed [below](#properties).

Fields can be accessed using projection functions:

{% arend %}
\func test5 (x : R) => R.p_1 {x}
\func test6 (x : R) => f_1 {x}
{% endarend %}

An alternative way to access fields is provided by the following syntax:

{% arend %}
\func test5' (x : R) => x.p_1
\func test6' (x : R) => x.f_1
{% endarend %}

This syntax is allowed only when the expression before {%ard%} . {%endard%} is a variable with an explicitly specified type which is a record.
If {%ard%} x : R {%endard%} and {%ard%} f {%endard%} is a field of {%ard%} R {%endard%}, then {%ard%} x.f {%endard%} is equivalent to {%ard%} R.f {x} {%endard%}. 

The type {%ard%} A_i {%endard%} can depend on variables {%ard%} p_1, ... p_{i-1} {%endard%}.
The type {%ard%} B_i {%endard%} can depend on variables {%ard%} p_1, ... p_n {%endard%} and {%ard%} f_1, ... f_{i-1} {%endard%}.

Records are essentially Sigma types. For example, the record {%ard%} R {%endard%} above is equivalent to the Sigma type
{%ard%} \Sigma (p_1 : A_1) ... (p_n : A_n) (f_1 : B_1) ... (f_k : B_k) {%endard%}.

Instances of type {%ard%} R {%endard%} can be created using _new expression_. Any of the variants of the syntax listed below can be used, they are all equivalent. 
See [Class extensions](../expressions/class-ext) for more information about new expressions and related constructions.

{% arend %}
\func r1 => \new R a_1 ... a_n { | f_1 => b_1 ... | f_k => b_k }
\func r2 => \new R { | p_1 => a_1 ... | p_n => a_n | f_1 => b_1 ... | f_k => b_k }
\func r3 => \new R a_1 ... a_n b_1 ... b_k
\func r4 => \new R a_1 ... a_i { | p_{i+1} => a_{i+1} ... | p_n => a_n | f_1 => b_1 ... | f_k => b_k }
\func r5 => \new R a_1 ... a_n b_1 ... b_i { f_{i+1} => b_{i+1} ... | f_k => b_k }
{% endarend %}

The same function can also be defined using [copattern matching](functions#copattern-matching):

{% arend %}
\func r6 : R \cowith
  | p_1 => a_1
  ...
  | p_n => a_n
  | f_1 => b_1
  ...
  | f_k => b_k
{% endarend %}

Records satisfy the eta rule.
This means that the expression {%ard%} \new R r.p_1 ... r.p_n r.f_1 ... r.f_k {%endard%} is equivalent to {%ard%} r {%endard%}.

## Properties

Some fields can be marked as a _property_.
This is done by using the keyword {%ard%} \property {%endard%} instead of {%ard%} \field {%endard%}:

{% arend %}
\record NegativeInt {
  \field x : Int
  \property isNeg : x < 0
}
{% endarend %}

The type of a property must be a proposition, otherwise the definition does not typecheck.

If {%ard%} A {%endard%} is a proposition, then {%ard%} | f : A {%endard%} is also marked as a property. In this case, {%ard%} f {%endard%} can be defined as a
normal field, which is not a property, by writing {%ard%} \field f : A {%endard%}. 

Properties do not evaluate.
Thus, they are related to fields in the same way as [lemmas](functions#lemmas) are related to functions.
For example, consider the following function:

{% arend %}
\func test (x : Int) (p : x < 0) => isNeg {\new NegativeInt x p}
{% endarend %}

Then {%ard%} test x p {%endard%} evaluates to {%ard%} p {%endard%} if {%ard%} isNeg {%endard%} is not a property and does not evaluate if it is.

## Extensions

An extension {%ard%} S {%endard%} of a record {%ard%} R {%endard%} is another record which adds some fields to {%ard%} R {%endard%} and implements some of the fields of {%ard%} R {%endard%}.
The record {%ard%} R {%endard%} is called a _super class_ of {%ard%} S {%endard%} and {%ard%} S {%endard%} is called a _subclass_ of {%ard%} R {%endard%}.
If {%ard%} R {%endard%} is the definition of a record from the beginning of this page, then an extension {%ard%} S {%endard%} of {%ard%} R {%endard%} can be defined as follows:

{% arend %}
\record S (r_1 : D_1) ... (r_t : D_t) \extends R {
  | g_1 : C_1
  ...
  | g_m : C_m
  | p_{i_1} => a_{i_1}
  ...
  | p_{i_q} => a_{i_q}
  | f_{j_1} => b_{j_1}
  ...
  | f_{j_s} => b_{j_s}
}
{% endarend %}

Here expressions {%ard%} a_i {%endard%} and {%ard%} b_j {%endard%} have types {%ard%} A_i {%endard%} and {%ard%} B_j {%endard%} respectively.
Expressions {%ard%} a_i {%endard%} and {%ard%} b_j {%endard%} may refer to any field of {%ard%} S {%endard%}, but implementations must not form a cycle.

The type {%ard%} S {%endard%} is a subtype of {%ard%} R {%endard%}. That is, every expression of type {%ard%} S {%endard%} is also of type {%ard%} R {%endard%}.

A record is equivalent to the Sigma type, consisting of all of its unimplemented fields.
For example, consider the following records:

{% arend %}
\record C (x y : Nat) {
  | x<=y : x <= y
  | y<=0 : y <= 0
}

\record D \extends C {
  | y => x
  | x<=y => <=-reflexive x
}
{% endarend %}

Then {%ard%} D {%endard%} is equivalent to {%ard%} \Sigma (x : Nat) (x <= 0) {%endard%}:

{% arend %}
\func fromD (d : D) : \Sigma (x : Nat) (x <= 0) => (d.x, d.y<=0)
\func toD (p : \Sigma (x : Nat) (x <= 0)) => \new D p.1 p.2
\func fromToD (d : D) : toD (fromD d) = d => idp
\func toFromD (p : \Sigma (x : Nat) (x <= 0)) : fromD (toD p) = p => idp
{% endarend %}

where {%ard%} idp {%endard%} is the proof by reflexivity.
This works since both records and Sigma types satisfy eta rules.

A record can extend several records.
If these records extend some base record themselves, then the fields of this base record will not be repeated in the final record.
For example, consider the following records:

{% arend %}
\record A (x : Nat)
\record B \extends A
\record C \extends A
\record D \extends B,C
{% endarend %}

Then {%ard%} D {%endard%} has a single field {%ard%} x {%endard%}.
If super classes have fields with the same name which are not defined in some common super class, then the final record
will have several different fields with the same name.
In order to access these fields, fully qualified names should be used:

{% arend %}
\record B (x : Nat)
\record C (x : Nat)
\record D \extends B,C

\func fromD (d : D) : \Sigma Nat Nat => (B.x {d}, C.x {d})
\func toD (p : \Sigma Nat Nat) => \new D p.1 p.2
\func fromToD (d : D) : toD (fromD d) = d => idp
\func toFromD (p : \Sigma Nat Nat) : fromD (toD p) = p => idp
{% endarend %}

## This

Every field of a record {%ard%} R {%endard%} has additional implicit parameter of type {%ard%} R {%endard%}, which can be referred to with the keyword {%ard%} \this {%endard%}:

{% arend %}
\record R (X : \Type) (t : X -> X)

\func f (r : R) => r.t

\record S \extends R {
  | x : X
  | p : f \this x = x
}
{% endarend %}

The keyword {%ard%} \this {%endard%} can appear only in arguments of definitions and only in those arguments, which in turn satisfy this condition.
