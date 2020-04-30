---
title: Higher Inductive Types
---

Higher inductive types generalize ordinary [inductive types](data).
Various homotopy colimits of types and other constructions such as
truncations are higher inductive types. A specific homotopy structure of a higher inductive
type can be defined by means of _conditions_ in data definitions.

## Conditions

If {%ard%} con {%endard%} is a constructor of an inductive type {%ard%} D {%endard%}, then an expression of the form
{%ard%} con a_1 ... a_n {%endard%} does not reduce any further unless the definition of {%ard%} D {%endard%} contains _conditions_ on {%ard%} con {%endard%}.
A condition on a constructor is a rule that says how such an expression might be reduced.
For example, one can define integers as a data type with two constructors: one for positive, and one for negative integers, and a condition on the second constructor telling positive and negative zero have to be computationally equal:

{% arend %}
\data Int
  | pos Nat
  | neg Nat \with {
    | zero => pos zero
  }
{% endarend %}

Conditions are imposed on a constructor by defining it as a function by [pattern matching](functions#pattern-matching).
The only differences are that it is not required that all cases are covered and that pattern matching on constructors
{%ard%} left {%endard%} and {%ard%} right {%endard%} of the [interval type](../prelude) {%ard%} I {%endard%} is allowed.
The general syntax is the same as for ordinary pattern matching.
Either {%ard%} \with { | c_1 | ... | c_m } {%endard%} or {%ard%} \elim x_1, ... x_n { | c_1 | ... | c_m } {%endard%} can be added after parameters
of the constructor, where {%ard%} | c_1 | ... | c_m {%endard%} is a list of clauses.

A constructor with conditions evaluates if its arguments match the specification in the same way as a function defined by pattern matching.
This means that a function over a data type with conditions must respect the conditions, this is checked
by the typechecker.
For example, a function of type {%ard%} Int -> X {%endard%} must map positive and negative zero to the same value.
Thus, one cannot define the following function:

{% arend %}
\func f (x : Int) : Nat
  | pos n => n
  | neg n => suc n
{% endarend %}

## Higher inductive types

A higher inductive type is a data type with a constructor that has conditions of the form {%ard%} | left => e {%endard%} and {%ard%} | right => e' {%endard%}.
Let us give a few examples:

{% arend %}
-- Circle
\data S1
  | base
  | loop I \with {
    | left => base
    | right => base
  }

-- Suspension
\data Susp (A : \Type)
  | north
  | south
  | merid A (i : I) \elim i {
    | left => north
    | right => south
  }

-- Propositional truncation
\data Trunc (A : \Type)
  | inT A
  | truncT (x y : Trunc A) (i : I) \elim i {
    | left => x
    | right => y
  }

-- Set quotient
\data Quotient (A : \Type) (R : A -> A -> \Type)
  | inQ A
  | equivQ (x y : A) (R x y) (i : I) \elim i {
    | left => inQ x
    | right => inQ y
  }
  | truncQ (a a' : Quotient A R) (p p' : a = a') (i j : I) \elim i, j {
    | i, left  => p @ i
    | i, right => p' @ i
    | left,  _ => a
    | right, _ => a'
  }
{% endarend %}

If {%ard%} X {%endard%} is a proposition, then, to define a function of type {%ard%} Trunc A -> X {%endard%}, it is enough to specify its value for {%ard%} inT a {%endard%}.
The same works for any higher inductive type and any level.
For example, to define a function {%ard%} Quotient A R -> X {%endard%}, it is enough to specify its value for {%ard%} inQ a {%endard%} and {%ard%} equivQ x y r i {%endard%}
if {%ard%} X {%endard%} is a set and only for {%ard%} inQ a {%endard%} if it is a proposition.
This also works for several arguments.
For example, if {%ard%} X {%endard%} is a set, then, to define a function {%ard%} Quotient A R -> Quotient A R -> X {%endard%},
it is enough to specify its value for {%ard%} inQ a, inQ a' {%endard%}, {%ard%} inQ a, equivQ x y r i {%endard%}, and {%ard%} equivQ x y r i, inQ a {%endard%}.
