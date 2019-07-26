---
title: Classes
toc: false
---

A _class_ is a record that has several useful properties.
A class is defined in the same way as a record, but it begins with the keyword {%ard%} \class {%endard%} instead of {%ard%} \record {%endard%}.
Classes can extend other classes and records and vice versa.
The first explicit parameter of a class is called its _classifying field_.
Classes are implicitly coerced to the type of the classifying field.
Let us consider an example:

{% arend %}
\class Semigroup (E : \Set)
  | \infixl 7 * : E -> E -> E
  | *-assoc (x y z : E) : (x * y) * z = x * (y * z)

\func square {S : Semigroup} (x : S) => x * x
{% endarend %}

It is allowed to write {%ard%} x : S {%endard%} instead of {%ard%} x : S.E {%endard%} since {%ard%} S {%endard%} is implicitly coerced to an element of type {%ard%} \Set {%endard%}, that is {%ard%} S.E {%endard%}.

In case an parameter of a definition or a constructor has type, which is an [extension](../expressions/class-ext) {%ard%} C { ... } {%endard%} of {%ard%} C {%endard%},
it is marked as a _local instance_ of class {%ard%} C {%endard%}. Implicit parameter {%ard%} \this {%endard%} of a field of class {%ard%} C {%endard%} is also a local instance. 


If the parameter {%ard%} p : C { ... } {%endard%} of {%ard%} f {%endard%} is a local instance, then the value of {%ard%} p {%endard%} in a usage of {%ard%} f {%endard%} is inferred to 
a local instance {%ard%} v : C { ... } {%endard%}, visible in the context of the usage of {%ard%} f {%endard%}, if the expected value of the classifying
field of {%ard%} p {%endard%} coincides with the classifying field of {%ard%} v {%endard%}. 
For instance, the function {%ard%} square {%endard%} in the example above has one local instance {%ard%} S {%endard%} of the class {%ard%} Semigroup {%endard%}.
The field {%ard%} * {%endard%} of the class {%ard%} Semigroup {%endard%} is used in the body of {%ard%} square {%endard%} and the expected type of its call in {%ard%} x * x {%endard%} is 
{%ard%} S.E -> S.E -> {?} {%endard%}. This implies that the expected classifying field is {%ard%} S.E {%endard%}, which is the classifying field of the
local instance {%ard%} S {%endard%}, so this instance is inferred as the implicit argument of {%ard%} * {%endard%}.

## Instances

It is also possible to define _global instances_.
To do this, one needs to use the keyword {%ard%} \instance {%endard%}:

{% arend %}
\instance NatSemigroup : Semigroup Nat
  | * => Nat.*
  | *-assoc => {?} -- the proof is omitted
{% endarend %}

A global instance is just a function, defined by [copattern matching](functions#copattern-matching).
It can be used as an ordinary function.
The only difference with an ordinary function is that it can only be defined by copattern matching and must define an
instance of a class.
Also, the classifying field of an instance must be a data or a record applied to some arguments and if some parameters
of the instance have a class as a type, its classifying field must be an argument of the classifying field of the 
resulting instance.

If there is no local instance with the expected classifying field, then such an instance will be searched among
global instances.
There is no backtracking, so the first appropriate instance will be chosen.
A global instance is appropriate in a usage if the expected classifying field is the same data or record
as the data or the record in the classifying field of the instance. If this holds, the global instance
is appropriate even if the data or the record are applied to different arguments.
