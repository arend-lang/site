---
layout: single
title: Arend Features
sidebar:
  nav: "about"
toc: true
toc_label: Arend Features
toc_sticky: true
---

{% include about-arend.md place="below" %}

Arend also has a simple and powerful mechanism of dealing with universe levels, see [here](#universe-levels).

# Homotopy Features

Arend is based on homotopy type theory with an interval type.
This means that it has a built-in contractible interval type together with two constructors {%ard%} left, right : I {%endard%}.
We can use this type to define the type of _n_-dimensional cubes as {%ard%} \Sigma I ... I {%endard%}, that is as the product of _n_ itervals.
These types are not very interesting by themselves since they are contractible,
but they can be used as types of cells in the definition of a higher inductive type as discussed below.

## Path Types

A path in a type {%ard%} A {%endard%} between points {%ard%} a, a' : A {%endard%} is a function {%ard%} f : I -> A {%endard%} such that {%ard%} f left == a {%endard%} and {%ard%} f right == a' {%endard%} (we use "==" to denote the definitional equality).
The type of paths is denoted {%ard%} a = a' {%endard%}.
To get a path from a function and vice verse, we can use the following functions:

{% arend %}
path (f : I -> A) : f left = f right

@ (p : a = a') : I -> A
{% endarend %}

Function {%ard%} @ {%endard%} is usually written in infix form and pronounced "at".
Function {%ard%} path {%endard%} is actually the only constructor of the data type {%ard%} = {%endard%}.
Functions {%ard%} path {%endard%} and {%ard%} @ {%endard%} are mutually inverse,
that is, {%ard%} path f @ i == f i {%endard%} and {%ard%} path (\lam i => p @ i) == p {%endard%}.

This definition of path types has several nice properties.
First, all the usual constructions (such as concatenation of paths, transport, and the J rule) are definable for them.
Moreover, some of these constructions satisfy additional computational equalities.
For example, we can define the function that applies a map to a path as follows:

{% arend %}
\func pmap {A B : \Type} (f : A -> B) {a a' : A} (p : a = a') : f a = f a'
  => path (\lam i => f (p @ i))
{% endarend %}

This function is strictly functorial, that is we have equalities {%ard%} pmap id p == p {%endard%}
and {%ard%} pmap (\lam x => g (f x)) p == pmap g (pmap f p) {%endard%}.

It is also easy to _prove_ functional extensionality:

{% arend %}
\func funExt {A : \Type} (B : A -> \Type) (f g : \Pi (x : A) -> B x) (h : \Pi (x : A) -> f x = g x) : f = g
  => path (\lam i a => h a @ i)
{% endarend %}

This function also satisfies various definitional equalities, which means that we can pass easily between equality of functions and their pointwise equality.

## Higher Inductive Types

A higher inductive type is a data type that has higher cells as its constructors.
For example, the 1-dimensional sphere can be defined as the data type with one point {%ard%} base {%endard%} and one 1-dimensional constructor {%ard%} loop {%endard%} attached to this point:

{% arend %}
\data S1
  | base
  | loop I \with {
    | left => base
    | right => base
  }
{% endarend %}

Higher constructors such as {%ard%} loop {%endard%} work like ordinary functions:
{%ard%} loop left {%endard%} and {%ard%} loop right {%endard%} evaluate to {%ard%} base {%endard%}.
The syntax of such constructors is the same as the syntax of functions defined by pattern matching.

We can also attach cells of even higher dimensions.
For example, the 2-dimensional sphere can be defined as the data type with one point {%ard%} base2 {%endard%} and one 2-dimensional constructor {%ard%} loop2 {%endard%} attached to this point.
Since the boundary of 2-dimensional cube consists of four 1-dimensional cubes, we need to specify four conditions on constructor {%ard%} loop2 {%endard%}:

{% arend %}
\data S2
  | base2
  | loop2 I I \with {
    | left, _ => base2
    | right, _ => base2
    | _, left => base2
    | _, right => base2
  }
{% endarend %}

Functions over higher inductive types can be defined by pattern matching as usual.
The only difference is that it is required that they respect equations on constructors.
For example, to define a function {%ard%} S2 -> T {%endard%}, we need to specify one point {%ard%} b : T {%endard%} and one function {%ard%} l : I -> I -> T {%endard%}
such that {%ard%} l left _ == b {%endard%}, {%ard%} l right _ == b {%endard%}, {%ard%} l _ left == b {%endard%}, and {%ard%} l _ left == b {%endard%}:

{% arend %}
\func f (x : S2) : T
  | base2 => b
  | loop2 i j => l i j
{% endarend %}

If this definition does not satisfy the conditions described above, an error message will be generated.

## Truncated Data Types

Truncated data types can be defined as higher inductive types as usual, but there is a simpler way to do this.
A data type can be defined as {%ard%} \truncated {%endard%}, which means that it will be truncated to the specified homotopy level.
For example, set quotients can be defined as follows:

{% arend %}
\truncated \data Quotient {A : \Type} (R : A -> A -> \Type) : \Set
  | in~ A
  | ~-equiv (x y : A) (R x y) (i : I) \elim i {
    | left => in~ x
    | right => in~ y
  }
{% endarend %}

Such data types can be eliminated only into types of the corresponding homotopy level.

## Pattern Matching

A pattern matching on a higher inductive type can be simplified if the goal has some finite homotopy level.
To define a function into an n-type, it is enough to specify its values for constructors of dimension less than or equal to n + 1.
For example, if {%ard%} X {%endard%} is a set, to define a function {%ard%} Quotient A R -> X {%endard%},
it is enough to specify its value for each {%ard%} a : A {%endard%} and prove that this definition respects the equivalence relation
(this proof is the value corresponding to the second constructor).
This works for the definition of quotients we gave above and also for quotients defined as a higher inductive type.

If {%ard%} P x {%endard%} is a proposition, to define a function {%ard%} \Pi (x : Quotient A R) -> P x {%endard%},
it is enough to specify it for the constructor {%ard%} in~ {%endard%}.
This becomes even more useful when {%ard%} P {%endard%} depends on several elements of the quotient.
For example, if we have 3 elements {%ard%} x, y, z : Quotient A R {%endard%} (which is defined as a higher inductive type with 3 constructors),
then to prove some property about them, we need to consider only one case (since its the only 0-dimensional one) instead of nine.

# Class System

Arend has records and classes.
Classes are just records with additional functionality, which makes them into a haskell-style type classes.

## Inheritance

Records are just Sigma types with named fields.
For example, we can define the type of monoids as follows:

{% arend %}
\record Monoid (E : \Set)
  | ide : E
  | \infixl 7 * : E -> E -> E

  | ide-left (x : E) : ide * x = x
  | ide-right (x : E) : x * ide = x
  | *-assoc (x y z : E) : (x * y) * z = x * (y * z)
{% endarend %}

Records can be inherited.
If a record extends some base record, then it will have the same fields as the base one together with its own fields.
For example, we can define a group as a monoid together with three additional fields:

{% arend %}
\record Group \extends Monoid
  | inverse : E -> E
  | inverse-left (x : E) : inverse x * x = ide
  | inverse-right (x : E) : x * inverse x = ide
{% endarend %}

Extensions also can implement some of the fields of the base record.
Such a record is equivalent to the Sigma type which has all not implemented fields.
For example, the type of commutative monoids can be defined as follows:

{% arend %}
\record CMonoid \extends Monoid
  | *-comm (x y : E) : x * y = y * x
  | ide-right x => *-comm x ide *> ide-left x
{% endarend %}

For commutative monoids, it is enough to prove that {%ard%} ide {%endard%} is the left identity since the fact that it is the right identity follows from the commutativity.
We can prove this in the definition of commutative monoids by implementing the corresponding field.

Records also support multiple inheritance.
For example, we can define the type of commutative groups simply by extending the types of groups and commutative monoids:

{% arend %}
\record CGroup \extends Group, CMonoid
{% endarend %}

## Anonymous Extensions

Parameters of records are actually their fields.
So, the following two definitions of pointed sets are actually equivalent:

{% arend %}
\record Pointed (E : \Set)
  | ide : E

\record Pointed'
  | E' : \Set
  | ide' : E'
{% endarend %}

The reason why Arend does not have record parameters is because it has anonymous extensions instead.
An anonymous extension of a record {%ard%} R {%endard%} is an expression of the form {%ard%} R { | f_1 => e_1 ... | f_n => e_n } {%endard%},
where {%ard%} f_1, ... f_n {%endard%} are fields of {%ard%} R {%endard%} and {%ard%} e_1, ... e_n {%endard%} are expressions of the corresponding types.
Such an expression is the same as a records which extends {%ard%} R {%endard%} and implements specified fields, but we do not have to define this record separately.
The anonymous extension described above can also be written as {%ard%} R e_1 ... e_n {%endard%}.
In this case, fields are implemented in the same order they were defined in the record.

Let us consider some examples:
* The type {%ard%} Monoid {%endard%} is the type of monoids.
* The type {%ard%} Monoid Nat {%endard%} is the type of monoid structures on the set {%ard%} Nat {%endard%}.
* The type {%ard%} Monoid Nat 1 (Nat.*) {%endard%} is the type of proofs that {%ard%} 1 {%endard%} and {%ard%} Nat.* {%endard%} determine the structure of a monoid on {%ard%} Nat {%endard%}.

Note that the latter two examples look as if the type of monoids was defined with 1 and 3 parameters, respectively.
Thus, we do not have to worry which fields should be defined as parameters and which should be left as fields.
We can use _any_ record as if it was defined in all of these styles _at the same time_.

## Classes

Let us say we have the definition of monoids as described above.
Then we want to write expressions of the form {%ard%} (x * y) * ide * z {%endard%}, but we cannot do this.
The reason is that {%ard%} * {%endard%} and {%ard%} ide {%endard%} are fields.
This means that they require one additional argument, an instance of {%ard%} Monoid {%endard%}.
Instances of records usually cannot be inferred automatically.
For this reason, it is better to define {%ard%} Monoid {%endard%} as a _class_.
A class is defined in the same way as a record but with the keyword {%ard%} \class {%endard%} instead of {%ard%} \record {%endard%}.

Instances of classes are inferred automatically.
This inference algorithm looks for instances in two places.
First, it looks for parameters of a definition in which the field call is located.
If there is an appropriate parameter, then it will be used as a class instance.
For example, instances in the function {%ard%} test {%endard%} below will be inferred as shown in {%ard%} test2 {%endard%}.

{% arend %}
\func test {M : Monoid} (x y z : M) => (x * y) * ide * z
\func test2 {M : Monoid} (x y z : M) => (x M.* y) M.* M.ide M.* z
{% endarend %}

If there is no appropriate local instance, the algorithm will search the set of global instances.
A global instance is just a function defined using the keyword {%ard%} \instance {%endard%} instead of {%ard%} \func {%endard%}.
For example, we can prove that {%ard%} Nat {%endard%} is an instance of the class {%ard%} Monoid {%endard%} and use this instance as shown below:

{% arend %}
\instance NatMonoid : Monoid Nat
  | ide => 1
  | * => Nat.*
  | ide-left x => {?} -- the proofs are omitted
  | ide-right x => {?}
  | *-assoc x y z => {?}

\func test (x y z : Nat) => (x * y) * 1 * (z * ide)
{% endarend %}

# Universe Levels

Arend has a hieararchy of universes parameterized by two natural number.
The first parameter corresponds to the usual (predicative) level of the universe.
The second parameter corresponds to the homotopy level of types in this universe.
The universe of level (p,h) is written as {%ard%} \h-Type p{%endard%}.
The universe {%ard%} \0-Type p{%endard%} can be abbreviated as {%ard%} \Set p{%endard%}.
We can also write {%ard%} \Type p h {%endard%} instead of {%ard%} \h-Type p {%endard%}.

Levels cannot be added with each other, but we have the successor function {%ard%} \suc {%endard%} and the maximum function {%ard%} \max {%endard%}.
There is also the largest homotopy level {%ard%} \oo {%endard%}, which corresponds to untruncated types.

The universe {%ard%} \h-Type p {%endard%} belongs to the universe {%ard%} \\(h+1)-Type (p+1) {%endard%}.
Universes are cummulative: if {%ard%} A : \h-Type p {%endard%}, then {%ard%} A : \h'-Type p' {%endard%} for all h' and p' greater than or equal to h and p, respectively.

## Homotopy Levels

If a type {%ard%} A {%endard%} belongs to a universe {%ard%} \\(h+1)-Type p {%endard%},
the type of paths {%ard%} a = {A} a' {%endard%} belongs to the universe {%ard%} \h-Type p {%endard%}.
This means that universes of h-types behave in the same way as the usual ones (defined as subtypes of untruncated universes),
but we do not have to carry around proofs that some type belongs to some homotopy level.

## The Universe of Propositions

The smallest universe is {%ard%} \Prop {%endard%}, the universe of propositions.
This universe is impredicative, that is it does not have the predicative level.
Thus, if {%ard%} A {%endard%} is a set of any predicative level, then {%ard%} a = {A} a' {%endard%} belongs to {%ard%} \Prop {%endard%}.
Also, if {%ard%} B a {%endard%} belongs to {%ard%} \Prop {%endard%}, then this is also true for {%ard%} \Pi (a : A) -> B a {%endard%} regardless of levels of {%ard%} A {%endard%}.

## Universe Polymorphism

To define a polymorphic function (or any other kind of definition), we do not have to specify levels of types explicitly.
The correct level of universes usually can be inferred automatically.
For example, we can define the following function:

{% arend %}
\func test : \Type => \Type
{% endarend %}

The inferred levels of the universe in the type of the functions are greater than the levels of the universe in the body by one.

Every definition has two implicit level parameters {%ard%} \lp {%endard%} and {%ard%} \lh {%endard%} for the predicative and homotopy levels, respectively.
These levels also do not have to be specified explicitly since they also can be inferred in the same way as universe levels.
Consider the following examples:

{% arend %}
\func id {A : \Type} (a : A) => a

\class Pointed (E : \Type)
  | point : E

\func test => id Pointed
{% endarend %}

The levels of the universe of the field {%ard%} E {%endard%} are inferred to {%ard%} (\lp, \lh) {%endard%}.
This implies that {%ard%} Pointed {%endard%} belongs to {%ard%} \Type (\suc \lp) (\suc \lh) {%endard%}.
Thus, the first implicit argument of the function {%ard%} id {%endard%} in the definition {%ard%} test {%endard%} is inferred to {%ard%} \Type (\suc \lp) (\suc \lh) {%endard%}.
This implies that the level arguments are inferred to {%ard%} (\suc (\suc \lp), \suc (\suc \lh)) {%endard%}.

# Language Extensions

A language extension is a Java class which is invoked during type-checking.
This can be used to implement custom operations on the abstract syntax tree which are not supported by the language.
They can also be used to implement various decision procedures for proof automation.
To do this, you'll need [Arend API](https://github.com/JetBrains/Arend/releases/latest/download/Arend-api-1.3.0.jar) (you can also download its [sources](https://github.com/JetBrains/Arend/releases/latest/download/Arend-api-1.3.0-sources.jar)).
