---
title: Prelude
---

Prelude is a built-in module, containing several definitions, which behave differently from ordinary definitions.
It is always imported implicitly in every module.
You can also import it explicitly to hide or rename some of its definitions.

We will discuss these definitions in this module.
You can look at the file `Prelude.ard`, which contains these definitions, but note that they only roughly correspond
to actual definitions since most of them cannot be actually defined in the ordinary syntax.

# Nat and Int

The definitions of {%ard%} Nat {%endard%}, {%ard%} Int {%endard%}, {%ard%} Nat.* {%endard%}, {%ard%} Nat.<= {%endard%}, and {%ard%} Nat.div {%endard%} are actually correct,
they could have been as well defined in an ordinary file and successfully typechecked according to normal Arend typechecking rules.
The only difference is that these definitions from Prelude are implemented more efficiently.
Definitions of {%ard%} Nat.divMod {%endard%}, {%ard%} Nat.divModProp {%endard%}, and {%ard%} Nat.modProp {%endard%} are omitted, but these functions also can be defined in Arend.

Functions {%ard%} Nat.+ {%endard%} and {%ard%} Nat.- {%endard%} have more computational rules than can be defined normally:
{% arend %}
n + 0 => n
n + suc m => suc (n + m)
0 + m => m
suc n + m => suc (n + m)

0 - m => neg m
n - 0 => pos n
suc n - suc m => n - m
{% endarend %}

Finally, {%ard%} Nat.mod (suc n) {%endard%} has type {%ard%} Fin (suc n) {%endard%} and {%ard%} Nat.divMod (suc n) {%endard%} has type {%ard%} \Sigma Nat (Fin (suc n)) {%endard%}.

# Fin

The type {%ard%} Fin n {%endard%} is a subtype of {%ard%} Nat {%endard%} and also a subtype of {%ard%} Fin (suc n) {%endard%}.
Constructors of {%ard%} Nat {%endard%} are also constructors of {%ard%} Fin n {%endard%}: {%ard%} zero {%endard%} has type {%ard%} Fin (suc n) {%endard%} and if {%ard%} x : Fin n {%endard%}, then {%ard%} suc x : Fin (suc n) {%endard%}.

# Array

{%ard%} Array {%endard%} is a record consisting of a type of its elements {%ard%}A{%endard%}, its length {%ard%}len{%endard%}, and a function {%ard%} Fin len -> A {%endard%}.
Thus, {%ard%} Array A {%endard%} is equivalent to the type of lists of elements of type {%ard%} A {%endard%} and {%ard%} Array A n {%endard%} is equivalent to the type of vectors of elements of type {%ard%} A {%endard%} and length {%ard%} n {%endard%}.

The type of dependent arrays {%ard%} DArray {%endard%} is a generalization of {%ard%} Array {%endard%} in which {%ard%} A : Fin len -> \Type {%endard%} is a dependent type and elements are given by a dependent function {%ard%} \Pi (j : Fin len) -> A j {%endard%}.

# Interval and squeeze functions

The definition of the interval type {%ard%} \data I | left | right {%endard%} looks like the definition of the set with two
elements, but this is not true actually.
One way to think about this data type is that it has one more constructor, which connects {%ard%} left {%endard%} and
{%ard%} right {%endard%} and which cannot be accessed explicitly. This means that it is forbidden to define a function
on {%ard%} I {%endard%} by pattern matching. Functions from {%ard%} I {%endard%} can be defined by means of several auxiliary functions:
{%ard%} coe {%endard%}, {%ard%} coe2 {%endard%}, {%ard%} squeeze {%endard%}, {%ard%} squeezeR {%endard%}. Function {%ard%} coe {%endard%} plays the role of eliminator for {%ard%} I {%endard%}, it is discussed
further in this module.

Functions {%ard%} squeeze {%endard%} and {%ard%} squeezeR {%endard%} satisfy the following computational conditions:
{% arend %}
squeeze left j => left
squeeze right j => j
squeeze i left => left
squeeze i right => i

squeezeR left j => j
squeezeR right j => right
squeezeR i left => i
squeezeR i right => right
{% endarend %}

Such functions can be defined in terms of the function {%ard%} coe {%endard%},
but for efficiency purposes they are defined as primitives in Arend.

# Path

The definition of {%ard%} Path A a a' {%endard%} is not correct.
By the definition, it should consist of all functions {%ard%} \Pi (i : I) -> A i {%endard%}, but actually it consists of all such
functions {%ard%} f {%endard%} that also satisfy computational conditions {%ard%} f left => a {%endard%} and {%ard%} f right => a' {%endard%}.
This means that while typechecking the expression {%ard%} path f {%endard%} the typechecker also checks that these computational conditions hold and, if they don't, produces an error message.
For example, if you write {%ard%} \func test : 1 = 0 => path (\lam _ => 0) {%endard%}, you will see the following error message:

{% arend %}
[ERROR] test.ard:1:23: The left path endpoint mismatch
  Expected: 1
    Actual: 0
  In: path (\lam _ => 0)
  While processing: test
{% endarend %}

The homotopy level of the universe, which is the type of {%ard%} Path {%endard%}, is also computed differently. If -1 ≤ n and
{%ard%} A {%endard%} is in a universe of (n+1)-types, then {%ard%} Path A a a' {%endard%} is in a universe of n-types. Otherwise, it has the same
homotopy level as {%ard%} A {%endard%}.

Prelude also contains an infix form of {%ard%} Path {%endard%} called {%ard%} = {%endard%} which is actually a correctly defined function.
The definition of {%ard%} @ {%endard%} is also correct, but the typechecker has an eta rule for this definition:
{% arend %}
path (\lam i => p @ i) == p
{% endarend %}
This rule does not apply to functions {%ard%} @ {%endard%} defined in other files.

Finally, function {%ard%} Path.inProp {%endard%} is not correct since it does not have a body.
It postulates the proof irrelevance for types in {%ard%} \Prop {%endard%}, namely that any two elements of a type in {%ard%} \Prop {%endard%} are equal.

# idp

The constructor {%ard%} idp {%endard%} is not a correct definition since it is not allowed to use lambdas in constructors.
This constructor can be used to replace the J operator with pattern matching.
For example, we can define J itself as follows:

{% arend %}
\func J {A : \Type} {a : A} (B : \Pi (a' : A) -> a = a' -> \Type) (b : B a idp) {a' : A} (p : a = a') : B a' p \elim p
  | idp => b
{% endarend %}

After we match {%ard%} p {%endard%} with {%ard%} idp {%endard%}, variables {%ard%} a {%endard%} and {%ard%} a' {%endard%} become equivalent.
To be more precise, we can refer to both variables, but the latter will evaluate to the former.

There are certain restrictions on this pattern matching principle.
If we want to match {%ard%} p : e = e' {%endard%} with {%ard%} idp {%endard%}, expressions {%ard%} e {%endard%} and {%ard%} e' {%endard%} cannot be arbitrary.
At least one of them must be a variable which does not occur in the other expression.
Also, it should be possible to substitute the variable with this expression, which means that the free variables of the expression should be bound at each occurrence of the variable.

This pattern matching principle can also be used in case-expressions.
For example, J can be defined as follows:

{% arend %}
\func J {A : \Type} {a : A} (B : \Pi (a' : A) -> a = a' -> \Type) (b : B a idp) {a' : A} (p : a = a') : B a' p
  => \case \elim a', \elim p \with {
    | _, idp => b
  }
{% endarend %}

Note that the restrictions we described above should be satisfied.
Moreover, the expression which is matched with {%ard%} idp {%endard%} should have type {%ard%} p : e = e' {%endard%},
where either {%ard%} e {%endard%} or {%ard%} e' {%endard%} is a variable bound in one of the arguments of the case expression.

# coe and coe2

Function {%ard%} coe {%endard%} is an eliminator for the interval type.
For every type over the interval, it allows to transport elements from the fiber over {%ard%} left {%endard%} to the fiber over an
arbitrary point.
It can be used to prove that {%ard%} I {%endard%} is contractible and that {%ard%} = {%endard%} satisfies the rules for
ordinary identity types.
The definition of {%ard%} coe {%endard%} is not correct since it uses pattern matching on the interval.
This function satisfies one additional reduction rule:
{% arend %}
coe (\lam x => A) a i => a
{% endarend %}
if {%ard%} x {%endard%} is not free in {%ard%} A {%endard%}.

Function {%ard%} coe2 {%endard%} is a generalization of {%ard%} coe {%endard%}, which allows to transport elements between any two fibers of a type
over the interval.

# iso

The definition of {%ard%} iso {%endard%} is not correct since it uses pattern matching on the interval.
This definition implies the univalence axiom.
