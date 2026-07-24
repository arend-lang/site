---
title: Universes
---

A universe is a type of types. Since the type of all types cannot be consistently introduced into a type theory
with dependent Pi types, as the type of types cannot contain itself, Arend contains a hierarchy of universes 
{%ard%} \Type n {%endard%} (the whitespace is optional), parameterized by a natural number {%ard%} n {%endard%}. This number is called the 
_predicative level_ of the universe. Informally, the universe {%ard%} \Type0 {%endard%} contains all types that do not refer to universes
in their definition, the universe {%ard%} \Type1 {%endard%} contains all types in {%ard%} \Type0 {%endard%} together with those types that
refer to {%ard%} \Type0 {%endard%} and no other universes in their definitions, and so on. This is not precise, since, for instance, 
the universe {%ard%} \Type n {%endard%} also contains some data types, classes and records that refer to {%ard%} \Type m {%endard%}, where n ≤ m, in types of parameters.
See section on universe placement rules below for more precise statements and details.  
 
Note that the hierarchy of 
universes in Arend is cumulative, that is every expression of type {%ard%} \Type n {%endard%} has also type {%ard%} \Type (n+1) {%endard%}. 

Writing {%ard%} \Type {%endard%} without a level denotes the universe with the largest, _infinite_, predicative level.
It is convenient for parameters whose predicative level does not matter. Note, however, that the infinite {%ard%} \Type {%endard%}
is not itself a small type, so it is not a member of any {%ard%} \Type n {%endard%} (in particular, not of itself). This is what
rules out contradictory circular definitions; for the same reason a definition such as {%ard%} \func bad : \Type => \Type {%endard%} is not allowed.

## Homotopy levels

Types are further stratified into universes {%ard%} \n-Type p {%endard%} according to their _homotopy level_ n,
which is an integer number (or infinity ∞) in the range: -1 ≤ n ≤ ∞. 
Some of these universes have alternative names: the universe of propositions ((-1)-types) {%ard%} \Prop {%endard%} 
and universes of sets (0-types) {%ard%} \Set p {%endard%} (coincides with {%ard%} \0-Type p {%endard%}). 
The untruncated universe (homotopy level ∞) is simply {%ard%} \Type p {%endard%}.

Unlike the predicative level, the homotopy level is _not_ an argument of {%ard%} \Type {%endard%}: the universe
{%ard%} \Type {%endard%} always denotes the untruncated universe, and each truncated universe is written with its own
keyword {%ard%} \n-Type {%endard%}, which is in turn parameterized by a predicative level. There is no
{%ard%} \oo-Type {%endard%}, and it is not possible to write two levels after {%ard%} \Type {%endard%}.

Every truncated universe must be given a (finite) predicative level. Writing {%ard%} \Set {%endard%} or
{%ard%} \66-Type {%endard%} with the level omitted is an error ("Infinite level is not allowed here"). Supply a
concrete level, as in {%ard%} \Set 0 {%endard%}, or a level parameter (see [Level polymorphism](#level-polymorphism)).
Only {%ard%} \Type {%endard%} may be used without a level.

Note that the universe {%ard%} \Prop {%endard%} is _impredicative_: it does not have a predicative level. Practically, this means that
if {%ard%} B : \Prop {%endard%}, then the type {%ard%} \Pi (x : A) -> B {%endard%} is in {%ard%} \Prop {%endard%} for any {%ard%} A {%endard%}. 

The universe {%ard%} \Prop {%endard%} is not proof irrelevant, but some elements of propositions are computationally equal.
If {%ard%} A : \Prop {%endard%} and {%ard%} a, a' : A {%endard%} are such that they never evaluate to a constructor, then they are computationally equal.
For example, if the type is an empty data type, then this is true for any pair of its elements, so they will always be computationally equal.

## Universe placement rules

Types in Arend are distributed over the universes according to the following rules. Below we write {%ard%} \h-Type p {%endard%}
for the universe of homotopy level {%ard%} h {%endard%} and predicative level {%ard%} p {%endard%}, where {%ard%} h = ∞ {%endard%}
corresponds to the untruncated universe {%ard%} \Type p {%endard%} and {%ard%} h = -1 {%endard%} to {%ard%} \Prop {%endard%}.

* If {%ard%} A : \h_1-Type p_1 {%endard%} and {%ard%} B : \h_2-Type p_2 {%endard%}, then {%ard%} \Sigma A B : \max(h_1,h_2)-Type max(p_1,p_2) {%endard%}.
* If {%ard%} A : \h_1-Type p_1 {%endard%} and {%ard%} B : \h_2-Type p_2 {%endard%}, then {%ard%} \Pi (x:A) -> B : \h_2-Type max(p_1,p_2) {%endard%}.
  Note that if {%ard%} B : \Prop {%endard%}, then {%ard%} (\Pi (x : A) -> B) : \Prop {%endard%} for any {%ard%} A {%endard%}.
* If 0 ≤ h < ∞, then {%ard%} \h-Type p : \(h+1)-Type (p+1) {%endard%}.
* {%ard%} \Prop : \Set 0 {%endard%}, which is the same as {%ard%} \Prop : \0-Type 0 {%endard%}.
* {%ard%} \Type p : \Type (p+1) {%endard%} (the untruncated universe stays untruncated).
* If {%ard%} A : I -> \h-Type p {%endard%}, then {%ard%} Path A a a' : \max(-1,h-1)-Type p {%endard%}.
  In particular, if {%ard%} A : \Set p {%endard%}, then {%ard%} a = a' : \Prop {%endard%}.
* If {%ard%} D {%endard%} is a data type and {%ard%} A_1 : \h_1-Type p_1, ..., A_k : \h_k-Type p_k {%endard%} are types of parameters
  of constructors of {%ard%} D {%endard%}, then predicative level of {%ard%} D {%endard%} is the maximum over {%ard%} 0, p_1, ..., p_k {%endard%}.
  If {%ard%} D {%endard%} has conditions, equalising a constructor on two ends of the interval type, then homotopy level of 
  {%ard%} D {%endard%} is ∞. Otherwise, if {%ard%} D {%endard%} has more than one constructor, then its homotopy level is
  the maximum over {%ard%} 0, h_1, ..., h_k {%endard%}, and if {%ard%} D {%endard%} has at most one constructor, then its homotopy level
  is the maximum over {%ard%} -1, h_1, ..., h_k {%endard%}.
* If {%ard%} C {%endard%} is a class or record and {%ard%} A_1 : \h_1-Type p_1, ..., A_k : \h_k-Type p_k {%endard%} are types of parameters
  of unimplemented fields of {%ard%} C {%endard%} (including fields of superclasses), then its predicative level is the maximum 
  over {%ard%} 0, p_1, ..., p_k {%endard%} and its homotopy level is the maximum over {%ard%} -1, h_1, ..., h_k {%endard%}.       

## Level polymorphism

A definition can be made polymorphic in the predicative level by declaring one or more _level parameters_ right after
its name, using the syntax {%ard%} .{...} {%endard%}, and referring to them in universes such as {%ard%} \Type l {%endard%}:

{% arend %}
\func id.{l} (A : \Type l) (a : A) => a
{% endarend %}

There is no implicit level parameter: a definition that mentions only the bare (infinite) {%ard%} \Type {%endard%} is
not level-polymorphic. Homotopy levels are not a polymorphic axis; only predicative levels can be abstracted this way.

Level arguments can be specified explicitly in a defcall with the same {%ard%} .{...} {%endard%} syntax; the arguments
are level expressions:

{% arend %}
\func test1 => id.{0} Nat 0
\func test2.{l} => id.{\suc l} (\Type l) Nat
{% endarend %}

Level expressions are defined inductively:

* A level parameter (such as {%ard%} l {%endard%} above) is a level expression.
* A constant (that is, a natural number) is a level expression.
* {%ard%} _ {%endard%} is a level expression. Such an expression suggests the typechecker to infer the expression.
* If {%ard%} l {%endard%} is a level expression, then {%ard%} \suc l {%endard%} is also a level expression.
* If {%ard%} l1 {%endard%} and {%ard%} l2 {%endard%} are level expressions, then {%ard%} \max l1 l2 {%endard%} is also a level expression.

## Multiple level parameters

A definition may declare several predicative level parameters, separated by commas; they are independent level variables:

{% arend %}
\func pair.{l1, l2} (A : \Type l1) (B : \Type l2) => \Sigma A B
{% endarend %}

Level arguments for such a definition are given in the same order, again with {%ard%} .{...} {%endard%}:

{% arend %}
\func example => pair.{0, 1} Nat \Type0
{% endarend %}

If level parameters are not explicitly declared for a definition, they will be inherited from definitions that appear in parameters if all of them have the same levels.

## Level inference

The level arguments of a function in a defcall can often be inferred automatically, so {%ard%} .{...} {%endard%} rarely
needs to be written explicitly. For example, {%ard%} id Nat 0 {%endard%} elaborates to {%ard%} id.{0} Nat 0 {%endard%}.

The levels of a universe in the signature of a function can also be omitted, in which case they will be inferred by
the typechecker. Note, however, that a bare {%ard%} \Type {%endard%} denotes the infinite universe rather than a level to
be inferred; and {%ard%} \Set {%endard%}/{%ard%} \n-Type {%endard%} require a finite predicative level, so an unconstrained
level there is an error rather than being defaulted silently.

The levels in the parameters and in the result type of a recursive function are inferred before the levels in the body.

A definition is marked as _universe-like_ if it contains universes or universe-like definitions applied to one of its
level parameters. If {%ard%} D {%endard%} is a universe-like definition, then {%ard%} D.{p} {%endard%} is equivalent to
{%ard%} D.{p'} {%endard%} only if {%ard%} p = p' {%endard%}. If {%ard%} D {%endard%} is not universe-like, then these
expressions are always equivalent.
