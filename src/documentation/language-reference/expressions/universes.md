---
title: Universes
---

A universe is a type of types. Since the type of all types cannot be consistently introduced to a type theory
with dependent Pi types, as the type of types cannot contain itself, Arend contains a hierarchy of universes 
{%ard%} \Type n {%endard%} (the whitespace is optional), parameterized by a natural number {%ard%} n {%endard%}. This number is called the 
_predicative level_ of the universe. Informally, the universe {%ard%} \Type0 {%endard%} contains all types that do not refer to universes
in their definition, the universe {%ard%} \Type1 {%endard%} contains all types in {%ard%} \Type0 {%endard%} together with those types that
refer to {%ard%} \Type0 {%endard%} and no other universes in their definitions, and so on. This is not precise, since, for instance, 
the universe {%ard%} \Type n {%endard%} contains also some data types, classes and records that refer to {%ard%} \Type m {%endard%}, where n ≤ m, in types of parameters.
See section on universe placement rules below for more precise statements and details.  
 
Note that the hierarchy of 
universes in Arend is cumulative, that is every expression of type {%ard%} \Type n {%endard%} has also type {%ard%} \Type (n+1) {%endard%}. 

Types in {%ard%} \Type n {%endard%} in Arend are also arranged in universes {%ard%} \h-Type n {%endard%} according to their _homotopy level_ h,
which is an integer number (or infinity ∞) in the range: -1 ≤ h ≤ ∞. 
Some of these universes have alternative names: the universe of propositions (-1-types) {%ard%} \Prop {%endard%} 
(coincides with {%ard%} \-1-Type n {%endard%} for any {%ard%} n {%endard%}) and universes of sets (0-types) {%ard%} \Set n {%endard%} (coincides with {%ard%} \0-Type n {%endard%}). 
Note that the universe {%ard%} \Prop {%endard%} is _impredicative_: it does not have predicative level. Practically, this means that
if {%ard%} B : \Prop {%endard%}, then the type {%ard%} \Pi (x : \Prop) -> B {%endard%} is in {%ard%} \Prop {%endard%}. 

The universe {%ard%} \Prop {%endard%} is not proof irrelevant, but some elements of propositions are computationally equal.
If {%ard%} A : \Prop {%endard%} and {%ard%} a, a' : A {%endard%} are such that they never evaluate to a constructor, then they are computationally equal.
For example, if the type is an empty data type, then this is true for any pair of its elements, so they always be computationally equal.

Universes with h equal to ∞ are represented in the syntax as {%ard%} \oo-Type p {%endard%}. The homotopy level can also be 
specified after the predicative level: {%ard%} \Type p h {%endard%} is equivalent to {%ard%} \h-Type p {%endard%}.   

## Universe placement rules

Types in Arend are distributed over the universes according to the following rules:

* If {%ard%} A : \h_1-Type p_1 {%endard%} and {%ard%} B : \h_2-Type p_2 {%endard%}, then {%ard%} \Sigma A B : \max(h_1,h_2)-Type max(p_1,p_2) {%endard%}.
* If {%ard%} A : \h_1-Type p_1 {%endard%} and {%ard%} B : \h_2-Type p_2 {%endard%}, then {%ard%} \Pi (x:A) -> B : \h_2-Type max(p_1,p_2) {%endard%}.
  Note that if {%ard%} A {%endard%} is {%ard%} \Prop {%endard%} and {%ard%} B : \Prop {%endard%}, then {%ard%} (\Pi (x : \Prop) -> B) : \Prop {%endard%}.
* If 0 ≤ h < ∞, then {%ard%} \h-Type p : \(h+1)-Type (p+1) {%endard%}.
* {%ard%} \Prop : \Set 0 {%endard%}, which is the same as {%ard%} \Prop : \0-Type 0 {%endard%}.
* {%ard%} \oo-Type p : \oo-Type (p+1) {%endard%}.
* If {%ard%} A : I -> \h-Type p {%endard%}, then {%ard%} Path A a a' : \max(-1,h-1)-Type p {%endard%}.
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

Every definition is considered to be polymorphic in both levels.
That is, every definition has two additional parameters: one for a predicative level and one for a homotopy level.
These parameters are denoted by {%ard%} \lp {%endard%} and {%ard%} \lh {%endard%} respectively.
Level arguments can be specified explicitly in a defcall by writing {%ard%} \levels p h {%endard%}, where {%ard%} p {%endard%} and {%ard%} h {%endard%} are level expressions of the corresponding kind.
For example, {%ard%} Path (\lam _ => Nat) 0 0 {%endard%} is equivalent to {%ard%} Path \levels 0 0 (\lam _ => Nat) 0 0 {%endard%}.  
Keyword {%ard%} \levels {%endard%} can often be omitted (if the resulting expression is unambiguous).
The {%ard%} \Prop {%endard%} level can be specified by the expression {%ard%} \levels \Prop {%endard%}.
Level expressions are defined inductively:

* {%ard%} \lp {%endard%} is a level expression of the predicative kind and {%ard%} \lh {%endard%} is a level expression of the homotopy kind.
* A constant (that is, a natural number) is a level expression of both kinds. There is also constant {%ard%} \oo {%endard%} for homotopy levels which denotes the infinity level.
* {%ard%} _ {%endard%} is a level expression of both kinds. Such an expression suggests the typechecker to infer the expression.
* If {%ard%} l {%endard%} is a level expression, then {%ard%} \suc l {%endard%} is also a level expression of the same kind as {%ard%} l {%endard%}.
* If {%ard%} l1 {%endard%} and {%ard%} l2 {%endard%} are level expressions of the same kind, then {%ard%} \max l1 l2 {%endard%} is also a level expression of the same kind as {%ard%} l1 {%endard%} and {%ard%} l2 {%endard%}.

Since the only level variables are {%ard%} \lp {%endard%} and {%ard%} \lh {%endard%}, the expression {%ard%} \max l1 l2 {%endard%} is useful only when one of the levels is a constant.

## Level parameters

It is possible to declare definitions with several level parameters with the following syntax:
{% arend %}
\func func \plevels p1 <= p2 <= p3 \hlevels h1 >= h2 (A : \Type p2 h1) (B : \Type p3 h2) => \Type p1
{% endarend %}

All level parameters of the same type must be linearly ordered.
In the example above, {%ard%} func {%endard%} has three predicative level parameters which are declared in ascending order and two homotopy level parameters in descending order.
Level arguments for a definition with multiple level parameters can be specified as before:
{% arend %}
\func example => func \levels (1,2,3) (2,1) Nat Nat
{% endarend %}

If level parameters are not explicitly declared for a definition, they will be inhereted from definitions that appear in parameters if all of them have the same levels.

## Global level declarations

Levels can be also declared on the top level as follows:

{% arend %}
\plevels p1 <= p2 <= p3
\hlevels h1 >= h2
{% endarend %}

These levels can be used in any definition, in which case they will be used as level parameters of this definition.

## Level inference

The level arguments of a function in a defcall can often be inferred automatically.
Moreover, both levels of a universe in the signature of a function can also be omitted, in which case they
will also be inferred by the typechecker.
The typechecker always tries to infer the minimal level which mentions either {%ard%} \lp {%endard%} or {%ard%} \lh {%endard%} if possible.
Consider, for example, the following code which defines the identity function:

{% arend %}
\func id {A : \Type} (a : A) => a
{% endarend %}

The minimal appropriate level (both predicative and homotopy) of the universe {%ard%} \Type {%endard%} in the definition of this function is 0,
but it is also possible to use levels {%ard%} \lp {%endard%} and {%ard%} \lh {%endard%}, so this function is equivalent to the following one:

{% arend %}
\func id' {A : \Type \lp \lh} (a : A) => a
{% endarend %}

Consider a few more examples.
Every definition below is followed by an equivalent definition with explicitly specified levels.

{% arend %}
\data Either (A B : \Type) | inl A | inr B
\data Either' (A B : \Type \lp \lh) | inl A | inr B

\func f => id \Type
\func f' => id (\suc \lp) (\suc \lh) (\Type \lp \lh)

\func fromEither {A : \Type} (e : Either A \Type) : \Type \elim e
  | inl a => A
  | inr X => X
\func fromEither' {A : \Type \lp \lh} (e : Either (\suc \lp) (\suc \lh) A (\Type \lp \lh)) : \Type \lp \lh \elim e
  | inl a => A
  | inr X => X
{% endarend %}

The levels in parameters and in the result type of a recursive function are inferred before levels in the body.
In particular, this means that the following function will not typecheck:

{% arend %}
\func eitherToType {A : \Type} (e : Either A A) : \Type
  | inl _ => \Type
  | inr _ => \Type
{% endarend %}

This problem can be fixed by specifying explicitly the levels of the universe that appears in the result type:

{% arend %}
\func eitherToTypeFixed {A : \Type} (e : Either A A) : \Type (\suc \lp) (\suc \lh)
  | inl _ => \Type
  | inr _ => \Type
\func eitherToTypeFixed' {A : \Type \lp \lh} (e : Either \lp \lh A A) : \Type (\suc \lp) (\suc \lh)
  | inl _ => \Type \lp \lh
  | inr _ => \Type \lp \lh
{% endarend %}

If levels are set to constants instead as shown below, then the function also will typecheck,
but the levels of universes in the body will also be constants:

{% arend %}
\func eitherToTypeConstant {A : \Type} (e : Either A A) : \3-Type 7
  | inl _ => \Type
  | inr _ => \Type
\func eitherToTypeConstant' {A : \Type \lp \lh} (e : Either \lp \lh A A) : \3-Type 7
  | inl _ => \Set0
  | inr _ => \Set0
{% endarend %}

Note that homotopy levels inferred by the typechecker are always greater than or equal to 0.
Thus, the function {%ard%} eitherToProp {%endard%} below does not typecheck, {%ard%} eitherToPropFixed {%endard%} should be
used instead:

{% arend %}
\func eitherToProp {A : \Type} (e : Either A A) : \Set0
  | inl _ => \Type
  | inr _ => \Type

\func eitherToPropFixed {A : \Type} (e : Either A A) : \Set0
  | inl _ => \Prop
  | inr _ => \Prop
{% endarend %}

Levels in the result type of a non-recursive function are inferred simultaneously with the
levels in the body.
For example, the following function typechecks:

{% arend %}
\func f : \Type => \Type
\func f' : \Type (\suc \lp) (\suc \lh) => \Type \lp \lh
{% endarend %}

A definition is marked as _universe-like_ if it contains universes or universe-like definitions applied to either {%ard%} \lp {%endard%} or {%ard%} \lh {%endard%}.
It is often true that the level of a definition can be inferred to either {%ard%} c {%endard%} or {%ard%} \lp + c {%endard%} for some constant {%ard%} c {%endard%}.
If a definition is universe-like, then the inference algorithm uses the latter option, otherwise it uses the former option.
Also, if {%ard%} D {%endard%} is a universe-like definition, then {%ard%} D \levels p h {%endard%} is equivalent to {%ard%} D \levels p' h' {%endard%} only if {%ard%} p = p' {%endard%} and {%ard%} h = h' {%endard%}.
If {%ard%} D {%endard%} is not universe-like, then these expressions are always equivalent.
