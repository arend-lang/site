---
title: Functions
---

Functions in Arend are functions in the mathematical sense.
They can have arbitrary arity.
In particular, constants in Arend are just functions of arity 0.
A definition of a function {%ard%} f {%endard%} consists of the signature of {%ard%} f {%endard%} followed by the body of {%ard%} f {%endard%}.
The full syntax of function signatures is as follows:   

{% arend %}
\func f p_1 ... p_n : T
{% endarend %}

where {%ard%} f {%endard%} is the name of the function, {%ard%} p_1, ... p_n {%endard%} are named [parameters](parameters) and
{%ard%} T {%endard%} is the result type. In some cases specification {%ard%} : T {%endard%} of the result type can be omitted depending on the 
definition of function body.

There are several ways to define the body of a function. These ways are described below.   

## Non-recursive definitions

A non-recursive function can be defined simply by specifying an expression for the result of the function: 

{% arend %}
\func f p_1 ... p_n : T => e
{% endarend %}

where {%ard%} e {%endard%} is an expression, which must be
of type {%ard%} T {%endard%} if it is specified. In such definitions the result type {%ard%} : T {%endard%} can often be omitted as the typechecker 
can usually infer it from {%ard%} e {%endard%}.

For example, to define the identity function on type {%ard%} A {%endard%}, write the following code:

{% arend %}
\func id (x : A) => x
{% endarend %}

A function with three parameters that returns the second one can be defined as follows:

{% arend %}
\func second (x : A) (y : B) (z : C) => y
{% endarend %}

You can explicitly specify the result types of these functions.
The definitions above are equivalent to the following definitions:

{% arend %}
\func id (x : A) : A => x
\func second (x : A) (y : B) (z : C) : B => y
{% endarend %}

Parameters of a function may appear in its body and in its result type.

## Pattern matching

Functions can be defined by pattern matching.
Let {%ard%} D {%endard%} be an [inductive type](data) with constructors {%ard%} con1 {%endard%} and {%ard%} con2 Nat {%endard%}.
You can define a function which maps {%ard%} D {%endard%} to natural numbers in such a way that {%ard%} con1 {%endard%} is mapped to {%ard%} 0 {%endard%} and {%ard%} con2 n {%endard%} is mapped to {%ard%} suc n {%endard%}:

{% arend %}
\func f (d : D) : Nat
  | con1 => 0
  | con2 n => suc n
{% endarend %}

The result type of a function defined by pattern matching must be specified explicitly.
The general form of function definition by pattern matching is

{% arend %}
\func f (x_1 : T_1) ... (x_n : T_n) : R
  | clause_1
  ...
  | clause_k
{% endarend %}

where each {%ard%} clause_i {%endard%} is of the form

{% arend %}
p^i_1, ... p^i_n => e_i
{% endarend %}

where {%ard%} p^i_j {%endard%} is a pattern of type {%ard%} T_i {%endard%} (see below for the definition of a pattern) and {%ard%} e_i {%endard%} is an
expression of type {%ard%} R[p^i_1/x_1, ... p^i_n/x_n] {%endard%} (see [Expressions](../expressions) for the
discussion of the substitution operation and types of expressions).
Variables {%ard%} x_1, ... x_n {%endard%} are not visible in expressions {%ard%} e_i {%endard%}.
Note that this construction requires all the variables to be matched on,
that is the number of patterns in each clause must be {%ard%} n {%endard%} (but see [below](#elim) for partial pattern matching). 

The clauses {%ard%} clause_1, ... clause_k {%endard%} must cover all the cases.
That is, if there is a pattern of the form {%ard%} con p_1 ... p_n {%endard%}, where {%ard%} con {%endard%} is a constructor of a data type {%ard%} D {%endard%},
then there must be patterns of the form {%ard%} con' p_1' ... p_k' {%endard%} for all constructors {%ard%} con' {%endard%} of {%ard%} D {%endard%}.

Pattern matching on constructors {%ard%} left {%endard%} and {%ard%} right {%endard%} of the [interval type](../prelude) {%ard%} I {%endard%} is not allowed.
For example, the definition {%ard%} \func f (i : I) : Nat | left => 0 | right => 1 {%endard%} is not valid.  

If some of the parameters of {%ard%} f {%endard%} are implicit, corresponding patterns must be either omitted or specified explicitly by surrounding them in {%ard%} { } {%endard%}.

The definition above can be equivalently written using the keyword {%ard%} \with {%endard%}:

{% arend %}
\func f p_1 ... p_n : R \with { | clause_1 ... | clause_k } 
{% endarend %}

A _pattern_ of type {%ard%} T {%endard%} can have one of the following forms:

* A variable. If a variable {%ard%} x {%endard%} appears as a subpattern of {%ard%} p_i {%endard%} in a clause {%ard%} | p_1 ... p_i ... => e {%endard%}, 
it can be used in {%ard%} e {%endard%} and it will have type {%ard%} T {%endard%}. If this variable is not used anywhere, its name can be replaced with {%ard%} _ {%endard%}.
* {%ard%} con s_1 ... s_m {%endard%}, where {%ard%} con (y_1 : A_1) ... (y_m : A_m) {%endard%} is a constructor of a data type {%ard%} D {%endard%} and {%ard%} s_1 ... s_m {%endard%} are patterns.
  In this case, {%ard%} T {%endard%} must be equal to {%ard%} D {%endard%} and pattern {%ard%} s_i {%endard%} must have type {%ard%} A_i[s_1/y_1, ... s_{i-1}/y_{i-1}] {%endard%}.
  If some of the parameters of {%ard%} con {%endard%} are implicit, corresponding patterns must either be omitted or enclosed in {%ard%} { } {%endard%}.
* {%ard%} (s_1, ... s_m) {%endard%}, where {%ard%} s_1 ... s_m {%endard%} are patterns.
  In this case, {%ard%} T {%endard%} must be either a [Sigma type](../expressions/sigma) with parameters {%ard%} (y_1 : A_1) ... (y_m : A_m) {%endard%} or a [class](classes) (or a [record](records)) with fields {%ard%} y_1 : A_1, ... y_m : A_m {%endard%}.
  The pattern {%ard%} s_i {%endard%} must have type {%ard%} A_i[s_1/y_1, ... s_{i-1}/y_{i-1}] {%endard%}.
  If {%ard%} m {%endard%} equals to 0, then {%ard%} T {%endard%} may also be a data type without constructors.
  In this case, the right hand side {%ard%} => e_i {%endard%} of the clause in which such a pattern appears must be omitted.

Also, a constructor or a tuple pattern may be an _as-pattern_.
This means that there might be an expressions of the form {%ard%} \as x : E {%endard%} after the pattern, where {%ard%} x {%endard%} is a variable and {%ard%} E {%endard%} is its type which can be omitted.
Then {%ard%} x {%endard%} is equivalent to this pattern.

Now, let us discuss how expressions of the form {%ard%} f a_1 ... a_n {%endard%} evaluate (see [Expressions](../expressions/#evaluation) for the definition of the reduction and evaluation relations).
Let {%ard%} E {%endard%} be equal to {%ard%} f a_1 ... a_n {%endard%}.
To reduce this expression, we first evaluate expressions {%ard%} a_1, ... a_n {%endard%} and match them with the patterns in the definition of {%ard%} f {%endard%} left to right, top to bottom.
If all patterns {%ard%} p^i_1, ... p^i_n {%endard%} matches with {%ard%} a_1, ... a_n {%endard%} for some i, then {%ard%} E {%endard%} reduces to {%ard%} e_i[b_1/y_1, ... b_k/y_k] {%endard%},
where {%ard%} y_1, ... y_k {%endard%} are variables that appear in {%ard%} p^i_1, ... p^i_n {%endard%} and {%ard%} b_1, ... b_k {%endard%} are subexpressions of {%ard%} a_1, ... a_n {%endard%} corresponding to these variables.
If some argument cannot be matched with a pattern {%ard%} con s_1 ... s_m {%endard%} because it is of the form {%ard%} con' ... {%endard%} for some constructor {%ard%} con' {%endard%} different from {%ard%} con {%endard%},
then the evaluator skips the clause with this patterns and tries the next one.
If some argument cannot be matched with a pattern because it is not a constructor, then {%ard%} E {%endard%} does not reduce.
If none of the clauses match with arguments, then {%ard%} E {%endard%} also does not reduce.
Variables and patterns of the form {%ard%} (s_1, ... s_m) {%endard%} match with any expression.

Let us consider an example.
Let {%ard%} B {%endard%} be a data type with two constructors {%ard%} T {%endard%} and {%ard%} F {%endard%}.
Consider the following function:

{% arend %}
\func g (b b' : B) : Nat
  | T, _ => 0
  | _, T => 1
  | _, _ => 2
{% endarend %}

Let {%ard%} x {%endard%} be a variable and let {%ard%} e {%endard%} be an arbitrary expression.
If the first argument of {%ard%} g a_1 a_2 {%endard%} is {%ard%} T {%endard%}, then the expression reduces to {%ard%} 0 {%endard%}, if it is {%ard%} x {%endard%},
then the expression does not reduce since the first pattern fails to match with {%ard%} x {%endard%}.
If the first argument is {%ard%} F {%endard%}, then the evaluator tries to match the second argument:

{% arend %}
g T e => 0
g x e -- does not reduce
g F T => 1
g F F => 2
g F x -- does not reduce
{% endarend %}

Note that patterns are matched left to right, top to bottom and not the other way around.
This means that even if a funcall matches the first clause, it may not evaluate.
For example, consider the following definition:

{% arend %}
\func \infix 4 < (n m : Nat) : Bool
  | _, 0 => false
  | 0, suc _ => true
  | suc n, suc m => n < m
{% endarend %}

The funcall {%ard%} n < 0 {%endard%} does not evaluate since it matches the first argument first, but funcalls {%ard%} 0 < 0 {%endard%} and {%ard%} suc n < 0 {%endard%} both evaluate to {%ard%} false {%endard%}.

Sometimes you need to write a clause in which one of the parameters is a data type without constructors.
You can write pattern {%ard%} () {%endard%} which is called in this case _the absurd pattern_.
In this case, you must omit the right hand side of the clause.
For example, to define a function from the empty data type you can write:

{% arend %}
\data Empty

\func absurd {A : \Type} (e : Empty) : A
  | ()
{% endarend %}

You can often (but not always) omit the clause with an abusrd pattern completely.
For example, you can define function {%ard%} absurd {%endard%} as follows:

{% arend %}
\func absurd {A : \Type} (e : Empty) : A
{% endarend %}

## Elim

It is often true that one only needs to pattern match on a single parameter of a function (or a few parameters), but the function has much more parameters.
Then we need to repeat parameters on which we do not pattern match in each clause, which is inconvenient.
In this case, we can use the {%ard%} \elim {%endard%} construction:

{% arend %}
\func f (x_1 : A_1) ... (x_n : A_n) : R \elim x_{i_1}, ... x_{i_m}
  | p^1_1, ... p^1_m => e_1
  ...
  | p^k_1, ... p^k_m => e_k
{% endarend %}

where i\_1, ... i\_m are integers such that 1 ≤ i\_1 < ... < i\_m ≤ n.
In this case, parameters {%ard%} x_{i_1}, ... x_{i_m} {%endard%} are _eliminated_ and are not visible in expressions {%ard%} e_1, ... e_k {%endard%}.
Other parameters of {%ard%} f {%endard%} are still visible in these expressions.
Note that it does not matter whether a parameter {%ard%} x_i {%endard%} is explicit or implicit when it is eliminated, the corresponding pattern is always explicit.

As an example, consider the following function which chooses one of its arguments depending on the value of its other argument:

{% arend %}
\func if (b : B) (t e : X) : X \elim b
  | T => t
  | F => e
{% endarend %}

## Recursive functions

Functions defined by pattern matching can be recursive.
That is, if {%ard%} f {%endard%} is a function as described above, then a reference to {%ard%} f {%endard%} may occur inside expressions {%ard%} e_1, ... e_k {%endard%}.
Every function in Arend is a total function.
Thus, not every recursive definition is allowed.
In order for such a definition to be valid, the recursion must be _structural_.
This means that in a definition of {%ard%} f {%endard%} by pattern matching the arguments to recursive calls of {%ard%} f {%endard%} must be
subpatterns of the patterns for the arguments of {%ard%} f {%endard%}.

Functions can also be mutually recursive.
That is, we can have several functions which refer to each other.
In this case, there must be a linear order on the set of these functions {%ard%} f_1, ... f_n {%endard%} such that the signature of {%ard%} f_i {%endard%} refers only to previous functions.
The bodies of the functions may refer to each other as long as the whole recursive system is structural.

## Copattern matching

If the result type of a function is a [record](records) or a [class](classes),
then a function can also be defined by _copattern matching_, which has the following syntax:

{% arend %}
\func f (x_1 : A_1) ... (x_n : A_n) : C \cowith
  | coclause_1
  ...
  | coclause_k
{% endarend %}

where a _coclause_ is a pair consisting of a field {%ard%} g {%endard%} of {%ard%} C {%endard%} and an expression {%ard%} e {%endard%} written {%ard%} g => e {%endard%}.
Such a function has the same semantics as a definition of an instance, that is it is equivalent to the following definition:

{% arend %}
\func f (x_1 : A_1) ... (x_n : A_n) => \new C {
  | coclause_1
  ...
  | coclause_k
}
{% endarend %}

See [Class extensions](../expressions/class-ext) for the description of the involved constructions.

## Lemmas

A _lemma_ is a function, the result type of which is a proposition and the body is considered to be a proof 
without computational content, and, thus, it does not evaluate.
To define a lemma use the keyword {%ard%} \lemma {%endard%} instead of {%ard%} \func {%endard%}.
If the result type of a lemma does not belong to {%ard%} \Prop {%endard%}, but is provably a proposition, you can use the keywords [\level](level/#level-of-a-type) to define a lemma with this result type.
The fact that lemmas do not evaluate may greatly improve performance of typechecking if their proofs are too lengthy.
