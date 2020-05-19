---
title: Inductive types
---

Inductive and [higher inductive](hits) types are represented by data definitions.
The basic syntax of a data definition looks like this:

{% arend %}
\data D p_1 ... p_n
  | con_1 p^1_1 ... p^1_{k_1}
  ...
  | con_m p^m_1 ... p^m_{k_m}
{% endarend %}

where {%ard%} p_1, ... p_n {%endard%} and {%ard%} p^1_1, ... p^m_{k_m} {%endard%} are either named or unnamed [parameters](parameters).
There are several extensions of this syntax which are discussed further in this module and in the module on [HITs](hits).
Each row {%ard%} con_i p^i_1 ... p^i_{k_i} {%endard%} defines a constructor {%ard%} con_i {%endard%} with the specified parameters.
Parameters {%ard%} p_1, ... p_n {%endard%} are parameters of the data type {%ard%} D {%endard%}, but they also become implicit parameters of
the constructors.

Let {%ard%} A, ... F {%endard%} be some types and let {%ard%} a {%endard%}, ... {%ard%} f {%endard%} be terms of the corresponding types.
Consider the following example:

{% arend %}
\data Data A B
  | cons {C} D E
  | cons'

\func s1 => Data a b
\func s2 => cons d e
\func s2' => cons {a} d e
\func s2'' => cons {a} {b} {c} d e
\func s3 => cons'
\func s3' => cons' {a}
\func s3'' => cons' {a} {b}
{% endarend %}

Constructor {%ard%} cons {%endard%} has three implicit parameters of types {%ard%} A {%endard%}, {%ard%} B {%endard%}, and {%ard%} C {%endard%} and two explicit parameters of types {%ard%} D {%endard%} and {%ard%} E {%endard%}.
Constructor {%ard%} cons' {%endard%} has only two implicit parameters of types {%ard%} A {%endard%} and {%ard%} B {%endard%}.

The type of a [defcall](../expressions#defcalls) {%ard%} con_i {a_1} ... {a_n} b_1 ... b_{k_i} {%endard%} is {%ard%} D a_1 ... a_n {%endard%}.
The type of a defcall {%ard%} D a_1 ... a_n {%endard%} is of the form [\h-Type p](../expressions/universes).
Levels {%ard%} h {%endard%} and {%ard%} p {%endard%} are inferred automatically and may depend on levels of {%ard%} a_1, ..., a_n {%endard%}.
Alternatively, these levels can be fixed and specified explicitly in the definition of a data type:

{% arend %}
\data D p_1 ... p_n : \h-Type p
  | con_1 p^1_1 ... p^1_{k_1}
  ...
  | con_m p^m_1 ... p^m_{k_m}
{% endarend %}

If the actual type of {%ard%} D {%endard%} does not always fit into the specified levels, the typechecker will generate an error message.

Constructors belong to the [module](modules) associated to the data definition, but they are also visible in the module in which the data type is defined:

{% arend %}
\data D | con1 | con2

\func f => con1
\func g => con2
\func f' => D.con1
\func g' => D.con2
{% endarend %}

In the example above, we defined a data type {%ard%} D {%endard%} with two constructors {%ard%} con1 {%endard%} and {%ard%} con2 {%endard%}.
Functions {%ard%} f {%endard%} and {%ard%} f' {%endard%} (as well as {%ard%} g {%endard%} and {%ard%} g' {%endard%}) are equivalent.

## Inductive definitions

A data definition can be recursive, that is {%ard%} D {%endard%} may appear in parameters {%ard%} p^1\_1, ... p^m_{k_m} {%endard%} (but not in {%ard%} p_1, ... p_n {%endard%}).
Such recursive definitions are called _inductive data types_.
There is one restriction for such definitions: recursive calls to {%ard%} D {%endard%} may occur only in _strictly positive_ positions.
The set of strictly positive positions is defined inductively:

* {%ard%} D {%endard%} occurs only in strictly positive positions in {%ard%} D a_1 ... a_n {%endard%} if it does not occur in {%ard%} a_1, ... a_n {%endard%}.
* {%ard%} D {%endard%} occurs only in strictly positive positions in {%ard%} \Pi (x : A) -> B {%endard%} if it occurs only in strictly positive positions in {%ard%} B {%endard%} and does not occur in {%ard%} A {%endard%}.
* {%ard%} D {%endard%} occurs only in strictly positive positions in {%ard%} Path (\lam i => B) b b' {%endard%} if it occurs only in strictly positive positions in {%ard%} B {%endard%} and does not occur in {%ard%} b {%endard%} and {%ard%} b' {%endard%}.
* {%ard%} D {%endard%} occurs only in strictly positive positions in any other expression if it does not occur in it.

## Truncation

Data types can be truncated to a specified homotopy level, which is less than its actual level.
This is done by specifying explicitly the type of a data definition and writing the keyword {%ard%} \truncated {%endard%} before the definition:

{% arend %}
\truncated \data D p_1 ... p_n : \h-Type p
  | con_1 p^1_1 ... p^1_{k_1}
  ...
  | con_m p^m_1 ... p^m_{k_m}
{% endarend %}

If the actual predicative level of {%ard%} D {%endard%} is greater than {%ard%} p {%endard%}, the typechecker will generate an error message, whereas {%ard%} h {%endard%} can be any number.
Such a data type can be eliminated only into types of the same homotopy level.
Consider the following example:

{% arend %}
\truncated \data Exists (A : \Type) (B : A -> \Type) : \Prop
  | witness (a : A) (B a)

{-
-- This function will not typecheck.
\func extract (p : Exists Nat (\lam n => n = 3)) : Nat
  | witness a b => a
-}

\func existsSuc (p : Exists Nat (\lam n => n = 3)) : Exists Nat (\lam n => suc n = 4)
  | witness n p => witness (suc n) (path (\lam i => suc (p @ i)))


\func existsEq (p : Exists Nat (\lam n => n = 3)) : 0 = 0
  | witness n p => path (\lam _ => 0)
{% endarend %}

The data type {%ard%} Exists {%endard%} defines a proposition of the form 'There is an {%ard%} a : A {%endard%} such that {%ard%} B a {%endard%}'.
Note that a function like {%ard%} extract {%endard%}, which extracts {%ard%} n : Nat {%endard%} out of a proof of {%ard%} Exists Nat (\lam n => n = 3) {%endard%},
is not valid as its result type {%ard%} Nat {%endard%} is of homotopy level of a set (h = 0), which is greater than the homotopy level of a proposition (h = -1).
Two other functions {%ard%} existsSuc {%endard%} and {%ard%} existsEq {%endard%} in the example above are correct as 
their result types, {%ard%} Exists Nat (\lam n => suc n = 4) {%endard%} and {%ard%} 0 = 0 {%endard%} respectively, are propositions.

If the universe of the resulting type is greater than the universe of the data type, it is still possible to define a function by pattern matching on it if the resulting type is _provably_ belongs to the universe of the data type.
This can be done with keyword [\level](level#level-of-a-type).
In this case, the function should be declared as [\sfunc](functions#sfunc) since truncated data types are [squashed](level#squashed-data-types).

A truncated data type is (provably) equivalent to the truncation of the untruncated version of this data type.
Thus, this is simply a syntactic sugar that allows to define functions over a truncated data type more easily.

## Induction-induction and induction-recursion

Two or more data types can be mutually recursive.
This is called _induction-induction_.
Just as simply inductive definitions, inductive-inductive definitions also must satisfy a strict positivity condition.
Namely, recursive calls to the definition itself and to other recursive definitions may occur only in strictly positive
positions.

Data types may also be mutually recursive with functions.
This is called _induction-recursion_.
Strict positivity and termination checkers work as usual for such definitions.

## Varying number of constructors

Sometimes there might be a need to define a data type, which has different constructors depending on its parameters.
The classical example is the data type of lists of fixed length.
The data type {%ard%} Vec A 0 {%endard%} has only one constructor {%ard%} nil {%endard%}, the empty list.
The data type {%ard%} Vec A (suc n) {%endard%} also has one constructor {%ard%} cons {%endard%}, a non-empty list.
Such a data type can be defined by 'pattern matching':

{% arend %}
\data Vec (A : \Type) (n : Nat) \elim n
  | 0 => nil
  | suc n => cons A (Vec A n)
{% endarend %}

The general syntax is similar to the syntax of functions defined by [pattern matching](functions#pattern-matching).
Either {%ard%} \elim vars {%endard%} or {%ard%} \with {%endard%} constructs can be used with the only difference that 
{%ard%} \elim vars {%endard%} allows to match on a proper subset of parameters of data type.

{% arend %}
\data D p_1 ... p_n \with
  | t^1_1, ... t^1_n => con_1 p^1_1 ... p^1_{k_1}
  ...
  | t^m_1, ... t^m_n => con_m p^m_1 ... p^m_{k_m}
{% endarend %}

Each clause starts a list of patterns, followed by {%ard%} => {%endard%}, followed by a constructor definition.
The order of clauses does not matter.
If a clause matches the arguments of a defcall {%ard%} D a_1 ... a_n {%endard%}, then the corresponding constructor is added to this data type.
For example, one can define the following data type:

{% arend %}
\data Bool | true | false

\data T (b : Bool) \with
  | true => con1
  | true => con2
{% endarend %}

Data type {%ard%} T true {%endard%} has two constructors: {%ard%} con1 {%endard%} and {%ard%} con2 {%endard%}.
Data type {%ard%} T false {%endard%} is empty.
It is also possible to define several constructors in a single clause as follows:

{% arend %}
\data T (b : Bool) \with
  | true => {
    | con1
    | con2
  }
{% endarend %}

This definition is equivalent to the previous one.

## Constructor synonyms

A constructor synonym is a function defined with keyword {%ard%} \cons {%endard%}.
Such a function cannot be defined by pattern matching and it must consists only of constructors of data types.
It can be used in patterns as a synonym for its right hand side.
