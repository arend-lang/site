---
title: Expressions
---

An expression denotes a value which may depend on some variables.
The basic example of an expression is simply a variable {%ard%} x {%endard%}.
Of course, {%ard%} x {%endard%} must be defined somewhere in order for such an expression to make sense.
It can be either a parameter (of a [definition](../definitions/parameters), or a [lambda expression](pi), or a [pi expression](pi), or a [sigma expression](sigma)),
a variable defined in a [let expression](let), or a variable defined in a [pattern](../definitions/functions/#pattern-matching).

If {%ard%} e, e_1, ... e_n {%endard%} are expressions and {%ard%} x_1, ... x_n {%endard%} are variables, then we will write {%ard%} e[e_1/x_1, ... e_n/x_n] {%endard%} for the _substitution_ operation.
This is a meta-operation, namely, it is a function on the set of expressions of the language and not an expression itself.
The expression {%ard%} e[e_1/x_1, ... e_n/x_n] {%endard%} is simply {%ard%} e {%endard%} in which every occurrence of each of the variables {%ard%} x_i {%endard%} is replaced with the expression {%ard%} e_i {%endard%}.

## Evaluation

There is a binary relation {%ard%} => {%endard%} on the set of expressions called the _reduction relation_.
If {%ard%} e_1 => ... => e_n {%endard%}, we will say that {%ard%} e_1 {%endard%} _reduces_ to {%ard%} e_n {%endard%}.
If there is no {%ard%} e' {%endard%} such that {%ard%} e => e' {%endard%}, we will say that {%ard%} e {%endard%} is a _normal form_.
If {%ard%} e {%endard%} reduces to {%ard%} e' {%endard%} and {%ard%} e' {%endard%} is a normal form, we will say that {%ard%} e' {%endard%} is a _normal form_ of {%ard%} e {%endard%} and that {%ard%} e {%endard%} _evaluates_ to {%ard%} e' {%endard%}.
Every expression has a unique normal form.

The relation {%ard%} => {%endard%} is a meta-relation on the set of expressions of the language, that is you cannot refer to it explicitly in the language.
This relation is used by the typechecker to compare expressions.
The typechecker never compares expressions directly.
To compare expressions {%ard%} e_1 {%endard%} and {%ard%} e_2 {%endard%}, it first evaluates their normal forms and then compares them.
Since normal forms always exist, the comparison algorithm always terminates, but it is easy to write an expression that does not evaluate in any reasonable time.

The reflexive, symmetric, and transitive closure of {%ard%} => {%endard%} is denoted by {%ard%} == {%endard%} and called the _computational equality_.
We will often call terms {%ard%} t_1 {%endard%} and {%ard%} t_2 {%endard%} such that {%ard%} t_1 == t_2 {%endard%} simply _equivalent_.

## Types

Every expression has a type. The notation {%ard%} e : E {%endard%} is used for the judgement that an expression {%ard%} e {%endard%} has type {%ard%} E {%endard%}.

A type is an expression which has type {%ard%} \Type {%endard%}.
The expression {%ard%} \Type {%endard%} is discussed in [Universes](universes).

Every variable has a type which is the one specified when the variable is defined or, if it is not specified, the one that can be inferred.
An expression of the form {%ard%} x {%endard%} has the type of the variable {%ard%} x {%endard%}.

The type of an expression can usually be inferred automatically, but in rare cases, when it cannot be inferred, or
just for the sake of readability it can also be specified explicitly.
An expression of the form {%ard%} (e : E) {%endard%} (parentheses are necessary) is equivalent to {%ard%} e {%endard%}, but also has an explicit type
annotation.
In this expression, {%ard%} e {%endard%} must have type {%ard%} E {%endard%} and the type of the whole expression is also {%ard%} E {%endard%} (since it is equivalent to {%ard%} e {%endard%}).

## Defcalls

A _defcall_ is an expression of the form {%ard%} f a_1 ... a_n {%endard%}, where {%ard%} f {%endard%} is the name of a definition with n parameters
and {%ard%} a_1, ..., a_n {%endard%} are expressions. Note that classes and records do not have parameters and any defcall in this
case is of the form {%ard%} f {%endard%}. Expression of the form {%ard%} f a_1 ... a_n {%endard%}, where {%ard%} f {%endard%} is the name of a class, are _class
extensions_, see [Class extensions](class-ext) for details.

Defcall expressions have the following properties: 

* If {%ard%} f {%endard%} is a definition with parameters {%ard%} x_1, ... x_n {%endard%} and the result type {%ard%} R {%endard%}, then the type of a 
defcall {%ard%} f a_1 ... a_n {%endard%} is {%ard%} R[a_1/x_1, ... a_n/x_n] {%endard%}.

* If {%ard%} f {%endard%} is either a class, a record, a data type, a constructor without conditions, an instance, or a
function defined by copattern matching, then {%ard%} f a_1 ... a_n {%endard%} is a normal form whenever {%ard%} a_1, ... a_n {%endard%} are.

* If {%ard%} f {%endard%} is a function defined as {%ard%} \func f (x_1 : A_1) ... (x_n : A_n) => e {%endard%}, then {%ard%} f a_1 ... a_n {%endard%} reduces
to {%ard%} e[a_1/x_1, ... a_n/x_n] {%endard%}. If {%ard%} f {%endard%} is a function defined by pattern matching or a constructor with conditions, then the evaluation of
defcalls {%ard%} f a_1 ... a_n {%endard%} is described in [Functions](../definitions/functions/#pattern-matching).
If {%ard%} f {%endard%} is an instance or a function defined by copattern matching, then the evaluation of defcalls {%ard%} f a_1 ... a_n {%endard%} is described in [Classes](../definitions/classes/#instances).

* If {%ard%} f {%endard%} has n parameters and k < n, an expression of the form {%ard%} f a_1 ... a_k {%endard%} is also valid and is equivalent to {%ard%} \lam a_{k+1} ... a_n => f a_1 ... a_n {%endard%}.
