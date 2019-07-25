---
title: Class extensions
toc: false
---

A class extension is an expression of the form {%ard%} C { | f_1 => e_1 ... | f_n => e_n } {%endard%}, where {%ard%} C {%endard%} is a record,
{%ard%} f_1, ... f_n {%endard%} are its fields of types {%ard%} A_1, ... A_n {%endard%} respectively, and {%ard%} e_1, ... e_n {%endard%} are expressions 
such that {%ard%} e_i : A_i[e_1/f_1, ... e_n/f_n] {%endard%}.
Note that {%ard%} A_i {%endard%} cannot depend on any field except for {%ard%} f_1, ... f_n {%endard%}.
An expression of the form {%ard%} C e_1 ... e_n {%endard%} is equivalent to {%ard%} C { | f_1 => e_1 ... | f_n => e_n } {%endard%}, where {%ard%} f_1, ... f_n {%endard%} is the list of not implemented fields of {%ard%} C {%endard%} in the order of their definition.

The expression {%ard%} C {} {%endard%} is equivalent to {%ard%} C {%endard%}.
An expression of the form {%ard%} C { I } {%endard%} is a subtype of {%ard%} C' { I' } {%endard%} if and only if {%ard%} C {%endard%} is a subclass of {%ard%} C' {%endard%} and {%ard%} I' {%endard%} is a subset of {%ard%} I {%endard%}.
The expression {%ard%} \new C { I } {%endard%} is an instance of type {%ard%} C { I } {%endard%}, which is a subtype {%ard%} C {%endard%}.
Thus, you can use this expression to create an element of type {%ard%} C {%endard%}.

## New expression

The expression {%ard%} \new C { I } {%endard%} is correct only if all fields of {%ard%} C {%endard%} are implemented in {%ard%} C { I } {%endard%}, but the typechecker can infer some implementations from the expected type of the expression.
For example, in the following code we do not have to implement field {%ard%} x {%endard%} in the {%ard%} \new {%endard%} expression explicitly since {%ard%} f {%endard%} expects an element of {%ard%} R 0 {%endard%}, so the typechecker knows that {%ard%} x {%endard%} must be equal to {%ard%} 0 {%endard%}.

{% arend %}
\record R (x y : Nat)
\func f (r : R 0) => r.y
\func g => f (\new R { | y => 1 })
{% endarend %}

If {%ard%} c {%endard%} is an instance of a record {%ard%} C {%endard%} with fields {%ard%} f_1, ... f_n {%endard%}, then the expression {%ard%} \new c {%endard%} is equivalent to {%ard%} \new C { | f_1 => c.f_1 ... | f_n => c.f_n } {%endard%}.
More generally, the expression {%ard%} \new c { | f_{i_1} => e_1 ... | f_{i_k} => e_k } {%endard%} is equivalent to {%ard%} \new c {%endard%} in which {%ard%} c.f_{i_j} {%endard%} is replaced with {%ard%} e_j {%endard%}.
