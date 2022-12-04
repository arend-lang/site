---
title: Sigma Types
toc: false
---

A Sigma type is a type of (dependent) tuples.
If {%ard%} p_1, ... p_n {%endard%} are named or unnamed parameters, then {%ard%} \Sigma p_1 ... p_n {%endard%} is also a type.
If {%ard%} A_i {%endard%} has type {%ard%} \Type p_i h_i {%endard%}, then the type of the Sigma type is {%ard%} \Type p_max h_max {%endard%}, where {%ard%} p_max {%endard%} is the maximum
of {%ard%} p_1, ... p_n {%endard%} and {%ard%} h_max {%endard%} is the maximum of {%ard%} h_1, ... h_n {%endard%}.

An expression of the form {%ard%} \Sigma p_1 ... p_n (x_1 ... x_k : A) q_1 ... q_m {%endard%} is equivalent to
{%ard%} \Sigma p_1 ... p_n (x_1 : A) ... (x_k : A) q_1 ... q_m {%endard%}.

If {%ard%} a_i {%endard%} is an expression of type {%ard%} A_i[a_1/x_1, ... a_{i-1}/x_{i-1}] {%endard%}, then {%ard%} (a_1, ... a_n) {%endard%} is an expression of
type {%ard%} \Sigma (x_1 : A_1) ... (x_n : A_n) {%endard%}. 
Note that the typechecker often cannot infer the correct type of such an expression.
If the typechecker does not know it already, it always tries to guess a non-dependent version.
In case the typechecker fails to infer the type, it should be specified explicitly:
{%ard%} ((a_1, ... a_n) : \Sigma (x_1 : A_1) ... (x_n : A_n)) {%endard%}.
You can also explicitly specify the type of each field: {%ard%} (b_1 : B_1, ... b_n : B_n) {%endard%}, however in this case 
{%ard%} B_i {%endard%} cannot refer to previous parameters, therefore this can only be used to define non-dependent Sigma types.

If {%ard%} p {%endard%} is an expression of type {%ard%} \Sigma (x_1 : A_1) ... (x_n : A_n) {%endard%} and 1 ≤ i ≤ n, then {%ard%} p.i {%endard%} is an expression of
type {%ard%} A_i[p.1/x_1, ... p_{i-1}/x_{i-1}] {%endard%}.

An expression of the form {%ard%} (a_1, ... a_n).i {%endard%} reduces to {%ard%} a_i {%endard%}.

An expression of the form {%ard%} (p.1, ... p.n) {%endard%} is equivalent to {%ard%} p {%endard%} (eta equivalence for Sigma types).

A field can be marked as a property with the following syntax: {%ard%} \Sigma p_1 ... (\property p_i) ... p_n {%endard%}.
Properties work just like [record properties](../definitions/records#properties).
That is, the type of a property must live in {%ard%} \Prop {%endard%} and {%ard%} (a_1, ... a_n).i {%endard%} does not evaluate if the i-th field is a property.
