---
title: Let
toc: false
---

Let expressions allow to introduce local variables.
Such expressions have the following syntax:

{% arend %}
\let | p_1 => e_1
     ...
     | p_n => e_n
\in e_{n+1}
{% endarend %}

where {%ard%} p_1, ... p_n {%endard%} are patterns and {%ard%} e_1, ... e_{n+1} {%endard%} are expressions.

Every pattern is either a variable or an expression of the form {%ard%} (p_1', ... p_k') {%endard%},
where {%ard%} p_1', ... p_k' {%endard%} are patterns. This implies that if {%ard%} p_i {%endard%} is a tuple of k subpatterns,
then the type of {%ard%} e_i {%endard%} must be either a k-fold Sigma type or a record with k fields.
Note that because of the eta-equivalence for Sigma types and records the structure of
{%ard%} e_i {%endard%} does not matter: for example, expression {%ard%} \let (x,y) => z \in e {%endard%} evaluates to
{%ard%} e[z.1/x,z.2/y] {%endard%} if type of {%ard%} z {%endard%} is Sigma type (and with fields instead of projections
{%ard%} z.1 {%endard%} and {%ard%} z.2 {%endard%} in case of a record). In general, if pattern {%ard%} p_i {%endard%} contains
variables {%ard%} x_i^1, ... x_i^{n_i} {%endard%} expression 
{%ard%} \let | p_1 => e_1 ... | p_n => e_n \in e {%endard%} evaluates to {%ard%} e[... proj_i^j(e_i)/x_i^j ...] {%endard%},
where {%ard%} proj_i^j {%endard%} is the sequence of projections and field access expressions, corresponding to {%ard%} j {%endard%}-th variable of {%ard%} p_i {%endard%}. 

The expression {%ard%} \let | x_1 => e_1 ... | x_n => e_n \in e {%endard%} has type 
{%ard%} \let | x_1 => e_1 ... | x_n => e_n \in E {%endard%}, where {%ard%} E {%endard%} is the type of {%ard%} e {%endard%}.

The type of {%ard%} e_i {%endard%} can be explicitly specified as follows: {%ard%} | p_i : E_i => e_i {%endard%}.

It is also allowed to write lambda parameters after a pattern if it is a variable.
That is, instead of {%ard%} | x_i => e_i {%endard%}, you can write {%ard%} | x_i p^i_1 ... p^i_{n_i} => e_i {%endard%},
where {%ard%} p^i_1, ... p^i_{n_i} {%endard%} are either variables or named parameters to which {%ard%} e_i {%endard%} can refer.
Such a clause is equivalent to {%ard%} | x_i => \lam p^i_1 ... p^i_{n_i} => e_i {%endard%}.

Let expressions also can be _strict_.
This means that expressions {%ard%} e_1, ... e_n {%endard%} will be evaluated immediately when the let expression is evaluated.
To define a strict let expression, use the keyword {%ard%} \let! {%endard%} instead of {%ard%} \let {%endard%}.
