---
title: Case
toc: false
---

The basic syntax of case expressions looks like this:

{% arend %}
\case e_1, ... e_n \with {
  | p_1^1, ... p_n^1 => d_1
  ...
  | p_1^k, ... p_n^k => d_k
}
{% endarend %}

where {%ard%} e_1, ... e_n {%endard%} and {%ard%} d_1, ... d_k {%endard%} are expressions and {%ard%} p_1^1, ... p_n^k {%endard%} are patterns.
Such an expression reduces in the same way as functions defined by pattern matching (see [Functions](../definitions/functions#pattern-matching)).
If the typechecker does not know the type of a case expression, it must be specified explicitly:
{% arend %}
\case e_1, ... e_n \return T \with { ... }
{% endarend %}

The general syntax of case expressions looks like this:
{% arend %}
\case e_1 \as x_1 : E_1, ... e_n \as x_n : E_n \return T \with { ... }
{% endarend %}
where {%ard%} x_1, ... x_n {%endard%} are variables and {%ard%} E_1, ... E_n {%endard%} are expressions.
The parts {%ard%} \as x_i {%endard%} and {%ard%} : E_i {%endard%} can be omitted.
Expressions {%ard%} E_i {%endard%} can refer to {%ard%} x_1, ... x_{i-1} {%endard%} and expression {%ard%} T {%endard%} can refer to {%ard%} x_1, ... x_n {%endard%}.
In this case, {%ard%} e_i {%endard%} must have type {%ard%} E_i[e_1/x_1, ... e_{i-1}/x_{i-1}] {%endard%}.
The type of the case expression is {%ard%} T[e_1/x_1, ... e_n/x_n] {%endard%}.

## \scase

Expression {%ard%} \scase {%endard%} is related to {%ard%} \case {%endard%} in the same way as [\sfunc](/documentation/language-reference/definitions/functions#sfunc) is related to {%ard%} \func {%endard%}.
That is, expressions of the form {%ard%} \scase e_1, ... e_n \with { ... } {%endard%} never evaluate.
To evaluate such an expression, you need to use keyword {%ard%} \eval {%endard%} before it.
Similarly, {%ard%} \peval \scase e_1, ... e_n \with { ... } {%endard%} has type {%ard%} \scase e_1, ... e_n \with { ... } = \eval \scase e_1, ... e_n \with { ... } {%endard%}.
