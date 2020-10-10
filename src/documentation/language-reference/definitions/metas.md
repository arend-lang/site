---
title: Meta definitions
toc: false
---

Meta definitions are usually defined externally in Java code, but it is also possible to describe simple metas directly in Arend code.
The general syntax of such a meta looks like this:
{%arend%}
\meta f x_1 ... x_n => e
{%endarend%}
where {%ard%} f {%endard%} is a name, {%ard%} x_1, ... x_n {%endard%} are names of parameters, and {%ard%} e {%endard%} is an expression.
This expression is typechecked only when the meta is invoked.
It expects {%ard%} n {%endard%} arguments and {%ard%} f e_1 ... e_n {%endard%} is replaced with {%ard%} e[e_1/x_1, ... e_n/x_n] {%endard%} and this expression is typechecked instead of the original application.
