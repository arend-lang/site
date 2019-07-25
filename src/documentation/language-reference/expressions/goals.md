---
title: Goals
toc: false
---

A _goal_ marks an unfinished expression.
It always produces an error message which contains the expected type of an expression that should replace the goal and
the context of the goal, that is the list of available variables with their types.
A goal is written as {%ard%} {?} {%endard%} or {%ard%} {?id} {%endard%}, where {%ard%} id {%endard%} is any identifier which denotes the name of the goal.
The name of a goal only appears in error messages and does not affect the code in any way.

For example, consider the following code:
{% arend %}
\func f (x y : Nat) (p : x = y) : y = x
  => {?}
{% endarend %}

It will produce the following error message:

{% arend %}
[GOAL] test.ard:1:44:
  Expected type: y = {Nat} x
  Context:
    y : Nat
    x : Nat
    p : x = {Nat} y
  In: {?}
  While processing: f
{% endarend %}

The information in the error message might be especially useful, when the expected type or types of variables are inferred by the typechecker.
