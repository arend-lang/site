---
title: Type synonyms
toc: false
---

A type synonym is a [function](functions) that returns a type and does not evaluate.
To define a type synonym, use {%ard%} \type {%endard%} keywork:

{% arend %}
\type T p_1 ... p_n => E
{% endarend %}

For example, we can define the type of pairs as follows

{% arend %}
\type Pair (A : \Type) => \Sigma A A
{% endarend %}

This differs from the analogous function definition because {%ard%} Pair A {%endard%} and {%ard%} \Sigma A A {%endard%} are not computationally equivalent.
Nevertheless, these types are equivalent.
The coercion between them is implicit:

{% arend %}
\func coerceFrom (p : Pair Nat) : \Sigma Nat Nat => p
\func coerceTo (p : \Sigma Nat Nat) : Pair Nat => p
{% endarend %}
