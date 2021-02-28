---
title: \module Algebra.Meta
---

# equation

{%ard%} equation a_1 ... a_n {%endard%} proves an equation {%ard%} a_0 = a_{n+1} {%endard%} using {%ard%} a_1, ... a_n {%endard%} as intermediate steps.
A proof of {%ard%} a_i = a_{i+1} {%endard%} can be specified as implicit arguments between them.
{%ard%} using {%endard%}, {%ard%} usingOnly {%endard%}, and {%ard%} hiding {%endard%} with a single argument can be used instead of a proof to control the context.
The first implicit argument can be either a universe or a subclass of either {%ard%} Monoid {%endard%}, {%ard%} AddMonoid {%endard%}, or {%ard%} Order.Lattice.Bounded.MeetSemilattice {%endard%}.
In the former case, the meta will prove an equality in a type without using any additional structure on it.
In the latter case, the meta will prove an equality using only structure available in the specified class.

# cong

This meta implements the congruence closure algorithm.
For example, given assumptions {%ard%} x = x' {%endard%} and {%ard%} y = y' {%endard%}, it can prove {%ard%} f x y = f x' y' {%endard%}.
