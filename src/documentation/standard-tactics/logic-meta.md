---
title: \module Logic.Meta
---

# `contradiction`

 [scope-meta]: /documentation/standard-tactics/meta#scope-metas

This meta will try to derive a contradiction from the context if no arguments are specified.
Implicit `using`, `usingOnly` and `hiding` (description of these metas can be found [here][scope-meta]) arguments can be used to modify the context it uses.
Examples (requires arend-lib):

{% arend %}
\import Logic.Meta
\import Logic
\import Meta
\import Order.StrictOrder
\import Set

\lemma equality {x y : Nat} (p : x = y) (q : Not (x = y)) : Empty
  => contradiction

\lemma irreflexivity {A : Set#} {x y : A} (p : x # x) : Empty
  => contradiction

\lemma irreflexivity2 {A : Set#} {x y : A} (p : x # y) (q : x = y) : Empty
  => contradiction

\lemma irreflexivity3 {A : StrictPoset} {x y z : A} (p : x < y) (q : x = z) (s : y = z) : Empty
  => contradiction

\lemma usingTest (P Q : \Prop) (q : Q) (e : P -> Empty) (p : P) : Empty
  => contradiction {usingOnly (e,p)}

\lemma transTest {A : LinearOrder} {x y z u v w : A}
  (p : x < y) (q : y = z) (a : z <= u) (b : u = v) (c : v < w) (d : w <= x)
  : Empty
  => contradiction
{% endarend %}

It can also be specified with an implicit argument which itself is a contradiction.
Examples:

{% arend %}
\lemma explicitProof (P : \Prop) (e : Empty) : P
  => contradiction {e}

\lemma explicitProof2 (P : \Prop) (e : P -> Not P) (p : P) : Empty
  => contradiction {e}
{% endarend %}

# `Exists`

The alias of this meta is `∃`, which is convenient to read.

+ {%ard%} Exists {x y z} B {%endard%} is equivalent to {%ard%} TruncP (\Sigma (x y z : _) B) {%endard%}.
+ {%ard%} Exists (x y z : A) B {%endard%} is equivalent to {%ard%} TruncP (\Sigma (x y z : A) B) {%endard%}.

Examples:

{% arend %}
\lemma test1 : ∃ = (\Sigma) => idp

\lemma test2 : ∃ Nat = TruncP Nat => idp

\lemma test3 : ∃ (x : Nat) (x = 0) = TruncP (\Sigma (x : Nat) (x = 0)) => idp

\lemma test4 : ∃ {x} (x = 0) = TruncP (\Sigma (x : Nat) (x = 0)) => idp

\lemma test5 : ∃ {x y} (x = 0) = TruncP (\Sigma (x y : Nat) (x = 0)) => idp
{% endarend %}

If the argument of `∃` is a predicate, it will be treated as a subset:

{% arend %}
\lemma test7 (P : Nat -> \Type)
  : ∃ P
  = TruncP (\Sigma (x : Nat) (P x))
  => idp

\lemma test8 (P : Nat -> Nat -> \Type)
  : ∃ P
  = TruncP (\Sigma (x y : Nat) (P x y))
  => idp

\lemma test9 (P : Nat -> \Type)
  : ∃ (x : P) (x = x)
  = TruncP (\Sigma (x : Nat) (P x) (x = x))
  => idp

\lemma test10 (P : Nat -> \Type)
  : ∃ (x y : P) (x = y) (y = x)
  = TruncP (\Sigma (x y : Nat) (P x) (P y) (x = y) (y = x))
  => idp

\lemma test11 (P : Nat -> Bool -> Array Nat -> \Type)
  : ∃ ((x,y,z) (a,b,c) : P) (x = a) (y = b) (z = c)
  = TruncP (\Sigma (x a : Nat) (y b : Bool) (z c : Array Nat) (P x y z) (P a b c) (x = a) (y = b) (z = c))
  => idp
{% endarend %}

If the argument of `∃` is an array, it will be treated as a set of its elements:

{% arend %}
\lemma test12 (l : Array Nat)
  : ∃ l
  = TruncP (Fin l.len)
  => idp

\lemma test13 {A : \Type} (y : A) (l : Array A)
  : ∃ (x : l) (x = y)
  = TruncP (\Sigma (j : Fin l.len) (l j = y))
  => idp

\lemma test14 {A : \Type} (l : Array A)
  : ∃ (x y : l) (x = y)
  = TruncP (\Sigma (j j' : Fin l.len) (l j = l j'))
  => idp
{% endarend %}

# `Given`

This meta has the same syntax as `Exists`, but returns an untruncated {%ard%}\Sigma{%endard%}-expression.

{% arend %}
\func sigmaTest : Given (x : Nat) (x = 0) = (\Sigma (x : Nat) (x = 0)) => idp
{% endarend %}

# `Forall`

The alias of this meta is `∀`.
This meta has a similar syntax to `Exists`, but returns a {%ard%}\Pi{%endard%}-expression.

{% arend %}
\lemma piTest1 : ∀ (x y : Nat) (x = y) = (\Pi (x y : Nat) -> x = y) => idp

\lemma piTest2 : ∀ {x y : Nat} (x = y) = (\Pi {x y : Nat} -> x = y) => idp

\lemma piTest3
  : ∀ x y (pos x = y)
  = (\Pi (x : Nat) (y : Int) -> pos x = y)
  => idp

\lemma piTest4
  : ∀ {x y} {z} (pos x = z)
  = (\Pi {x y : Nat} {z : Int} -> pos x = z)
  => idp

\lemma piTest5 (P : Nat -> \Type)
  : ∀ (x y : P) (x = y) (y = x)
  = (\Pi (x y : Nat) (P x) (P y) -> x = y -> y = x)
  => idp

\lemma piTest6 (P : Nat -> \Type)
  : ∀ {x y : P} (x = y) (y = x)
  = (\Pi {x y : Nat} (P x) (P y) -> x = y -> y = x)
  => idp

\lemma piTest7 {A : \Set} (l : Array A)
  : ∀ (x y : l) (x = y) (y = x)
  = (\Pi (j j' : Fin l.len) -> l j = l j' -> l j' = l j)
  => idp

\lemma piTest8 (P : Nat -> Bool -> Array Nat -> \Type)
  : ∀ ((x,y,z) (a,b,c) : P) (x = a) (y = b) (z = c)
  = (\Pi (x a : Nat) (y b : Bool) (z c : Array Nat) -> P x y z -> P a b c -> x = a -> y = b -> z = c)
  => idp
{% endarend %}

# `constructor`

Returns either a tuple, a {%ard%} \new {%endard%} expression, or a single constructor of a data type depending on the expected type.

{% arend %}
\func tuple0 : \Sigma (\Sigma) (\Sigma) => constructor constructor constructor

\func tuple1 : \Sigma Nat Nat => constructor 0 1

\func tuple2 : \Sigma (x : Nat) (p : x = 0) => constructor 0 idp

\func data2 : D => constructor 0 1 2
  \where
    \data D | con {x : Nat} (y z : Nat)

\record R (x : Nat) (y : Nat) (z : Nat)

\func class1 : R => constructor 1 2 3

\func class2 : R 1 => constructor 2 3
{% endarend %}
