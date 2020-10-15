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
{% endarend %}

It can also be specified with an implicit argument which itself is a contradiction.
Examples:

{% arend %}
\lemma explicitProof (P : \Prop) (e : Empty) : P
  => contradiction {e}

\lemma explicitProof2 (P : \Prop) (e : P -> Not P) (p : P) : Empty
  => contradiction {e}
{% endarend %}
