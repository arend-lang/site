---
title: Standard Metas for Equality
nav: metas-equality
---

The source code for this module: [PartI/MetasEquality.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/MetasEquality.ard) \\
The source code for the exercises: [PartI/MetasEqualityEx.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/Exercises/MetasEqualityEx.ard)
{: .notice--success}

Up to this point, equality proofs were assembled from the kernel primitives {%ard%}idp{%endard%}, {%ard%}pmap{%endard%}, {%ard%}transport{%endard%}, {%ard%}inv{%endard%}, and {%ard%}*>{%endard%}. As proofs grow these primitives become tedious to thread by hand. The Arend standard library ships *metas* — macros that expand into ordinary kernel terms post-elaboration. They are not a separate logic; they are surface syntax for the same {%ard%}transport{%endard%}/{%ard%}pmap{%endard%} machinery the previous chapters introduced.

In this chapter we introduce the metas most useful for equality proofs: {%ard%}rewrite{%endard%}, {%ard%}rewriteI{%endard%}, {%ard%}run{%endard%}, {%ard%}in{%endard%}, and {%ard%}at{%endard%}. We also cover the language features {%ard%}rewrite{%endard%} relies on: partial application of functions and *infix sections*. The full reference for each meta lives at [Standard Metas](/documentation/standard-tactics).

Metas are organized into several modules. Throughout this chapter we will assume the following imports:

{%arend%}
\import Paths        -- inv, *>, transport, transportInv, idp, pmap
\import Paths.Meta   -- rewrite, rewriteI, ext, simp_coe, simplify
\import Meta         -- run, in, at, cases, mcases, unfold, ...
\import Function.Meta -- $, #, repeat
{%endarend%}

# rewrite

{%ard%}rewrite p t{%endard%}, where {%ard%}p : a = b{%endard%}, looks at the *expected* type, replaces every occurrence of {%ard%}a{%endard%} with {%ard%}b{%endard%}, and uses {%ard%}t{%endard%} as a proof of the rewritten type. It is exactly sugar for {%ard%}transportInv{%endard%}:

{%arend%}
-- These two definitions are equivalent:
\func test (n m : Nat) (p : n = m) (q : m = 0) : n = 0
  => rewrite p q

\func test' (n m : Nat) (p : n = m) (q : m = 0) : n = 0
  => transportInv (\lam x => x = 0) p q
{%endarend%}

The companion meta {%ard%}rewriteI p{%endard%} is shorthand for {%ard%}rewrite (inv p){%endard%}: it rewrites in the opposite direction. Use {%ard%}rewriteI{%endard%} when the equation you have is "wrong-way-round" relative to the goal.

{%arend%}
\func test1 (a : Nat) (p : a = 0) : a Nat.+ a = 0
  => rewrite p idp

\func test2 (a : Nat) (p : 0 = a) : a Nat.+ a = 0
  => rewriteI p idp
{%endarend%}

The associativity of {%ard%}+{%endard%} from [Indexed Data Types](datanproofs) compresses noticeably with {%ard%}rewrite{%endard%}:

{%arend%}
\open Nat(+)

\lemma +-assoc (a b c : Nat) : a + b + c = a + (b + c) \elim c
  | 0 => idp
  | suc c => rewrite (+-assoc a b c) idp
{%endarend%}

The seed {%ard%}idp{%endard%} proves the goal *after* the rewrite has been applied; once both sides have been normalized to the same shape, reflexivity finishes the proof.

# Selective occurrences

When the LHS appears multiple times in the goal, rewriting *all* occurrences is sometimes wrong. {%ard%}rewrite {n_1, n_2, ...} p t{%endard%} rewrites only the listed occurrences (counting in left-to-right order, after each replacement). For example:

{%arend%}
\func test {x : Nat} (p : suc x = suc (suc x))
         : suc (suc x) = x Nat.+ 3
  => rewrite {1} p idp
{%endarend%}

Here {%ard%}suc x{%endard%} appears multiple times in the goal after normalization; without {%ard%}{1}{%endard%} the rewrite would chase its own tail.

# Partial application and infix sections

Arend allows partial application of any function or infix operator. Two forms appear constantly in proofs assembled with metas:

* {%ard%}pmap suc{%endard%} is a value of type {%ard%}{a a' : Nat} -> a = a' -> suc a = suc a'{%endard%} — a unary function that consumes a path. Perfectly usable as a building block.
* For infix operators like {%ard%}*>{%endard%}, the expressions {%ard%}(p *>){%endard%} and {%ard%}(`*> q){%endard%} are *sections*: the former precomposes with {%ard%}p{%endard%} on the left, the latter composes with {%ard%}q{%endard%} on the right. Each is a unary function on paths.
* {%ard%}__{%endard%} (double underscore) is the explicit anonymous-section placeholder: {%ard%}__ + 1{%endard%}, {%ard%}f __ x{%endard%}, etc.

{%arend%}
\func ex-pmap (n m : Nat) (p : n = m) : suc n = suc m
  => pmap suc p

\func ex-section-left (a b c : Nat) (p : a = b) (q : b = c) : a = c
  => (p *>) q   -- equivalent to p *> q

\func ex-double-underscore : Nat -> Nat
  => __ Nat.+ 1
{%endarend%}

These are language features, not meta features — but they are what makes the next section's {%ard%}run{%endard%}-blocks readable.

# run for chaining

Nested {%ard%}rewrite{%endard%} calls grow ugly:

{%arend%}
-- Hard to scan:
rewrite p (rewrite q (rewrite r idp))
{%endarend%}

The {%ard%}run{%endard%} meta lets you write the same chain top-to-bottom as a comma-separated list:

{%arend%}
\func ex-run {A : \Type} (a b c d : A) (p : a = b) (q : b = c) (r : c = d) : a = d
  => run {
    rewrite p,
    rewrite q,
    rewrite r,
    idp
  }
{%endarend%}

The semantics: {%ard%}run { f_1, f_2, ..., f_n, t }{%endard%} expands to {%ard%}f_1 (f_2 (... (f_n t))){%endard%}. The last entry is the seed (the innermost proof); each entry above is a unary function applied to the chain so far.

A {%ard%}run{%endard%}-block can mix {%ard%}rewrite{%endard%}, {%ard%}pmap f{%endard%}, infix sections like {%ard%}p *>{%endard%}, and any other unary function on proofs. For occasional advanced uses, {%ard%}run{%endard%} also accepts entries of the form {%ard%}\let | x => e \in {}{%endard%} or {%ard%}\lam x => {}{%endard%} (with empty bodies); these wrap the rest of the chain in a let-binding or a lambda respectively.

{%ard%}rewrite{%endard%} itself also accepts a tuple of paths in place of a single path: {%ard%}rewrite (p_1, p_2, ..., p_n) t{%endard%} is equivalent to {%ard%}rewrite p_1 (rewrite p_2 (... (rewrite p_n t))){%endard%}. Each {%ard%}p_i{%endard%} is applied in left-to-right order, with the previous rewrites already reflected in the goal by the time the next one runs. This is a more compact alternative to {%ard%}run{%endard%} when every step is itself a {%ard%}rewrite{%endard%}:

{%arend%}
\func ex-rewrite-tuple {A : \Type} (a b c d : A) (p : a = b) (q : b = c) (r : c = d) : a = d
  => rewrite (p, q, r) idp
{%endarend%}

Reach for {%ard%}run{%endard%} when the chain mixes different metas; reach for the tuple form when it is purely rewrites.

# in: applying a meta to a value

{%ard%}f in x{%endard%} runs {%ard%}f x{%endard%} but with one important subtlety: it discards the surrounding *expected* type. Internally, {%ard%}in{%endard%} elaborates to {%ard%}\let r => f x \in r{%endard%}, and that {%ard%}\let{%endard%} is typechecked without the goal's type information flowing in.

For most metas this difference is invisible. For {%ard%}rewrite{%endard%}, which inspects the expected type to decide *what* to rewrite, the difference is observable:

{%arend%}
-- Direct application uses the expected type:
\func test1 (x y : Nat) (p : x = zero) (q : zero = y) : x = y
  => rewrite p q   -- rewrites x → zero in the goal x = y, giving zero = y; matches q

-- `in` uses t's type instead:
\func test2 (x y : Nat) (p : zero = x) (q : zero = y) : x = y
  => rewrite p in q   -- rewrites zero → x in q's type zero = y, giving x = y
{%endarend%}

Use {%ard%}f in x{%endard%} when you want the meta to operate on the *value's* type rather than the goal — for example, when there is no annotated result type, or when you want a "rewrite in the hypothesis itself" effect on the seed.

{%ard%}in{%endard%} chains: {%ard%}(f_1, f_2, ..., f_n) in x{%endard%} ≡ {%ard%}f_1 (f_2 (... (f_n x))){%endard%}. Each step runs without an expected type.

{%ard%}in{%endard%} has loose precedence (priority 1, right-associative). To apply the result of {%ard%}f in x{%endard%} to further arguments, parens are required:

{%arend%}
(simp_coe in t) b      -- applies simp_coe in t, then applies result to b
-- simp_coe in t b     -- parses as simp_coe in (t b) — different proof
{%endarend%}

# at: modifying a hypothesis

{%ard%}f at h{%endard%} shadows the local binding {%ard%}h{%endard%} with {%ard%}f h{%endard%} for the rest of the expression — Arend's analogue of "rewrite in a hypothesis." It is the right tool when a hypothesis needs reshaping before it can be used.

There are three equivalent surface forms:

{%arend%}
\func test1 (x : Nat) (p : x = zero) (q : x = suc zero) : Empty
  => (rewrite p at q) (\case q \with {})

\func test2 (x : Nat) (p : x = zero) (q : x = suc zero) : Empty
  => rewrite p at q $ \case q \with {}

\func test3 (x : Nat) (p : x = zero) (q : x = suc zero) : Empty
  => run {
    rewrite p at q,
    \case q \with {}
  }
{%endarend%}

After {%ard%}rewrite p at q{%endard%}, the local {%ard%}q{%endard%} has type {%ard%}zero = suc zero{%endard%} instead of {%ard%}x = suc zero{%endard%}. The empty {%ard%}\case{%endard%} then derives {%ard%}Empty{%endard%} from the constructor disjointness of {%ard%}zero{%endard%} and {%ard%}suc zero{%endard%}.

Like {%ard%}in{%endard%}, {%ard%}at{%endard%} accepts a tuple-chaining form:

{%arend%}
\func test {x y : Nat} (p1 : x = zero) (p2 : y = suc zero) (q : x = y) : Empty
  => (rewrite p1, rewrite p2) at q $ \case q \with {}
{%endarend%}

{%ard%}at{%endard%} works on any local binding — function parameters, {%ard%}\let{%endard%}-bindings, and {%ard%}\have{%endard%}-bindings.

# When to use what

| Situation | Use |
|---|---|
| Rewrite in the goal | {%ard%}rewrite p t{%endard%} |
| Rewrite the goal in the opposite direction | {%ard%}rewriteI p t{%endard%} |
| Rewrite when expected type is unknown / use t's type | {%ard%}rewrite p in t{%endard%} |
| Modify a hypothesis | {%ard%}rewrite p at h $ ...{%endard%} |
| Chain several rewrites | {%ard%}run { rewrite p, rewrite q, ..., idp }{%endard%} |
| Multi-step chain with named intermediate values | {%ard%}==<{%endard%} / {%ard%}>=={%endard%} / {%ard%}qed{%endard%}, see [Proofs of Equality](equalityex#equational-reasoning-proof-of-comm-rewritten) |

# Exercises

**Exercise 1:** Reprove {%ard%}+-comm{%endard%} from [Proofs of Equality](equalityex) using only {%ard%}rewrite{%endard%}, {%ard%}rewriteI{%endard%}, and {%ard%}idp{%endard%} — no {%ard%}pmap{%endard%}, no {%ard%}*>{%endard%}, no equational reasoning. Compare the line count.
{: .notice--info}

**Exercise 2:** Predict which of the following typecheck and explain why. Then run them to verify.
{%arend%}
\func test1 (x y : Nat) (p : x = zero) (q : zero = y) : x = y => rewrite p q
\func test2 (x y : Nat) (p : x = zero) (q : zero = y) : x = y => rewrite p in q
\func test3 (x y : Nat) (p : zero = x) (q : zero = y) : x = y => rewrite p q
\func test4 (x y : Nat) (p : zero = x) (q : zero = y) : x = y => rewrite p in q
{%endarend%}
{: .notice--info}

**Exercise 3:** State a lemma where {%ard%}rewrite{%endard%} would replace too many occurrences. Use occurrence selection {%ard%}rewrite {n} p t{%endard%} to make the proof go through.
{: .notice--info}

**Exercise 4:** Take the proof of {%ard%}reverse-isInvolutive{%endard%} from [Indexed Data Types](datanproofs) (which uses {%ard%}rev-isInv{%endard%} and {%ard%}*>{%endard%}-chains in similar style) and rewrite its body as a single {%ard%}run{%endard%}-block.
{: .notice--info}

**Exercise 5:** Given {%ard%}(x : Nat) (p : x = 0) (q : x = 1){%endard%}, prove {%ard%}Empty{%endard%}. Write three solutions: (a) using {%ard%}at{%endard%}, (b) introducing a fresh binding via {%ard%}\have{%endard%}, (c) chaining {%ard%}*>{%endard%}-style with {%ard%}inv{%endard%}.
{: .notice--info}

**Exercise 6:** Use {%ard%}pmap suc at p{%endard%} to convert a hypothesis {%ard%}p : x = 0{%endard%} into {%ard%}p : suc x = 1{%endard%}, then use it to discharge a goal {%ard%}suc x = 1{%endard%}.
{: .notice--info}
