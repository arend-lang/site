---
title: Algebraic Metas
nav: metas-algebra
---

The source code for this module: [PartI/MetasAlgebra.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/MetasAlgebra.ard) \\
The source code for the exercises: [PartI/MetasAlgebraEx.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/Exercises/MetasAlgebraEx.ard)
{: .notice--success}

In [Standard Metas for Equality](metas-equality) we introduced metas for in-the-goal rewriting and chaining ({%ard%}rewrite{%endard%}, {%ard%}run{%endard%}, {%ard%}in{%endard%}, {%ard%}at{%endard%}). In [Records and Classes](records) we saw {%ard%}linarith{%endard%}, a meta that uses class instances to discharge linear arithmetic goals. This chapter introduces three more metas of the same flavor — {%ard%}simplify{%endard%}, {%ard%}equation{%endard%}, {%ard%}cong{%endard%} — plus the universal extensionality meta {%ard%}ext{%endard%}.

These metas all live in {%ard%}Algebra.Meta{%endard%} and {%ard%}Paths.Meta{%endard%}:

{%arend%}
\import Algebra.Meta  -- equation, cong, linarith, simplify
\import Paths.Meta    -- ext, simp_coe
{%endarend%}

# simplify: algebraic normalization

{%ard%}simplify{%endard%} normalizes monoid/group/ring/lattice expressions: it strips identity elements, eliminates double inverses and double negations, and collapses {%ard%}x * 0{%endard%}-style patterns. The meta inspects the algebraic class instance in scope and applies the laws guaranteed by that class.

{%arend%}
\lemma simp-1 {M : Monoid} (x : M) : x = x * ide
  => simplify

\lemma simp-2 {M : Monoid} (x : M) : x * x = (x * (ide * x)) * ide
  => simplify

\lemma simp-3 {R : Ring} (x : R) : negative (negative x) = x
  => simplify

\lemma simp-4 {R : Semiring} (x : R) : zro = x * zro
  => simplify
{%endarend%}

{%ard%}simplify{%endard%} is *not* a full decision procedure. It does not, for example, know about commutativity (without it, {%ard%}x * y = y * x{%endard%} is genuinely unprovable — an axiom is needed) or about distributing multiplication over a sum. Use it as a first-pass normalizer, then reach for {%ard%}equation{%endard%} or {%ard%}rewrite{%endard%} for the structural rewriting it cannot perform.

The {%ard%}in{%endard%}-form of {%ard%}simplify{%endard%} normalizes a hypothesis instead of the goal:

{%arend%}
\lemma simp-hyp {M : Monoid} (x y : M) (h : x * (ide * y) = ide) : x * y = ide
  => simplify in h
{%endarend%}

# equation: chained equality, with implicit step proofs

{%ard%}equation a_1 ... a_n{%endard%} proves a goal of shape {%ard%}a_0 = a_{n+1}{%endard%} by treating {%ard%}a_1, ..., a_n{%endard%} as intermediate steps. For each adjacent pair, the meta tries to fill in the proof from local hypotheses; if it cannot, you supply that step explicitly as an implicit argument.

{%arend%}
\lemma eq-test {M : Monoid} (x y z : M) (p : x = y) (q : y = z) : x = z
  => equation x y z
{%endarend%}

This is the meta-driven counterpart of the {%ard%}==<{%endard%} / {%ard%}>=={%endard%} / {%ard%}qed{%endard%} chain from [Proofs of Equality](equalityex#equational-reasoning-proof-of-comm-rewritten). The two coexist: prefer {%ard%}equation{%endard%} when the step proofs are uninteresting (or come from {%ard%}simplify{%endard%}-style normalization); prefer the explicit chain when each step has a name worth showing in the proof body.

# cong: congruence closure

{%ard%}cong{%endard%} proves a goal {%ard%}f x_1 ... x_n = f y_1 ... y_n{%endard%} from contextual equalities {%ard%}x_i = y_i{%endard%}. It runs the [congruence closure](https://en.wikipedia.org/wiki/Congruence_closure) algorithm — a multi-argument generalization of {%ard%}pmap{%endard%}.

{%arend%}
\lemma cong-test {A B : \Type} (f : A -> A -> B)
                 (x x' y y' : A) (p : x = x') (q : y = y')
               : f x y = f x' y'
  => cong
{%endarend%}

The hand-written equivalent would chain {%ard%}pmap{%endard%}, {%ard%}pmap2{%endard%}, or several {%ard%}rewrite{%endard%} steps; {%ard%}cong{%endard%} compresses all of them.

# ext: extensionality, polymorphic over the equality's type

{%ard%}ext{%endard%} discharges goals {%ard%}a = a'{%endard%} where the two sides have a structural form: a function, a Σ-tuple, a record, a proposition, or a type. Each form yields a different *subgoal*:

* On {%ard%}f = g{%endard%} for {%ard%}f, g : \Pi (x : A) -> B x{%endard%}: subgoal is pointwise equality {%ard%}\Pi (x : A) -> f x = g x{%endard%} (function extensionality).
* On {%ard%}t = s{%endard%} for {%ard%}\Sigma (x : A) (y : B x){%endard%}: subgoal is a Σ of componentwise equalities, with appropriate {%ard%}coe{%endard%}-corrections for the dependent components.
* On {%ard%}t = s{%endard%} for a record: same as the Σ case, with the option of copattern syntax {%ard%}ext R { | f_1 => p_1 | ... }{%endard%}.
* On {%ard%}A = B{%endard%} for {%ard%}A, B : \Prop{%endard%}: subgoal is {%ard%}\Sigma (A -> B) (B -> A){%endard%} (propositional extensionality, *provable* in Arend).
* On {%ard%}A = B{%endard%} for {%ard%}A, B : \Type{%endard%}: subgoal is {%ard%}Equiv {A} {B}{%endard%} (univalence).
* On {%ard%}x = y{%endard%} for {%ard%}P : \Prop{%endard%}: no subgoal — the meta closes the goal because all elements of a {%ard%}\Prop{%endard%} are equal.

Examples:

{%arend%}
\lemma ext-fun (f g : Nat -> Nat) (h : \Pi (n : Nat) -> f n = g n) : f = g
  => ext h

\lemma ext-sigma (p p' : \Sigma Nat Nat) (h1 : p.1 = p'.1) (h2 : p.2 = p'.2)
              : p = p'
  => ext (h1, h2)

\lemma ext-prop (A B : \Prop) (f : A -> B) (g : B -> A) : A = B
  => ext (f, g)
{%endarend%}

The full grammar for {%ard%}ext{%endard%} (including the record copattern form and dependent-Σ corrections) is documented at [Paths metas / ext](/documentation/standard-tactics/paths-meta#extensionality-meta).

# simp_coe (advanced)

When proofs accumulate {%ard%}coe{%endard%}/{%ard%}transport{%endard%} over Π-, Σ-, or record-types, {%ard%}simp_coe{%endard%} pushes them through the structure. It is most useful when working with higher inductive types in Part II; we mention it here only for completeness. See [Paths metas / simp_coe](/documentation/standard-tactics/paths-meta#simp_coe) for details.

# Exercises

**Exercise 1:** Prove the following one-liners with {%ard%}simplify{%endard%}: (a) {%ard%}{M : Monoid} (x : M) : x = x * ide{%endard%}, (b) {%ard%}{R : Ring} (x : R) : negative (negative x) = x{%endard%}, (c) {%ard%}{R : Semiring} (x : R) : zro = x * zro{%endard%}.
{: .notice--info}

**Exercise 2:** Find a goal that {%ard%}simplify{%endard%} cannot solve and explain why. Hint: try a goal that requires *commutativity*.
{: .notice--info}

**Exercise 3:** Prove {%ard%}{A : \Type} (f : A -> A -> A -> A) (x x' y y' z z' : A) (p : x = x') (q : y = y') (r : z = z') : f x y z = f x' y' z'{%endard%} with one {%ard%}cong{%endard%}. Then write the equivalent proof using {%ard%}pmap{%endard%}/{%ard%}pmap2{%endard%}/manual rewriting and compare line counts.
{: .notice--info}

**Exercise 4:** Prove {%ard%}(\lam (x : Nat) => x Nat.+ 0) = (\lam x => x){%endard%} using {%ard%}ext{%endard%}.
{: .notice--info}

**Exercise 5:** Define a 3-field {%ard%}\record R{%endard%} and prove that two values of {%ard%}R{%endard%} are equal whenever each pair of components is equal, using the copattern form {%ard%}ext R { | f_1 => p_1 | ... }{%endard%}.
{: .notice--info}

**Exercise 6:** Prove {%ard%}\Pi (A B : \Prop) -> (A -> B) -> (B -> A) -> A = B{%endard%} using {%ard%}ext{%endard%}.
{: .notice--info}
