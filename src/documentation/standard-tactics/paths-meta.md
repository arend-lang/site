---
title: \module Paths.Meta
---

# Rewriting metas

Metas {%ard%} rewrite {%endard%}, {%ard%} rewriteI {%endard%}, and {%ard%} rewriteF {%endard%} work just like the rewriting mechanism in other languages,
such as Coq or Idris (in Agda, `rewrite` is allowed only in the LHS of a clause, so it's different).

+ {%ard%} rewrite p t : T {%endard%} where {%ard%} p : a = b {%endard%} replaces occurrences of {%ard%} a {%endard%} in {%ard%} T {%endard%} with a variable {%ard%} x {%endard%}
  obtaining a type {%ard%} T[x/a] {%endard%} and returns {%ard%} transportInv (\lam x => T[x/a]) p t {%endard%}.
  Note that {%ard%} T {%endard%} is the expected type from the context, not the type of {%ard%} t {%endard%}.
  When the expected type is unknown, the type of {%ard%} t {%endard%} will be used instead of {%ard%} T {%endard%}.
+ {%ard%} rewriteF {%endard%} is like {%ard%} rewrite {%endard%} but it enforces to use the type of {%ard%} t {%endard%} instead of the expected type.
+ {%ard%} rewriteI p t {%endard%} is equivalent to {%ard%} rewrite (inv p) t {%endard%}.

To any of the metas above it is possible to add specification of numbers of occurrences. For example, {%ard%} rewrite {i1, i2, ... ik} p t : T {%endard%} rewrites only occurrences
with numbers {%ard%} i1, i2, ... ik {%endard%} where occurrence {%ard%} ij {%endard%} is the number of occurrence after all previous occurrences have been replaced.

Examples:

{% arend %}
\import Function.Meta
\import Paths.Meta
\import Data.List

\lemma +-assoc (a b c : Nat) : a + b + c = a + (b + c) \elim c
  | 0 => idp
  | suc c => rewrite (+-assoc a b c) idp

\lemma +-comm-rw (a b : Nat) : a + b = b + a
  | 0, 0 => idp
  | 0, suc b => rewrite (+-comm-rw 0 b) idp
  | suc a, 0 => rewriteI (+-comm-rw a 0) idp
  | suc a, suc b => rewrite (+-comm-rw $ suc a) $
       rewriteI (+-comm-rw a b) $ rewriteI (+-comm-rw a $ suc b) idp

\lemma test1 (x y : Nat) (p : x = 0) (q : 0 = y) : x = y => rewrite p q

\lemma test2 (x y : Nat) (p : 0 = x) (q : 0 = y) : x = y => rewriteI p q

\lemma test3 (x y : Nat) (p : 0 = x) (q : 0 = y) : x = y => rewriteF p q

\lemma test4 (x y : Nat) (p : 0 = x) (q : 0 = y) => rewriteF p q

\lemma test5 (x y : Nat) (p : 0 = x) (q : 0 = y) => rewrite p q

\lemma test6 {A : \Set} (x : A) (f : A -> A) (h : \Pi (z : A) -> f z = z) : f (f x) = x
  => rewrite h (rewrite h idp)

\lemma test7 {A : Nat} (x y : A) (f : A -> A) : f (x + y) = f (y + x)
  => rewrite +-comm-rw idp
  
\lemma testOccur {x : Nat} (p : suc x = suc (suc x)) : suc (suc x) = x Nat.+ 3 => rewrite {1} p idp  

\lemma testNorm {A : \Type} (a : A) (l : List A) (P : List A -> \Prop) (p : P (a :: l)) : P ((a :: l) ++ nil)
  => rewrite ++_nil p

\lemma testRestore {A : \Type} (xs ys zs : List A) (P : List A -> List A -> \Prop) (p : P (xs ++ ys) zs) : P (xs ++ ys) (zs ++ nil)
  => rewrite ++_nil p
{% endarend %}

# Algebraic rewrite

Meta {%ard%} rewriteEq {%endard%} allows for more advanced rewriting in algebraic subexpressions. {%ard%} rewriteEq p t : T {%endard%},
where {%ard%} p : a = b {%endard%}, like {%ard%} rewrite {%endard%} replaces literal occurrences of {%ard%} a {%endard%} in {%ard%} T {%endard%}
with {%ard%} b {%endard%}, but it also finds and replaces occurrences up to algebraic equivalences. Currently, this meta supports noncommutative monoids and categories.

For example, if {%ard%} ((a * b) * (ide * c)) * (d * ide) {%endard%} is an expression of type {%ard%} Monoid {%endard%} in {%ard%} T {%endard%},
then {%ard%} b * c * ide {%endard%} counts as an occurrence. If {%ard%} p : b * c * ide = x {%endard%}, then 
{%ard%} rewriteEq p t {%endard%} will rewrite {%ard%} ((a * b) * (ide * c)) * (d * ide) {%endard%} as {%ard%} ((a * x) * d) {%endard%}.

Meta {%ard%} rewriteEq {%endard%} also supports specification of numbers of occurrences which works similarly to the one for {%ard%} rewrite {%endard%}.
Note that occurrences can overlap in this case. The counting is natural from left to right.

Examples:

{% arend %}
\lemma test1 {A : Monoid} (a b c d x : A) (B : A -> \Prop) (p : b * c = x) (t : B (a * x * d)) : B (((a * b) * (ide * c)) * (d * ide))
  => rewriteEq p t
  
\lemma test2 {C : Precat} {a b c d : C} (P : Hom a d -> \Prop) (f : Hom a b) (g : Hom b c) (g' : Hom c b) (h : Hom c d) (p : g ∘ g' = id c) (t : P ((h ∘ g) ∘ (id b ∘ f))) : P ((h ∘ id c ∘ g) ∘ (g' ∘ g ∘ f))
  => rewriteEq p (rewriteEq (idp {_} {(h ∘ g) ∘ (id b ∘ f)}) t)
{% endarend %}  

# Extensionality meta

Meta {%ard%} ext {%endard%} proves goals of the form {%ard%} a = {A} a' {%endard%}.
It expects (at most) one argument and the type of this argument is called 'subgoal'. The expected type is called 'goal'.
* If the goal is {%ard%} f = {\Pi (x_1 : A_1) ... (x_n : A_n) -> B} g {%endard%}, then the subgoal is {%ard%} \Pi (x_1 : A_1) ... (x_n : A_n) -> f x_1 ... x_n = g x_1 ... x_n {%endard%}
* If the goal is {%ard%} t = {\Sigma (x_1 : A_1) ... (x_n : A_n) (y_1 : B_1 x_1 ... x_n) ... (y_k : B_k x_1 ... x_n) (z_1 : C_1) ... (z_m : C_m)} s {%endard%}, where {%ard%} C_i : \Prop {%endard%} and they can depend on {%ard%} x_j {%endard%} and {%ard%} y_l {%endard%} for all {%ard%} i {%endard%}, {%ard%} j {%endard%}, and {%ard%} l {%endard%},
then the subgoal is {%ard%} \Sigma (p_1 : t.1 = s.1) ... (p_n : t.n = s.n) D_1 ... D_k {%endard%}, where {%ard%} D_j {%endard%} is equal to {%ard%} coe (\lam i => B (p_1 @ i) ... (p_n @ i)) t.{k + j - 1} right = s.{k + j - 1} {%endard%}
* If the goal is {%ard%} t = {R} s {%endard%}, where {%ard%} R {%endard%} is a record, then the subgoal is defined in the same way as for \Sigma-types
It is also possible to use the following syntax in this case: {%ard%} ext R { | f_1 => e_1 ... | f_l => e_l } {%endard%}, which is equivalent to {%ard%} ext (e_1, ... e_l) {%endard%}
* If the goal is {%ard%} A = {\Prop} B {%endard%}, then the subgoal is {%ard%} \Sigma (A -> B) (B -> A) {%endard%}
* If the goal is {%ard%} A = {\Type} B {%endard%}, then the subgoal is {%ard%} Equiv {A} {B} {%endard%}
* If the goal is {%ard%} x = {P} y {%endard%}, where {%ard%} P : \Prop {%endard%}, then the argument for {%ard%} ext {%endard%} should be omitted.

# simp_coe

Simplifies certain equalities. It expects one argument and the type of this argument is called 'subgoal'. The expected type is called 'goal'.
* If the goal is {%ard%} coe (\lam i => \Pi (x : A) -> B x i) f right a = b' {%endard%}, then the subgoal is {%ard%} coe (B a) (f a) right = b {%endard%}.
* If the goal is {%ard%} coe (\lam i => \Pi (x : A) -> B x i) f right = g' {%endard%}, then the subgoal is {%ard%} \Pi (a : A) -> coe (B a) (f a) right = g a {%endard%}.
* If the goal is {%ard%} coe (\lam i => A i -> B i) f right = g' {%endard%}, then the subgoal is {%ard%} \Pi (a : A left) -> coe B (f a) right = g (coe A a right) {%endard%}.
* If the type under {%ard%} coe {%endard%} is a higher-order non-dependent function type, {%ard%} simp_co {%endard%}e simplifies it recursively.
* If the goal is {%ard%} (coe (\lam i => \Sigma (x_1 : A_1 i) ... (x_n : A_n i) ...) t right).n = b' {%endard%}, then the subgoal is {%ard%} coe A_n t.n right = b {%endard%}.
* If the goal is {%ard%} coe (\lam i => \Sigma (x_1 : A_1) ... (x_n : A_n) (B_{n+1} i) ... (B_k i)) t right = s' {%endard%}, then the subgoal is a \Sigma type consisting of equalities as specified above ignoring fields in \Prop.
* If the type under {%ard%} coe {%endard%} is a record, then {%ard%} simp_coe {%endard%} works similarly to the case of \Sigma types. The copattern matching syntax as in {ext} is also supported.
* All of the above cases also work for goals with {transport} instead of {coe} since the former evaluates to the latter.
* If the goal is {%ard%} transport (\lam x => f x = g x) p q = s {%endard%}, then the subgoal is {%ard%} q *> pmap g p = pmap f p *> s {%endard%}. If {%ard%} f {%endard%} does not depend on {%ard%} x {%endard%}, then the right hand side of the subgoal is simply {%ard%} s {%endard%}.
