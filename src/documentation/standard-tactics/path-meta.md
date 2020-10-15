---
title: \module Paths.Meta
---

# Rewriting metas

Meta `rewrite`, `rewriteI` and `rewriteF` works just like the rewriting mechanism in other languages,
such as Coq or Idris (in Agda, `rewrite` is allowed only in the LHS of a clause, so it's different).

+ `rewrite p t : T` where `p : a = b` replaces occurrences of `a` in `T` with a variable `x`
  obtaining a type `T[x/a]` and returns `transport (\lam x => T[x/a]) p t`.
  Note that `T` is the expected type from the context, not the type of `t`.
  When the expected type is unknown, the type of `t` will be used instead of `T`.
+ `rewriteF` is like `rewrite` but it enforces to use the type of `t` instead of the expected type.
+ `rewriteI p t` is equivalent to `rewrite (inv p) t`.

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

\lemma testNorm {A : \Type} (a : A) (l : List A) (P : List A -> \Prop) (p : P (a :: l)) : P ((a :: l) ++ nil)
  => rewrite ++_nil p

\lemma testRestore {A : \Type} (xs ys zs : List A) (P : List A -> List A -> \Prop) (p : P (xs ++ ys) zs) : P (xs ++ ys) (zs ++ nil)
  => rewrite ++_nil p
{% endarend %}
