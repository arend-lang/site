---
title: Equational Reasoning, J, Predicates
nav: equalityex
---

In this module we give a number of examples, demonstrating techniques used in more advanced proofs of equalities.
We introduce a convention for writing more readable equality proofs called _equational reasoning_. 
We argue that {%ard%}transport{%endard%} is insufficient in some cases and introduce its generalization
called _eliminator J_.

We supplement this discussion of equality with remarks on definitions of predicates.

# Commutativity of +

Let's apply notions from the previous module and prove commutativity of {%ard%}+ : Nat -> Nat -> Nat{%endard%}.
Note that {%ard%}transport{%endard%} satisfies the following property:

{%arend%}
-- transport B idp b ==> b

-- recall the definition of transport:
\func transport {A : \Type} (B : A -> \Type) {a a' : A} (p : a = a') (b : B a)
   => coe (\lam i => B (p @ i)) b right

-- indeed, coe (\lam i => B (idp @ i)) b right ==> 
-- ==> coe (\lam i => B a) b right ==> b
{%endarend%}

It will be more convenient to have transitivity of {%ard%}={%endard%}, which we proved in the previous module, in 
infix form:

{%arend%}
\func \infixr 5 *> {A : \Type} {a a' a'' : A} (p : a = a') (q : a' = a'') : a = a''
   => transport (\lam x => a = x) q p
{%endarend%}

Function {%ard%}*>{%endard%} thus satisfies the property {%ard%}p *> idp ==> p{%endard%}.
We can also define transitivity {%ard%}<*{%endard%} such that {%ard%}idp <* p ==> p{%endard%}, but
we do not need it yet.

The commutativity can now be proved as follows:

{%arend%}
\func +-comm (n m : Nat) : n + m = m + n
  | 0, 0 => idp
  | suc n, 0 => pmap suc (+-comm n 0)
  | 0, suc m => pmap suc (+-comm 0 m)
  | suc n, suc m => pmap suc (+-comm (suc n) m *> pmap suc (inv (+-comm n m)) *> +-comm n (suc m))
{%endarend%}

# Equational reasoning, proof of +-comm rewritten

There is one clever trick that allows to write sequences of equality proofs joining by transitivity in a
more readable form. Namely, one can define operators {%ard%}`==<`{%endard%}, {%ard%}`>==`{%endard%} and
{%ard%}`qed`{%endard%} such that it is possible to write instead of a chain of equality proofs 
{%ard%}p1 `*>` ... `*>` pn{%endard%} an extended chain {%ard%}a1 `==<` p1 `>==` a2 `==<` p2 `>==` a3 ... `qed {%endard%},
where we also specify the objects equality of which is proven at each step (in other words, {%ard%}pi : ai = a(i+1){%endard%}).
The proof {%ard%}+-comm{%endard%} rewritten in this way looks as follows:

{%arend%}
\func +-comm' (n m : Nat) : n + m = m + n
  | 0, 0 => idp
  | suc n, 0 => pmap suc (+-comm' n 0)
  | 0, suc m => pmap suc (+-comm' 0 m)
  | suc n, suc m => pmap suc (
    suc n + m   ==< +-comm' (suc n) m >==
    suc (m + n) ==< pmap suc (inv (+-comm' n m)) >==
    suc (n + m) ==< +-comm' n (suc m) >==
    suc m + n   `qed
  )

-- recall that:
-- x `f == f x -- postfix notation
-- x `f` y == f x y -- infix notation
{%endarend%}

These operators can be defined as follows:

{%arend%}
\func \infix 2 qed {A : \Type} (a : A) : a = a => idp

\func \infixr 1 >== {A : \Type} {a a' a'' : A} (p : a = a') (q : a' = a'') => p *> q

\func \infix 2 ==< {A : \Type} (a : A) {a' : A} (p : a = a') => p
{%endarend%}

# J operator

Recall from [Eliminators](/documentation/tutorial/PartI/idtype#Eliminators) that elimination
principles for a datatype {%ard%}D{%endard%} say that functions from {%ard%}D{%endard%} are
determined by their values on the constructors of {%ard%}D{%endard%}, that is that {%ard%}D{%endard%}
is "generated" by its constructors. 

Similarly, we can say that identity type {%ard%}={%endard%} is "generated" by reflexivity {%ard%}idp{%endard%}:
the non-dependent version of eliminator says that if we define the value of a function {%ard%}a = x -> B x{%endard%}
on {%ard%}idp{%endard%}, that is some value {%ard%}b : B a{%endard%}, then we would uniquely determine this function:    

{%arend%}
\func transport'
    {A : \Type}
    (B : A -> \Type)
    {a a' : A} (p : a = a')
    (b : B a)
    : B a'
  => coe (\lam i => B (p @ i)) b right
{%endarend%}

The J operator is a dependent version of this, stating that specifying value on {%ard%}idp{%endard%} is enough to determine 
a function {%ard%}\Pi (x : A) (p : a = x) -> B x p{%endard%}:  

{%arend%}
\func J
    {A : \Type} {a : A}
    (B : \Pi (a' : A) -> a = a' -> \Type)
    (b : B a idp)
    {a' : A} (p : a = a')
    : B a' p
  -- the details of the definition are not important for now
  => coe (\lam i => B (p @ i) (psqueeze p i)) b right
  \where
    \func psqueeze  {A : \Type} {a a' : A} (p : a = a') (i : I) : a = p @ i => path (\lam j => p @ I.squeeze i j)
{%endarend%}

Note that {%ard%}B a' p{%endard%} above depends on both {%ard%}a'{%endard%} and {%ard%}p{%endard%}. If we make {%ard%}a'{%endard%}
fixed and equal to {%ard%}a{%endard%} in the definition above, then we obtain _K eliminator_: 
{%arend%}
\func K {A : \Type} {a : A} (B : a = a -> \Type)
    (b : B idp)
    (p : a = a) : B p => {?}
{%endarend%}
This eliminator equivalent to the statement that every element of {%ard%}a = a{%endard%} is {%ard%}idp{%endard%}. 
It may seem natural at first sight to add it as an axiom then to simplify things by making proofs of equalities
unique (as it implies that {%ard%}p = p'{%endard%} for any {%ard%}p, p' : a = a'{%endard%}), but actually it is
important that these proofs are _not unique_. This issue will be discussed later. <!-- TODO: ref to Part II -->

It is not convenient to use the J operator directly.
For this reason, Arend has the pattern matching principle corresponding to J.
A parameter of type {%ard%} a = a' {%endard%} can be matched with {%ard%} idp {%endard%} making {%ard%} a {%endard%} and {%ard%} a' {%endard%} equivalent.
For example, {%ard%} transport {%endard%} can be defined as follows:

{%arend%}
\func transport {A : \Type} (B : A -> \Type) {a a' : A} (p : a = a') (b : B a) : B a' \elim p
  | idp => b
{%endarend%}

See [Prelude](/documentation/language-reference/prelude#idp) for more information about this pattern matching principle.

The pattern matching on {%ard%}idp{%endard%} may look confusing at first sight. On one hand we claim that {%ard%}a = a'{%endard%}
can have more than one element, but on the other hand we allow pattern matching on {%ard%}idp{%endard%}, which means that
{%ard%}a = a'{%endard%} has one element. This seeming contradiction is resolved by observing that in reality we pattern
match simultaneously on _two_ variables {%ard%} p : a = a' {%endard%} and {%ard%} a' {%endard%}, instead of just one
{%ard%} p : a = a' {%endard%}. In other words, we _do not_ match on the type {%ard%} a = a' {%endard%}, but match on the
type {%ard%} \Sigma (a' : A) (a = a') {%endard%} of pairs instead, which is one-element type.
Precisely this fact is the source of all the restrictions discussed in [Prelude](/documentation/language-reference/prelude#idp). 

# Associativity of append for vectors

Let us prove some statement that essentially requires J. A good example of such statement is associativity of the
append {%ard%}v++{%endard%} for vectors. Let's recall the definitions of the datatype {%ard%}Vec{%endard%} and
the function {%ard%}v++{%endard%}:

{%arend%}
\data Vec (A : \Type) (n : Nat) \elim n
  | zero => vnil
  | suc n => vcons A (Vec A n)

\func \infixl 4 v++ {A : \Type} {n m : Nat} (xs : Vec A n) (ys : Vec A m) : Vec A (m + n) \elim n, xs
  | 0, vnil => ys
  | suc n, vcons x xs => vcons x (xs v++ ys)
{%endarend%}

Already the statement of associativity of {%ard%}v++{%endard%} requires some work since the types of 
{%ard%}(xs v++ ys) v++ zs{%endard%} and {%ard%}xs v++ (ys v++ zs){%endard%} do not coincide: the types are
{%ard%}Vec A (k + (m + n)){%endard%} and {%ard%}Vec A ((k + m) + n){%endard%} respectively. We can get over it
by using {%ard%}transport{%endard%} since it allows to translate an element of {%ard%}Vec A x{%endard%} to an 
element of {%ard%}Vec A y{%endard%} if {%ard%}x = y{%endard%}:

{%arend%}
\func v++-assoc {A : \Type} {n m k : Nat} (xs : Vec A n) (ys : Vec A m) (zs : Vec A k)
  : (xs v++ ys) v++ zs = transport (Vec A) (+-assoc k m n) (xs v++ (ys v++ zs)) \elim n, xs
  | 0, vnil => idp
  | suc n, vcons x xs =>
      pmap (vcons x) (v++-assoc xs ys zs) *>
      inv (transport-vcons-comm (+-assoc k m n) x (xs v++ (ys v++ zs)))
  \where
    -- transport commutes with all constructors
    -- here is the proof that it commutes with vcons
    \func transport-vcons-comm {A : \Type} {n m : Nat} (p : n = m) (x : A) (xs : Vec A n)
      : transport (Vec A) (pmap suc p) (vcons x xs) = vcons x (transport (Vec A) p xs)
      | idp => idp
      {- This function can be defined with J as follows:
      => J (\lam m' p' => transport (Vec A) (pmap suc p') (vcons x xs) = vcons x (transport (Vec A) p' xs))
           idp
           p
      -}
{%endarend%}

Let us take a closer look at what is going on in this proof. First, we apply the congruence {%ard%}pmap (vcons x){%endard%} to the induction
hypothesis {%ard%}v++-assoc xs ys zs{%endard%} so that we obtain the equality:
{%arend%}
vcons x (xs v++ ys) v++ zs = vcons x (transport (Vec A) (+-assoc k m n) (xs v++ (ys v++ zs))).
{%endarend%}
This corresponds to the following three lines of the proof:
{%arend%}
  | 0, vnil => idp
  | suc n, vcons x xs =>
        pmap (vcons x) (v++-assoc xs ys zs)
{%endarend%}
The left side of the above equality is precisely what we need since {%ard%}((vcons x xs) v++ ys) v++ zs{%endard%}
evaluates to {%ard%}vcons x ((xs v++ ys) v++ zs){%endard%}. So, we should compose this proof with the proof of

{%arend%}
vcons x (transport (Vec A) (+-assoc k m n) (xs v++ (ys v++ zs))) = transport (Vec A) (+-assoc k m n) (vcons x (xs v++ (ys v++ zs)))
{%endarend%}

And this is precisely the commutativity of {%ard%}transport{%endard%} with {%ard%}vcons{%endard%}, which we 
prove in {%ard%}transport-vcons-comm{%endard%} lemma. 
Note that it is important that we generalize the statement and prove the commutativity not only for
{%ard%}+-assoc k m n{%endard%} but for all {%ard%}e : Nat{%endard%} satisfying {%ard%}p : k + m + n = e{%endard%} (otherwise, we would not be able to use pattern mathing or the J operator to prove this statement).


# Predicates

A predicate on a type {%ard%}A{%endard%} is by definition a function from {%ard%}A{%endard%} to a type of propositions.
In particular, in propositions-as-types logic predicates are functions {%ard%}A->\Type{%endard%}.

There are several ways to define a predicate over a type {%ard%}A{%endard%}:

* By combining existing predicates (for example, equality) by means of logical connectives. For example, 
{%ard%}isEven{%endard%} can be defined as {%ard%}\lam n => \Sigma (k : Nat) (n = 2 * k){%endard%}.
* By recursion, but only if {%ard%}A{%endard%} is a datatype.
* By induction.

We now illustrate all these ways in case of the predicate <= for natural numbers.

{%arend%}
-- Definition of <= via equality.
\func LessOrEq''' (n m : Nat) => \Sigma (k : Nat) (k + n = m)

-- Recursive definition of <=.
\func lessOrEq (n m : Nat) : \Type
  | 0, _ => Unit
  | suc _, 0 => Empty
  | suc n, suc m => lessOrEq n m

-- First inductive definition of <=.
\data LessOrEq (n m : Nat) \with
  | 0, m => z<=n
  | suc n, suc m => s<=s (LessOrEq n m)

\func test11 : LessOrEq 0 100 => z<=n
\func test12 : LessOrEq 3 67 => s<=s (s<=s (s<=s z<=n))
-- Of course, there is no proof of 1 <= 0.
-- \func test10 : LessOrEq 1 0 => ....

-- Second inductive definition of <=.
-- This is a modification of the first inductive definition,
-- where we avoid constructor patterns.
\data LessOrEq' (n m : Nat)
  | z<=n' (n = 0)
  | s<=s' {n' m' : Nat} (n = suc n') (m = suc m') (LessOrEq' n' m')
{%endarend%}

There are usually many ways to choose constructors for inductive definitions. To define a predicate inductively, we need to
come up with a set of axioms that characterise the predicate. 

For example, for {%ard%}LessOrEq{%endard%} we chose two axioms:
1) 0 <= m for all m, 2) if n <= m, then suc n <= suc m for all n, m. Every inequality can be derived from these axioms.
But this is not the only way to characterise {%ard%}LessOrEq{%endard%}. For example, we could use the following two axioms:
1) n <= n for all n, 2) if n <= m, then n <= suc m for all n, m:

{%arend%}
-- Third inductive definition of <=.
\data LessOrEq'' (n m : Nat) \elim m
  | suc m => <=-step (LessOrEq'' n m)
  | m => <=-refl (n = m)
{%endarend%}

