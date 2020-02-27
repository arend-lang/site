---
title:  Mere propositions
nav: hprops
---

Recall that under Curry-Howard correspondence there is no difference between propositions and types:
all types are propositions and vice versa. In this module we discuss and justify an alternative view,
according to which propositions are only some types, namely those types, all elements of which are equal.
These types are called _mere propositions_ since they have at most one element, which, if it exists, 
usually does not contain any data and is merely a proof of the proposition. It is standard in 
homotopy type theory to use the term "proposition" for mere propositions.

Subsequently we discuss another important subclass of types, consisting of those types that can be
idenified with sets.

# Subsets, injective functions

In set theory if {%ard%}A{%endard%} is a set and {%ard%}P{%endard%} is a predicate
on {%ard%}A{%endard%}, then we can define the subset {%ard%}{ x : A | P x }{%endard%}
of elements of {%ard%}A{%endard%} satisfying {%ard%}P{%endard%}, and the elements of the 
subset will also be elements of {%ard%}A{%endard%}.

In type theory we cannot talk about subtypes in this way. Instead, we say that a subtype
{%ard%}B{%endard%} of type {%ard%}A{%endard%} is just any type together with an injective
function {%ard%}B -> A{%endard%}. For example, the subset above corresponds to the type
{%ard%}\Sigma (x : A) (P x){%endard%}, which is realized as a subtype of {%ard%}A{%endard%}
by means of the function:
{%arend%}\lam t => t.1 : \Sigma (x : A) (P x) -> A{%endarend%}
as long as this function is an injection. As we will see further in this module, this function
is always an injection if the range of {%ard%}P{%endard%} is restricted to a certain class of
types. This class is precisely the class of all mere propositions.

Consider an example: the subtype of {%ard%}Nat{%endard%} consisting of even natural numbers.

{%arend%}
\func isEven (n : Nat) : Bool
  | 0 => true
  | 1 => false
  | suc (suc n) => isEven n

-- { n : Nat | T (isEven n) } -- set-theoretic notation 
\func Even => \Sigma (n : Nat) (T (isEven n)) -- subtype of even numbers

-- Embedding of even numbers into the type of all natural numbers
\func Even-inc (e : Even) => e.1
{%endarend%}

Let us show that {%ard%}Even-inc{%endard%} is an injection, namely that it satisfies the predicate
{%ard%}isInj{%endard%}:

{%arend%}
\func isInj {A B : \Type} (f : A -> B) =>
   \Pi (x y : A) -> f x = f y -> x = y
-- This is equivalent to the predicate below only in
-- presence of the excluded middle:
-- \Pi (x y : A) -> Not (x = y) -> Not (f x = f y)
{%endarend%}

This requires proving equalities between pairs. For non-dependent pairs this is completely
straightforward and reduces to proving equalities between components:

{%arend%}
\func prodEq {A B : \Type} (t1 t2 : \Sigma A B) (p : t1.1 = t2.1) (q : t1.2 = t2.2)
  : t1 = t2
  => path (\lam i => (p @ i, q @ i))
{%endarend%}

In case of dependent pairs, we cannot talk about equalities of second components since they
have different types. In order to prove equality of such pairs we need to have a proof of
equality between their first components and a proof of equality between the second component
of one of the pairs and transported second component of the other pair:

{%arend%}
\func sigmaEq {A : \Type} (B : A -> \Type) (t1 t2 : \Sigma (x : A) (B x))
  -- t1.2 : B t1.1
  -- t2.2 : B t2.1
              (p : t1.1 = t2.1) (q : transport B p t1.2 = t2.2)
  : t1 = t2
  {-
  \elim t1,t2,p,q
  | (a1,b1), (a2,b2), idp, idp => idp
  -}
  => J (\lam a' p' => 
          \Pi (b' : B a') (q' : transport B p' t1.2 = b') -> t1 = (a',b'))
       (\lam b' q' => pmap (\lam b'' => ((t1.1,b'') : \Sigma (x : A) (B x))) q')
       p t2.2 q

{%endarend%}

Note that any two elements of {%ard%}T b{%endard%} are equal. This allows us to prove
that {%ard%}Even-inc{%endard%} is injective:

{%arend%}
\func T-lem {b : Bool} {x y : T b} : x = y
  | {true} => idp

\func Even-inc-isInj : isInj Even-inc =>
  \lam x y p => sigmaEq (\lam n => T (isEven n)) x y p T-lem
{%endarend%}

Consider one more example. Define functions computing residuals modulo 3 and 5 and define the type
of all natural numbers that are divisible by 3 or 5:

{%arend%}
\func mod3 (n : Nat) : Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | suc (suc (suc n)) => mod3 n

\func mod5 (n : Nat) : Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | suc (suc (suc (suc (suc n)))) => mod5 n

\func MultipleOf3Or5 => \Sigma (n : Nat) ((mod3 n = 0) `Either` (mod5 n = 0))
{%endarend%}

In contrast to the previous example, the function that maps elements of
{%ard%}MultipleOf3Or5{%endard%} to {%ard%}Nat{%endard%} is not an injection:

{%arend%}
\func Mul-inc (m : MultipleOf3Or5) => m.1

-- One can prove that Mul-inc is not injective
\func not-Mul-inc-isInj (p : isInj Mul-inc) : Empty => {?}
{%endarend%}

<!-- TODO: prove not-Mul-inc-isInj or leave as exercise -->

This is so because for some {%ard%}n{%endard%}, namely for those that are divisible
by both 3 and 5, there are several non-equal proofs of {%ard%}(mod3 n = 0) `Either` (mod5 n = 0){%endard%}.
Thus {%ard%}MultipleOf3Or5{%endard%} is not a subtype of {%ard%}Nat{%endard%}.

# Mere propositions

As the two examples above illustrate, a predicate defining a subtype should have the range
consisting of types, all elements of which are equal. The types satisfying these conditions are
called _mere propositions_ or just propositions.

{%arend%}
\func isProp (A : \Type) => \Pi (x y : A) -> x = y
{%endarend%}

For example, according to this definition {%ard%}Bool{%endard%} is not a proposition.

{%arend%}
\func BoolIsNotProp (p : isProp Bool) : Empty => transport T (p true false) ()
{%endarend%}

Propositions can be formed using logical operations ⊤, ⊥, ∧, →, ∀ the same as
in the Curry-Howard correspondence. Operations ∨, ∃ and the predicate = can, of course,
also be defined, but in general require additional language constructs, which we 
introduce later. One can use recursion and induction to define predicates in this logic
as usual.

Consider several examples. The unit type {%ard%}Unit{%endard%} is proposition
corresponding to the proposition "True":

{%arend%}
\func Unit => \Sigma

\func Unit-isProp : isProp Unit => \lam x y => idp
{%endarend%}

The empty type {%ard%}Empty{%endard%} is the proposition "False":

{%arend%}
\func Empty-isProp : isProp Empty => \lam x y => absurd x
{%endarend%}

The product (conjunction) of propositions is proposition:

{%arend%}
\func Sigma-isProp {A B : \Type} (pA : isProp A) (pB : isProp B)
  : isProp (\Sigma A B) => \lam p q => prodEq p q (pA p.1 q.1) (pB p.2 q.2)
{%endarend%}

The function type (implication) between propositions is poposition:

{%arend%}
\func funcExt {A : \Type} (B : A -> \Type) (f g : \Pi (x : A) -> B x)
              (p : \Pi (x : A) -> f x = g x) : f = g =>
  path (\lam i x => p x @ i)


\func Impl-isProp {A B : \Type} {- (pA : isProp A) -} (pB : isProp B) : isProp (A -> B)
  => \lam f g =>
      -- path (\lam i x => pB (f x) (g x) @ i)
      funcExt (\lam _ => B) f g (\lam x => pB (f x) (g x))
{%endarend%}

Propositions are closed under Pi-types (universal quantification):

{%arend%}
\func forall-isProp {A : \Type} (B : A -> \Type) (pB : \Pi (x : A) -> isProp (B x))
  : isProp (\Pi (x : A) -> B x)
  => \lam f g => funcExt B f g (\lam x => pB x (f x) (g x))
{%endarend%}

However, the logic of propositions is not closed in general under sum types
{%ard%}Either A B{%endard%} (Curry-Howard disjunctions),
sigma types {%ard%}\Sigma (x : A) (B x){%endard%} (Curry-Howard existential quantifier)
and the equality type.

<!-- TODO: prove the nagation or leave as exercise -->
{%arend%}
\func Either-isProp {A B : \Type} (pA : isProp A) (pB : isProp B)
   : isProp (Either A B) =>
   {?}

\func exists-isProp {A : \Type} (B : A -> \Type)
                    (pB : \Pi (x : A) -> isProp (B x))
  : isProp (\Sigma (x : A) (B x)) =>
  {?}

\func equality-isProp {A : \Type} (a a' : A) : isProp (a = a') => {?}
{%endarend%}

For now we cannot define disjunctions, existential quantifiers and equality. But later
we will introduce a way to project appropriately any type {%ard%}A{%endard%} to the class
of propositions, and this projection will be applied to the types above to get 
corresponding logical operations.

Although, as we have just seen, equality of elements of a type {%ard%}A{%endard%} is not
a proposition in general, it holds for many types {%ard%}A{%endard%}. Such types are
called _sets_.

{%arend%}
\func isSet (A : \Type) => \Pi (a a' : A) -> isProp (a = a')

-- By definition equality is mere porosition for sets
\func equality-isProp {A : \Type} (p : isSet A) (a a' : A) : isProp (a = a') => p a a'
{%endarend%}

We conclude with several remarks on definitions of predicates in the logic of
mere propositions. 

A recursive definition defines a predicate valued in propositions if all its
clauses are propositions. For example, the following defines a predicate in the logic
of mere propositions if expressions {%ard%}E-zero{%endard%} and {%ard%}E-suc{%endard%} are propositions:

{%arend%}
\func pred (n : Nat) : \Type
  | 0 => E-zero
  | suc n => E-suc
{%endarend%}

Inductive definitions can be also used to define predicates. One should be careful with
inductive definitions since a predicate can often have several inductive definitions,
some of which are valued in propositions and some of them are not. For example:

{%arend%}
-- Defines predicate valued in propositions
\data \infix 4 <=' (n m : Nat) \with
  | 0, _ => zero<=_
  | suc n, suc m => suc<=suc (n <=' m)

-- Does not define a predicate valued in propositions
\data \infix 4 <='' (n m : Nat) \elim m
  | m => <=-refl (n = m)
  | 1 => zero<=one (n = 0)
  | suc m => <=-step (n <='' m)

{%endarend%}
