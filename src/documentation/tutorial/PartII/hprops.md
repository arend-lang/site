---
title:  Propositions and Sets
nav: hprops
---

The source code for this module: [PartII/PropsSets.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartII/src/PropsSets.ard) \\
The source code for the exercises: [PartII/PropsSetsEx.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartII/src/Exercises/PropsSetsEx.ard)
{: .notice--success}

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

**Exercise 1:** Let {%ard%}f : A -> B{%endard%} and {%ard%}g : B -> C{%endard%} be some functions.
 Prove that if {%ard%}f{%endard%} and {%ard%}g{%endard%} are injective, then {%ard%}g `o` f{%endard%}
 is also injective. Prove that if {%ard%}g `o` f{%endard%} is injective, then {%ard%}f{%endard%} is also injective.
{: .notice--info}

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

**Exercise 2:** Define the predicate "divisible by 3 or by 5" in such a way that it becomes a proposition.
    Prove that {%ard%}MultipleOf3Or5{%endard%} embeds in {%ard%}Nat{%endard%}.
{: .notice--info}

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

**Exercise 3:** We say that a type {%ard%}A{%endard%} is trivial if there exists an element in {%ard%}A{%endard%}
 such that it is equal to any other element in {%ard%}A{%endard%}. Prove that {%ard%}A{%endard%} is trivial iff
 {%ard%}A{%endard%} is proposition and there is an element in {%ard%}A{%endard%}.
{: .notice--info}

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

**Exercise 4:** Prove that {%ard%}Either{%endard%} is not a proposition in general.
{: .notice--info}

**Exercise 5:** Prove that {%ard%}\Sigma (x : A) (B x){%endard%} preserves propositions.
{: .notice--info}

For now we cannot define disjunctions, existential quantifiers and equality. But later
we will introduce a way to project appropriately any type {%ard%}A{%endard%} to the class
of propositions, and this projection will be applied to the types above to get 
corresponding logical operations.

We now make several remarks on definitions of predicates.

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
some of which are valued in propositions and some of which are not. For example:

{%arend%}
-- Defines predicate valued in propositions
\data \infix 4 <= (n m : Nat) \with
  | 0, _ => zero<=_
  | suc n, suc m => suc<=suc (n <= m)

-- Does not define a predicate valued in propositions
\data \infix 4 <=' (n m : Nat) \elim m
  | m => <=-refl (n = m)
  | 1 => zero<=one (n = 0)
  | suc m => <=-step (n <=' m)
{%endarend%}

**Exercise 6:** Prove that {%ard%}<={%endard%} and {%ard%}<=''{%endard%}
are predicates. It is allowed to use the fact that {%ard%}Nat{%endard%} is a set
without a proof.
{: .notice--info}
{%arend%}
\data <='' (n m : Nat) : \Set0 \elim m
  | suc m => <=-step (<='' n m)
  | m => <=-refl (n = m)
{%endarend%}

**Exercise 7:** Prove that {%ard%}ReflClosure <={%endard%} is not a predicate, but
{%ard%}ReflClosure (\lam x y => T (x < y)){%endard%} is a predicate.
{: .notice--info}
{%arend%}
\func \infix 4 < (n m : Nat) : Bool
  | _, 0 => false
  | 0, suc _ => true
  | suc n, suc m => n < m

\data ReflClosure (R : Nat -> Nat -> \Type) (x y : Nat)
  | refl (x = y)
  | inc (R x y)
{%endarend%}

**Exercise 8:** Prove that if {%ard%}A{%endard%} embeds in {%ard%}B{%endard%} and 
{%ard%}B{%endard%} is a proposition, then {%ard%}A{%endard%} is proposition.
{: .notice--info}

# Sets

Although, as we have just seen, equality of elements of a type {%ard%}A{%endard%} is not
a proposition in general, it holds for many types {%ard%}A{%endard%}. Such types are
called _sets_.

{%arend%}
\func isSet (A : \Type) => \Pi (a a' : A) -> isProp (a = a')

-- By definition equality is mere porosition for sets
\func equality-isProp {A : \Type} (p : isSet A) (a a' : A) : isProp (a = a') => p a a'
{%endarend%}

This can be interated further: we may consider types {%ard%}A{%endard%} such that 
{%ard%}a=a'{%endard%} are sets for all {%ard%}a a' : A{%endard%} and so on. Define
the _homotopy level_ of a type inductively as follows:

* Mere propositions are of homotopy level -1.
* A type {%ard%}A{%endard%} has homotopy level {%ard%}suc n{%endard%} iff
{%ard%}a=a'{%endard%} is of homotopy level {%ard%}n{%endard%}.
 
The predicate {%ard%}hasLevel A suc-l{%endard%}, saying that {%ard%}A{%endard%} has homotopy level 
{%ard%}suc-l - 1{%endard%}, can be defined as follows:

{%arend%}
\func hasLevel (A : \Type) (suc-l : Nat) : \Type \elim suc-l
  | 0 => isProp A
  | suc suc-l => \Pi (x y : A) -> (x = y) `hasLevel` suc-l
{%endarend%}

The sets are thus precisely all the types of homotopy level 0. This is a large class of types, 
which includes, for example, {%ard%}Nat{%endard%}, {%ard%}Unit{%endard%}, {%ard%}Bool{%endard%}, 
lists of sets and so on. All set-theoretic reasoning can be done entirely in the levels of sets
and propositions.

Let us consider several types and prove that they are sets. First of all, the empty type is trivially
a set:

{%arend%}
\func Empty-isSet : isSet Empty => \lam x y _ _ => \case x \with {}
{%endarend%}

Let us prove that the unit type is a set. We will need a lemma saying that if {%ard%}B{%endard%}
is a proposition and {%ard%}A{%endard%} is a retract of {%ard%}B{%endard%}, then {%ard%}A{%endard%}
is also a proposition. Recall that {%ard%}A{%endard%} is called a retract of {%ard%}B{%endard%}
if there exist functions {%ard%}f : A -> B{%endard%} and {%ard%}g : B -> A{%endard%} such that
the composition {%ard%}g `o` f {%endard%} is identity.

{%arend%}
\func retract-isProp {A B : \Type} (pB : isProp B) (f : A -> B) (g : B -> A)
  (h : \Pi (x : A) -> g (f x) = x)
  : isProp A
  => \lam x y => sym (h x) *> pmap g (pB (f x) (f y)) *> h y

{%endarend%}

By this lemma we reduce proving that {%ard%}isProp (x=y){%endard%} for all {%ard%}x y : Unit{%endard%} to proving
that {%ard%}x=y{%endard%} is a retract of {%ard%}\Sigma{%endard%} and using {%ard%}Unit-isProp{%endard%}:

{%arend%}
\data Unit | unit

\func Unit-isProp (x y : Unit) : x = y
  | unit, unit => idp

\func Unit-isSet : isSet Unit => \lam x y => retract-isProp {x = y} Unit-isProp
  (\lam _ => unit) (\lam _ => Unit-isProp x y)
  (\lam p => \case \elim x, \elim y, \elim p \with { | unit, _, idp => idp })
{%endarend%}

Consider another example: the type {%ard%}\Sigma (x : A) (B x){%endard%} of dependent pairs is a set
if {%ard%}A{%endard%} is a set and {%ard%}B x{%endard%} is a set for all {%ard%}x{%endard%}. 
We need two lemmas to prove this: the first one is the same statement with the word "set" replaced 
with "proposition", and the second one is another variant of the retract lemma:

{%arend%}
\func Sigma-isProp {A : \Type} (B : A -> \Type)
                    (pA : isProp A) (pB : \Pi (x : A) -> isProp (B x))
  : isProp (\Sigma (x : A) (B x)) => \lam p q => sigmaEq B p q (pA _ _) (pB _ _ _)

\func retract'-isProp {A B : \Type} (pB : isProp B) (g : B -> A)
                      (H : \Pi (x : A) -> \Sigma (y : B) (g y = x))
  : isProp A
  => \lam x y => sym (H x).2 *> pmap g (pB (H x).1 (H y).1) *> (H y).2
{%endarend%}

We can now prove that dependent pairs of sets is a set as follows:

{%arend%}
\func Sigma-isSet {A : \Type} (B : A -> \Type)
                  (pA : isSet A) (pB : \Pi (x : A) -> isSet (B x))
  : isSet (\Sigma (x : A) (B x))
  => \lam t t' => retract'-isProp
      {t = t'}
      {\Sigma (p : t.1 = t'.1) (transport B p t.2 = t'.2)}
      (Sigma-isProp (\lam p => transport B p t.2 = t'.2) (pA _ _) (\lam _ => pB _ _ _))
      (\lam s => sigmaEq B t t' s.1 s.2)
      (\lam p => \case \elim t', \elim p \with { | _, idp => ((idp,idp),idp) })
{%endarend%}

**Exercise 9:** Prove that a type with decidable equality is a set. Note that this implies that
{%ard%}Nat{%endard%} is a set since we have already proved that {%ard%}Nat{%endard%} has decidable
equality.
{: .notice--info}

**Exercise 10:** Prove that if {%ard%}A{%endard%} and {%ard%}B{%endard%} are sets, then
{%ard%}A `Or` B{%endard%} is also a set.
{: .notice--info}

**Exercise 11:** Prove that if {%ard%}B x{%endard%} is a set, then {%ard%}\Pi (x : A) -> B x{%endard%} is a set.
{: .notice--info}

**Exercise 12:** Prove that if {%ard%}A{%endard%} is a set, then {%ard%}List A{%endard%} is a set.
{: .notice--info}

# Groupoid structure on types

We conclude with description of a structure that characterizes types of higher homotopy levels. 
The types of homotopy level 1, or 1-types for short, have structure of what is called a _groupoid_:

{%arend%}
\func isGpd (A : \Type) => \Pi (x y : A) -> isSet (x = y)
{%endarend%}

A groupoid is a categorical generalization of the notion of a group: it is a category, where
every morphism is invertible. In particular, all endomorphisms
of any object in a groupoid is a group with composition as the group operation. In the groupoid
of a 1-type {%ard%}A{%endard%} the set of morphisms between objects {%ard%}x y : A{%endard%} is given
by elements of {%ard%}x=y{%endard%}. The identity morphism is {%ard%}idp{%endard%} and the composition
is given by transitivity {%ard%}*>{%endard%} of equality, which turnes out to be in this case a nontrivial
function rather than mere implication:

{%arend%}
\func \infixr 5 *> {A : \Type} {a a' a'' : A} (p : a = a') (q : a' = a'') : a = a''
  \elim q
  | idp => p
{%endarend%}

For example, the universe {%ard%}\Set{%endard%} of sets is 1-type and {%ard%}*>{%endard%} in this case
defines the composition of bijections between sets.

We can prove that {%ard%}*>{%endard%} and {%ard%}idp{%endard%} satisfy the required properties:

{%arend%}
-- 'idp' is left and right identity
\func idp-right {A : \Type} {x y : A} (p : x = y) : p *> idp = p => idp

\func idp-left {A : \Type} {x y : A} (p : x = y) : idp *> p = p \elim p
  | idp => idp

-- * is associative
\func *-assoc {A : \Type} {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
  : (p *> q) *> r = p *> (q *> r) \elim r
  | idp => idp

-- 'sym' is inverse 
\func sym-left {A : \Type} {x y : A} (p : x = y) : sym p *> p = idp
  \elim p
  | idp => idp

\func sym-right {A : \Type} {x y : A} (p : x = y) : p *> sym p = idp
  \elim p
  | idp => idp
{%endarend%}

The function {%ard%}*>{%endard%} is thus similar to a group operation. For example, we can
prove the left cancelation property for it:

{%arend%}
\func cancelLeft {A : \Type} {x y z : A}
                 (p : x = y) (q r : y = z) (s : p *> q = p *> r) : q = r
  \elim p, r
  | idp, idp => sym (idp-left q) *> s
{%endarend%}

We can generalize this structure and define inductively n-groupoid as a category, where morphisms
form (n-1)-groupoid. This is precisely the structure corresponding to homotopy level n, where n>=-1 
is an integer. The types
with infinite homotopy level correspond to infinity-groupoids, which are not necessarily merely
limits of n-groupoids and should be defined in a special way.

**Exercise 13:** Prove that n-types are closed under \Pi-types.
Hint: Proof by induction. For the induction step 'suc n' one should prove that if {%ard%}f,g : \Pi (x : A) -> B x{%endard%},
then {%ard%}f = g{%endard%} is equivalent to {%ard%}\Pi (x : A) -> f x = g x{%endard%}.
{: .notice--info}

