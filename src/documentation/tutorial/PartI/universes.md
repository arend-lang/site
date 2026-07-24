---
title: Universes, Induction, Specifications
nav: universes
---

The source code for this module: [PartI/Universes.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/Universes.ard),
 [PartI/sort.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/sort.ard) \\
The source code for the exercises: [PartI/UniversesEx.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/Exercises/UniversesEx.ard)
{: .notice--success}

In this module we take a closer look at the structure of the hierarchy of universes and
explain how polymorphism works.

We discuss more advanced forms of induction and recursion: induction-recursion and recursion-recursion.

We conclude with remarks on writing specifications for functions. 

# Hierarchies of universes, polymorphism

As we mentioned [earlier](synndef#polymorphism) there is no actual type of all types in Arend. 
The type {%ard%}\Type{%endard%} behaves pretty much like the one, but not quite, and the difference
is precisely that {%ard%}\Type{%endard%} cannot be used for contradictory circular definitions.
This is so because {%ard%}\Type{%endard%} actually hides the hierarchy of universes {%ard%}\Type0{%endard%},
{%ard%}\Type1{%endard%}, ... as we explain below.

The type {%ard%}\Type n{%endard%}, where the natural number {%ard%}n{%endard%} is called _the predicative level_
of the universe, contains all types that do not refer to universes or refer to universes {%ard%}\Type i{%endard%}
of lower predicative level i < n. 

{%arend%}
\func tt : \Type2 => \Type0 -> \Type1
{%endarend%}

In order to see how {%ard%}\Type{%endard%} works let us consider a definition parameterized by a type:

{%arend%}
\func id (A : \Type) (a : A) => a
{%endarend%}

When {%ard%}\Type{%endard%} is written without an explicit level, it denotes the universe with the
_infinite_ predicative level, that is the universe that contains {%ard%}\Type n{%endard%} for every
{%ard%}n{%endard%}. So the parameter {%ard%}A{%endard%} above ranges over this single infinite universe,
which is convenient when we do not care about the level. Note that the infinite {%ard%}\Type{%endard%} is
not itself a small type, hence it is not a member of any {%ard%}\Type n{%endard%} (in particular, not of
itself); this is exactly what rules out contradictory circular definitions. For the same reason a
definition such as {%ard%}\func bad : \Type => \Type{%endard%} is not allowed.

Thus {%ard%}id{%endard%} above is _not_ polymorphic in the level. To make a definition genuinely
polymorphic in the predicative level, we declare one or more named _level parameters_ right after its
name using the syntax {%ard%}.{...}{%endard%}, and refer to them in universes such as {%ard%}\Type l{%endard%}:

{%arend%}
\func id.{l} (A : \Type l) (a : A) => a
{%endarend%}

Now {%ard%}id{%endard%} has a level parameter {%ard%}l{%endard%} and works uniformly for every predicative
level. Level polymorphism is always explicit: a definition is polymorphic in the predicative level only if it
declares a level parameter.

The level of a universe is one higher than the level of its elements: {%ard%}\Type l : \Type (\suc l){%endard%},
and {%ard%}n = \suc l{%endard%} is minimal such that {%ard%}\Type l : \Type n{%endard%}. So a function that
returns the universe {%ard%}\Type l{%endard%} has result type {%ard%}\Type (\suc l){%endard%}:

{%arend%}
\func type.{l} : \Type (\suc l) => \Type l
{%endarend%}

There are two operations that allow to form level expressions out of atomic ones: {%ard%}\suc l{%endard%} and
{%ard%}\max l1 l2{%endard%}. Atomic level expressions are just nonnegative numerals and level parameters (such
as {%ard%}l{%endard%} above). Therefore any level expression built from a single parameter {%ard%}l{%endard%} is
either equivalent to a constant or to an expression of the form {%ard%}\max (l + c) c'{%endard%}, where
{%ard%}c, c'{%endard%} are constants and {%ard%}l + c{%endard%} is the c-fold {%ard%}\suc{%endard%} applied to
{%ard%}l{%endard%}.

The level of a Pi-type or other type forming construction is the maximal level among all types contained in this construction:

{%arend%}
\func test0.{l} : \Type (\max (\suc (\suc l)) 4) => \Type (\max l 3) -> \Type (\suc l)
{%endarend%}

We now illustrate the behaviour of universes and polymorphic definitions through a bunch of examples:

{%arend%}
\func test1 => id Nat 0
\func test2 => id \Type0 Nat
\func test3 => id (\Type0 -> \Type1) (\lam X => X)
\func test4.{l} => id (\Pi (A : \Type l) -> A -> A) id
{%endarend%}

When invoking a definition it is possible to specify the values of its level parameters explicitly, again with
the {%ard%}.{...}{%endard%} syntax. The arguments are level expressions, listed in the order in which the
parameters were declared:

{%arend%}
\func test5.{l} => id.{\suc l} (\Type l) Nat
\func test6 => id.{2} \Type1 \Type0
{%endarend%}

(The older ways of passing a level — positionally as an ordinary first argument, or via the {%ard%}\levels p h{%endard%}
construct — no longer exist. Homotopy levels have been removed, so a level argument is now a single predicative level.)

In case a definition is invoked without explicit specification for the values of its levels, they will be inferred
by the typechecker. In most cases there is no need to specify them explicitly.

The level of the universe of a data definition is the maximum among the levels of parameters of its constructors.
Levels of parameters of the definition do not matter. 

{%arend%}
\data Magma.{l} (A : \Type l)
  | con (A -> A -> A)

\data MagmaEx.{l} (A : \Type l) (B : \Type5)
  | con (A -> A -> A)

\func test7.{l} : \Type l => MagmaEx.{l} Nat \Type4
{%endarend%}

The level of a class or a record is determined by its _non-implemented_ fields and parameters (recall that parameters are
just fields). For example, consider the definition of Magma as a class:

{%arend%}
\class Magma.{l} (A : \Type l)
  | \infixl 6 ** : A -> A -> A
{%endarend%}

The level of {%ard%}Magma.{l}{%endard%} is {%ard%}\Type (\suc l){%endard%} since the definition of {%ard%}Magma.{l}{%endard%}
contains {%ard%}\Type l{%endard%}. Once the field {%ard%}A{%endard%} is implemented, that universe disappears from the
non-implemented fields and the level drops by one: {%ard%}Magma.{l} Nat{%endard%} lives in {%ard%}\Type l{%endard%}
(for instance {%ard%}Magma.{5} Nat : \Type5{%endard%}).

{%arend%}
\func test8.{l} : \Type (\suc l) => Magma.{l}

\func test9.{l} : \Type l => Magma.{l} Nat
{%endarend%}

Consider one more example, the class {%ard%}Functor{%endard%} of functors. Unlike {%ard%}\Type{%endard%}, the universe
{%ard%}\Set{%endard%} cannot be used with the infinite level, so it always requires an explicit predicative level:

{%arend%}
\class Functor.{l} (F : \Set l -> \Set l) -- \Set is almost the same as \Type, we will discuss the difference later
  | fmap {A B : \Set l} : (A -> B) -> F A -> F B
{%endarend%}

The level of {%ard%}Functor.{l}{%endard%} will be {%ard%}\Type (\suc l){%endard%} even if the field {%ard%}F{%endard%} is
implemented since {%ard%}fmap{%endard%} also refers to {%ard%}\Set l{%endard%}.

{%arend%}
\data Maybe.{l} (A : \Set l) | nothing | just A

\func test10.{l} : \Type (\suc l) => Functor.{l} Maybe
{%endarend%}

**Exercise 1:** Calculate the levels in each of the invocations of {%ard%}id''{%endard%} below.
Specify explicitly the result types for all idTest* (giving a result type also pins down the levels).
{: .notice--info}
{%arend%}
\func id''.{l} {A : \Type l} (a : A) => a

\func idTest1 => id'' (id'' id)
\func idTest2 => id'' Maybe
\func idTest3 => id'' Functor
\func idTest4 => id'' (Functor Maybe)
\func idTest5.{l} (f : \Pi {A B : \Set l} -> (A -> B) -> Maybe A -> Maybe B) => id'' (Functor Maybe f)
{%endarend%}


# Induction principles

We have already seen that data types have canonical eliminators associated with them and that
non-dependent and dependent eliminators correspond to recursion and induction principles
respectively. It is also possible to define custom eliminators and, thus, custom induction
principles that in some case are more convenient to use. For example, we can define an
induction principle for natural numbers that allows to use induction hypothesis for _any_
number less than the current one, not just for the number less by one:

{%arend%}
\func Nat-ind (E : Nat -> \Type)
  (r : \Pi (n : Nat) -> (\Pi (k : Nat) -> T (k < n) -> E k) -> E n)
  (n : Nat) : E n => {?} -- prove this as an exercise
{%endarend%}

**Exercise 2:** Define {%ard%}div{%endard%} via {%ard%}Nat-ind{%endard%}.
{: .notice--info}	
{%arend%}
\func div (n k : Nat) (p : T (0 < k)) : Nat => {?}
{%endarend%}


**Exercise 3:** Prove the following induction principle for lists:
{: .notice--info}
{%arend%}
\func List-ind
  {A : \Type}
  (E : List A -> \Type)
  (r : \Pi (xs : List A) -> (\Pi (ys : List A) -> T (length ys < length xs) -> E ys) -> E xs)
  (xs : List A) : E xs => {?}
{%endarend%}


# Induction-recursion

Recursion-recursion -- is a principle, allowing to define mutually recursive functions. For example,
consider function {%ard%}isOdd{%endard%} and {%ard%}isEven{%endard%}:

{%arend%}
\func isEven (n : Nat) : Bool
  | 0 => true
  | suc n => isOdd n

\func isOdd (n : Nat) : Bool
  | 0 => false
  | suc n => isEven n
{%endarend%}

Induction-induction -- is a principle, allowing to define mutually recursive data types. In case
a data type is a part of mutually inductive definition, its type must be specified explicitly.
Consider the types {%ard%}IsOdd{%endard%} and {%ard%}IsEven{%endard%}:

{%arend%}
\data IsEven (n : Nat) : \Type \with
  | 0 => zero-isEven
  | suc n => suc-isEven (IsOdd n)

\data IsOdd (n : Nat) : \Type \with
  | suc n => suc-isOdd (IsEven n)
{%endarend%}

Induction-recursion -- is a principle, allowing to define data types and functions that are mutually recursive.
For example, this construct allows to define universes of types as data types. We will explain how it can be
done below.

# Universes via induction-recursion

Let us define a custom universe containing some custom set of types:

{%arend%}
\data Type
  | nat
  | list Type
  | arr Type Type
{%endarend%}

The type {%ard%}Type{%endard%} can be thought of as a type that contains codes of types. We should also define a
function that realizes them as actual types:

{%arend%}
\func El (t : Type) : \Set0 \elim t
  | nat => Nat
  | list t => List (El t)
  | arr t1 t2 => El t1 -> El t2

\func idc (t : Type) (x : El t) : El t => x
{%endarend%}

The universe {%ard%}Type{%endard%} contains just non-dependent types. If we want to include also dependent types
to the universe, we should use induction-recursion:

{%arend%}
\data Type' : \Set0
  | nat'
  | list' Type'
  | pi' (a : Type') (El' a -> Type')

\func El' (t : Type') : \Set0 \elim t
  | nat' => Nat
  | list' t => List (El' t)
  | pi' t1 t2 => \Pi (a : El' t1) -> El' (t2 a)
{%endarend%}

# Completeness of specifications

Specification for an element of type {%ard%}A{%endard%} is simply a predicate {%ard%}P : A -> \Type{%endard%},
describing the property of an element that we want to prove. 

A specification {%ard%}P{%endard%} is _correct_ for {%ard%}a : A{%endard%} if {%ard%}P a{%endard%} is provable.
A specification {%ard%}P{%endard%} is _complete_ for {%ard%}a : A{%endard%} if {%ard%}P x{%endard%} implies 
{%ard%}x=a{%endard%} for all {%ard%}x : A{%endard%}.

For example, assume we want to write specification for a function {%ard%}fac : Nat -> Nat{%endard%} that computes
the factorial of a number:

{%arend%}
-- P1 is correct specification for 'fac', but incomplete.
\func P1 (f : Nat -> Nat) => f 3 = 6
-- P2 is complete, but not correct.
\func P2 (f : Nat -> Nat) => Empty
-- P3 -- correct and complete specification for 'fac'.
\func P3 (f : Nat -> Nat) => \Sigma (f 0 = 1) (\Pi (n : Nat) -> f (suc n) = suc n * f n)
{%endarend%}

Another example of a correct and complete specification for a sort function:

{%arend%}
\func P (f : List A -> List A) => \Pi (xs : List A) -> \Sigma (isSorted (f xs)) (isPerm (f xs) xs)
-- where 'isSorted xs' is true iff  'xs' is sorted and
-- 'isPerm xs ys' is true iff 'xs' is a permutation of 'ys'.
{%endarend%}

Of course, specifications must always be correct, but one may opt for working with incomplete specifications
since sometimes it is too hard to write and prove a complete one. Nevertheless, it is useful to understand,
when a specification is complete. One useful necessary and sufficient condition of completeness for correct
specifications can be formulated as follows:

{%arend%}
\Pi (x y : A) -> P x -> P y -> x = y
{%endarend%}

**Exercise 4:** Implement function {%ard%}filter{%endard%} and prove that it is correct, that is that the following holds:
 a) {%ard%}filter p xs{%endard%} is a sublist of {%ard%}xs{%endard%},
 b) All elements of {%ard%}filter p xs{%endard%} satisfy the predicate {%ard%}p{%endard%},
 c) Any sublist of {%ard%}xs{%endard%} with property (b) is a sublist of {%ard%}filter p xs{%endard%}.
{: .notice--info}


# Correctness of Insertion Sort

We now finally prove the correctness of the insertion sort algorithm, defined in [Indexed Data Types](datanproofs):
{%arend%}
\func sort {A : TotalPreorder} (xs : List A) : List A
  | nil => nil
  | cons a xs => insert a (sort xs)
  \where
    \func insert {A : TotalPreorder} (a : A) (xs : List A) : List A \elim xs
      | nil => cons a nil
      | cons x xs => \case totality x a \with {
        | inl _ => cons x (insert a xs)
        | inr _ => cons a (cons x xs)
      }
{%endarend%}

The full specification of the sort function consists of two properties:
* {%ard%}sort xs{%endard%} is a sorted list.
* {%ard%}sort xs{%endard%} is a permutation of {%ard%}xs{%endard%}.
We begin with the latter property.
It can be defined in several different (but equivalent) ways.
We will use an interesting option: instead of giving its definition from the start, we begin with an empty data type and add more constructors as needed:
{%arend%}
\data Perm {A : \Type} (xs ys : List A)
{%endarend%}

Of course, the proof proceeds by induction on the list:
{%arend%}
\func sort-perm {A : TotalPreorder} (xs : List A) : Perm xs (sort xs) \elim xs
  | nil => {?}
  | cons a l => {?}
{%endarend%}
In the first goal, we need to show that the empty list is a permutation of itself.
To do this, we need to add the first constructor to {%ard%} Perm {%endard%}:
{%arend%}
\data Perm {A : \Type} (xs ys : List A) \elim xs, ys
  | nil, nil => perm-nil
{%endarend%}

In the second goal, we need to show that {%ard%} cons a l {%endard%} is a permutation of {%ard%} insert a (sort l) {%endard%}.
Clearly, we need to use the induction hypothesis and we also need to prove some lemma about {%ard%} insert {%endard%} function.
There is an obvious property of this function related to permutation:
{%arend%}
\func insert-perm {A : TotalPreorder} (a : A) (xs : List A) : Perm (cons a xs) (sort.insert a xs) => {?}
{%endarend%}
This lemma implies that {%ard%} insert a (sort l) {%endard%} is a permutation of {%ard%} cons a (sort l) {%endard%}.
We can combine this property with the induction hypothesis to obtain the required result.
To do this, we need to know the following facts:
* Permutations are closed under {%ard%} cons a {%endard%} so that we can conclude that {%ard%} cons a (sort l) {%endard%} is a permutation of {%ard%} cons a l {%endard%},
* {%ard%} Perm {%endard%} is a transitive relation so that we can combine two proofs.

We add two new constructors to {%ard%} Perm {%endard%} which reflect these properties.
At this point, our proof looks like this:
{%arend%}
\data Perm {A : \Type} (xs ys : List A) \elim xs, ys
  | nil, nil => perm-nil
  | cons x xs, cons y ys => perm-cons (x = y) (Perm xs ys)
  | xs, ys => perm-trans {zs : List A} (Perm xs zs) (Perm zs ys)

\func sort-perm {A : TotalPreorder} (xs : List A) : Perm xs (sort xs) \elim xs
  | nil => perm-nil
  | cons a l => perm-trans (perm-cons idp (sort-perm l)) (insert-perm a (sort l))
  \where
    \func insert-perm {A : TotalPreorder} (a : A) (xs : List A) : Perm (cons a xs) (sort.insert a xs) => {?}
{%endarend%}

The proof of {%ard%} insert-perm {%endard%} also proceeds by induction on the list.
The {%ard%} nil {%endard%} case is easy: we just need to show that {%ard%} cons a nil {%endard%} is a permutation of itself.
In the {%ard%} cons {%endard%} case, we need to decide whether {%ard%} b <= a {%endard%} or {%ard%} a <= b {%endard%}.
We can do this by using {%ard%} \case {%endard%}:
{%arend%}
\func insert-perm {A : TotalPreorder} (a : A) (xs : List A) : Perm (cons a xs) (sort.insert a xs) \elim xs
  | nil => perm-cons idp perm-nil
  | cons b l => \case totality b a \as r \return
                                          Perm (cons a (cons b l)) (\case r \with {
                                            | inl _ => cons b (sort.insert a l)
                                            | inr _ => cons a (cons b l)
                                          }) \with {
    | inl b<=a => {?}
    | inr a<=b => {?}
  }
{%endarend%}

The second subgoal is easy: we need to prove that {%ard%} cons a (cons b l) {%endard%} is a permutation of itself.
We can show that {%ard%} Perm {%endard%} is reflexive using constructors that we already added:
{%arend%}
\func perm-refl {A : \Type} {xs : List A} : Perm xs xs \elim xs
  | nil => perm-nil
  | cons a l => perm-cons idp perm-refl
{%endarend%}

In the first subgoal, we need to prove that {%ard%} cons a (cons b l) {%endard%} is a permutation of {%ard%} cons b (insert a l) {%endard%}.
By the induction hypothesis and transitivity of {%ard%} Perm {%endard%}, we can reduce this problem to the problem of showing that {%ard%} cons a (cons b l) {%endard%} is a permutation of {%ard%} cons b (cons a l) {%endard%}.
To prove this, we need to add yet another constructor to {%ard%} Perm {%endard%}:

{%arend%}
\data Perm {A : \Type} (xs ys : List A) \elim xs, ys
  | nil, nil => perm-nil
  | cons x xs, cons y ys => perm-cons (x = y) (Perm xs ys)
  | xs, ys => perm-trans {zs : List A} (Perm xs zs) (Perm zs ys)
  | cons x (cons x' xs), cons y (cons y' ys) => perm-perm (x = y') (x' = y) (xs = ys)
{%endarend%}

Now, we can finish the proof of {%ard%} insert-perm {%endard%}:

{%arend%}
\func insert-perm {A : TotalPreorder} (a : A) (xs : List A) : Perm (cons a xs) (sort.insert a xs) \elim xs
  | nil => perm-cons idp perm-nil
  | cons b l => \case totality b a \as r \return
                                          Perm (cons a (cons b l)) (\case r \with {
                                            | inl _ => cons b (sort.insert a l)
                                            | inr _ => cons a (cons b l)
                                          }) \with {
    | inl b<=a => perm-trans (perm-perm idp idp idp) (perm-cons idp (insert-perm a l))
    | inr a<=b => perm-refl
  }
{%endarend%}

Our definition of {%ard%} Perm {%endard%} might look like cheating, but it is a perfectly valid definition of this predicate.
It might happen that we already have some fixed definition {%ard%} Perm' {%endard%} of this predicate and we want to prove that our sort function satisfies the required property with respect to {%ard%} Perm' {%endard%}.
In this case, we just need to prove that {%ard%} Perm xs ys {%endard%} implies {%ard%} Perm' xs ys {%endard%}.
It is easy to do this: we just need to show that {%ard%} Perm' {%endard%} satisfies 4 properties corresponding to 4 constructors of {%ard%} Perm {%endard%}.
We can even omit the intermediate step and replace {%ard%} Perm {%endard%} with {%ard%} Perm' {%endard%} and constructors of {%ard%} Perm {%endard%} with the proofs of corresponding properties.

Now, let us prove the remaining property of the sort function.
We will define predicate {%ard%} IsSorted {%endard%} inductively.
The empty list is always sorted and {%ard%} cons x xs {%endard%} is sorted if {%ard%} xs {%endard%} is sorted and {%ard%} x {%endard%} is less than or equal to the head of {%ard%} xs {%endard%}.
The problem is that {%ard%} xs {%endard%} might be empty, in which case the last property does not make sense.
We can consider three cases instead of two and define {%ard%} IsSorted {%endard%} as follows:
{%arend%}
\data IsSorted {A : Preorder} (xs : List A) \with
  | nil => nil-sorted
  | cons _ nil => single-sorted
  | cons x (cons y _ \as xs) => cons-sorted (x <= y) (IsSorted xs)
{%endarend%}

It turns out that this definition is not very convenient because we need to consider more cases when proving things about sorted lists.
There is another option: we can define the {%ard%} head {%endard%} that returns some default value when the list is empty:
{%arend%}
\func head {A : \Type} (def : A) (xs : List A) : A \elim xs
  | nil => def
  | cons a _ => a
{%endarend%}

Now, we can define predicate {%ard%} IsSorted {%endard%} as follows:
{%arend%}
\data IsSorted {A : Preorder} (xs : List A) \elim xs
  | nil => nil-sorted
  | cons x xs => cons-sorted (x <= head x xs) (IsSorted xs)
{%endarend%}

If {%ard%} xs {%endard%} is not empty, then condition {%ard%} x <= head x xs {%endard%} asserts that {%ard%} x {%endard%} is less than or equal to the head of {%ard%} xs {%endard%}.
If {%ard%} xs {%endard%} is empty, then condition {%ard%} x <= head x xs {%endard%} is always true by reflexivity of {%ard%} <= {%endard%}.

The rest of the proof is straightforward.
We formulate an obvious lemma about the {%ard%} insert {%endard%} function and prove the required property by induction:
{%arend%}
\func sort-sorted {A : TotalPreorder} (xs : List A) : IsSorted (sort xs) \elim xs
  | nil => nil-sorted
  | cons a l => insert-sorted a (sort-sorted l)
  \where {
    \func insert-sorted {A : TotalPreorder} (x : A) {xs : List A} (xs-sorted : IsSorted xs) : IsSorted (sort.insert x xs) => {?}
  }
{%endarend%}

The proof of the lemma is also a straightforward induction:
{%arend%}
\func insert-sorted {A : TotalPreorder} (x : A) {xs : List A} (xs-sorted : IsSorted xs) : IsSorted (sort.insert x xs) \elim xs
  | nil => cons-sorted <=-refl nil-sorted
  | cons a l => \case totality a x \as r \return
                                          IsSorted (\case r \with {
                                            | inl _ => cons a (sort.insert x l)
                                            | inr _ => cons x (cons a l)
                                          }) \with {
    | inl a<=x => \case xs-sorted \with {
      | cons-sorted a<=l l-sorted => cons-sorted (insert-lem a x l a<=x a<=l) (insert-sorted x l-sorted)
    }
    | inr x<=a => cons-sorted x<=a xs-sorted
  }
{%endarend%}

In the case {%ard%} inl a<=x {%endard%}, we need another auxiliary lemma with a simple proof by case analysis:
{%arend%}
\func insert-lem {A : TotalPreorder} (a x : A) (l : List A) (a<=x : a <= x) (a<=l : a <= head a l) : a <= head a (sort.insert x l) \elim l
  | nil => a<=x
  | cons b l => \case totality b x \as r \return
                                          a <= head a (\case r \with {
                                            | inl _ => cons b (sort.insert x l)
                                            | inr _ => cons x (cons b l)
                                          }) \with {
    | inl _ => a<=l
    | inr _ => a<=x
  }
{%endarend%}

This completes the proof of correctness of {%ard%} sort {%endard%}.
The full proof can be found [here](code/sort.ard).

**Exercise:** Implement another sorting algorithm and prove its correctness.
{: .notice--info}
