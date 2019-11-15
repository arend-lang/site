---
title: Universes, Induction-Recursion, Specifications
toc: false
nav: universes
---

In this module we take a closer look at the structure of the hierarchy of universes and
explain how polymorphism works.

We discuss more advanced forms of induction and recursion: induction-recursion and recursion-recursion.

We conclude with remarks on writing specifications for functions. 

# Hierarchies of universes, polymorphism

As we mentioned earlier (TODO: ref) there is no the actual type of all types in Arend. 
The type {%ard%}\Type{%endard%} behaves pretty much like the one, but not quite, and the difference
is precisely that {%ard%}\Type{%endard%} cannot be used for contradictory circular definitions.
This is so because {%ard%}\Type{%endard%} actually hides the hierarchy of unverses {%ard%}\Type0{%endard%},
{%ard%}\Type1{%endard%}, ... as we explain below.

The type {%ard%}\Type n{%endard%}, where the natural number {%ard%}n{%endard%} is called _predicative level_
of the universe, contains all types that do not refer to universes or refer to universes {%ard%}\Type i{%endard%}
of lower predicative level i < n. 

{%arend%}
\func tt : \Type2 => \Type0 -> \Type1
{%endarend%}

In order to see how {%ard%}\Type{%endard%} works let's consider a polymorphic definition:

{%arend%}
\func id (A : \Type) (a : A) => a
{%endarend%}

This definition is implicitly polymorphic by the level of the universe of {%ard%}A{%endard%}, that is
it has implicit parameter {%ard%}\lp{%endard%} for the level. The function {%ard%}id{%endard%} above
can equivalently be defined as follows:

{%arend%}
\func id (A : \Type \lp) (a : A) => a
{%endarend%}

Whenever we use {%ard%}\Type{%endard%} without explicit level, the typechecker infers the minimal appropriate
level. Consider the following example:

{%arend%}
\func type : \Type => \Type
{%endarend%}

The typechecker will infer the level {%ard%}\lp{%endard%} for {%ard%}\Type{%endard%} in the body of the function
{%ard%}type{%endard%}. Consequently, the typechecker infers {%ard%}\suc \lp{%endard%} for the level of the universe
in the result type of {%ard%}type{%endard%} since {%ard%}n = \suc \lp{%endard%} is minimal such that 
{%ard%}\Type \lp : \Type n{%endard%}. Thus, the function {%ard%}type{%endard%} can be equivalently rewritten
as follows:

{%arend%}
\func type : \Type (\suc \lp) => \Type \lp
{%endarend%}

There are two operations that allow to form level expressions out of atomic ones: {%ard%}\suc l{%endard%} and
{%ard%}\max l1 l2{%endard%}. Atomic ones, as we have seen, are just nonnegative numerals and polymorphic parameters
{%ard%}\lp{%endard%}. Therefore any level expression is either equivalent to a constant or to an expression of the form
{%ard%}\max (\lp + c) c'{%endard%}, where {%ard%}c, c'{%endard%} are constants and {%ard%}\lp + c{%endard%} is 
the c-fold {%ard%}\suc{%endard%} applied to {%ard%}\lp{%endard%}.

The level of a Pi-type or other type forming construction is the maximal level among all types contained in this construction:

{%arend%}
\func test0 : \Type (\max (\suc (\suc \lp)) 4) => \Type (\max \lp 3) -> \Type (\suc \lp)
{%endarend%}

We now illustrate the behaviour of universes and polymorphic definitions through a bunch of examples:

{%arend%}
\func test1 => id Nat 0
\func test2 => id \Type0 Nat
\func test3 => id (\Type0 -> \Type1) (\lam X => X)
\func test4 => id _ id
\func test4' => id (\Pi (A : \Type) -> A -> A) id
{%endarend%}

While invoking a definition it's possible to specify the value for its polymorphic level parameter {%ard%}\lp{%endard%}.
In case the value is not a numeral, it can be passed as an ordinary first parameter:

{%arend%}
\func test5 => id (\suc \lp) (\Type \lp) Nat
{%endarend%}

Alternatively, it can be done using the construct {%ard%}\level p h{%endard%}, where {%ard%}p{%endard%} is the level
(we ignore {%ard%}h{%endard%} for now). It is useful when the value is numeral.

{%arend%}
\func test5' => id (\level (\suc \lp) _) (\Type \lp) Nat
\func test6 => id (\level 2 _) \Type1 \Type0
{%endarend%}

In case a definition is invoked without explicit specification for the value of its level, the level will be infered
by the typechecker. In most cases there is no need to specify the level explicitly.

The level of the universe of a data definition is the maximum among the levels of parameters of its constructors.
Levels of parameters of the definition do not matter. 

{%arend%}
\data Magma (A : \Type)
  | con (A -> A -> A)

\data MagmaEx (A : \Type) (B : \Type5)
  | con (A -> A -> A)

\func test7 : \Type \lp => MagmaEx \lp Nat \Type4
{%endarend%}

The level of a class or a record is determined by its _non-implemented_ fields and parameters (recall that parameters are
just fields). For example, consider the definition of Magma as a class:

{%arend%}
\class Magma (A : \Type)
  | \infixl 6 ** : A -> A -> A
{%endarend%}

The level of {%ard%}Magma \lp{%endard%} is {%ard%}\Type (\suc \lp){%endard%} since the definition of {%ard%}Magma \lp{%endard%}
contains {%ard%}\Type \lp{%endard%}. But the level of {%ard%}Magma \lp Nat{%endard%} is just {%ard%}\Type0{%endard%} since
non-implemented fields of {%ard%}Magma \lp Nat{%endard%} do not contain universes.

{%arend%}
\func test8 : \Type (\suc \lp) => Magma \lp

\func test9 : \Type \lp => Magma \lp Nat
{%endarend%}

Consider one more example, the class {%ard%}Functor{%endard%} of functors:

{%arend%}
\class Functor (F : \Type -> \Type)
  | fmap {A B : \Type} : (A -> B) -> F A -> F B
{%endarend%}

The level of {%ard%}Functor{%endard%} will be {%ard%}\Type (\suc \lp){%endard%} even if the field {%ard%}F{%endard%} is
implemented since {%ard%}fmap{%endard%} also refers to {%ard%}\Type \lp{%endard%}.

{%arend%}
\data Maybe (A : \Type) | nothing | just A

\func test10 : \Type (\suc \lp) => Functor \lp Maybe
{%endarend%}

# Induction principles

We have already seen that data types have canonical eliminators associated to them and that
non-dependent and dependent eliminators correspond to recursion and indunction principles 
respectively. It is also possible to define custom eliminators and, thus, custom induction
principles that in some case are more convenient to use. For example, we can define an
induction principle for natural numbers that allows to use induction hypothesis for _any_
number less than the current one, not just for the number less by one:

{%arend%}
\func Nat-ind (E : Nat -> \Type)
  (r : \Pi (n : Nat) -> (\Pi (k : Nat) -> T (k < n) -> E k) -> E n)
  (n : Nat) : E n => {?} -- prove this as an exercise
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

Let's define a custom universe containing some custom set of types:

{%arend%}
\data Type
  | nat
  | list Type
  | arr Type Type
{%endarend%}

The type {%ard%}Type{%endard%} can be thought of as a type contains codes of types. We should also define a
function that realizes them as actual types:

{%arend%}
\func El (t : Type) : \Type0 \elim t
  | nat => Nat
  | list t => List (El t)
  | arr t1 t2 => El t1 -> El t2

\func idc (t : Type) (x : El t) : El t => x
{%endarend%}

The universe {%ard%}Type{%endard%} contains just non-dependent types. If we want to include also dependent types
to the universe, we should use induction-recursion:

{%arend%}
\data Type' : \Type0
  | nat'
  | list' Type'
  | pi' (a : Type') (El' a -> Type')

\func El' (t : Type') : \Type0 \elim t
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
factorial:

{%arend%}
-- P1 is correct specification for 'fac', but incomplete.
\func P1 (f : Nat -> Nat) => f 3 = 6
-- P2 is complete, but not correct.
\func P2 (f : Nat -> Nat) => Empty
-- P3 -- correct and complete specification for 'fac'.
\func P3 (f : Nat -> Nat) => \Sigma (f 0 = 1) (\Pi (n : Nat) -> f (suc n) = suc n * f n)
{%endarend%}

Another example -- correct and complete specification for a sort function:

{%arend%}
\func P (f : List A -> List A) => \Pi (xs : List A) -> \Sigma (isSorted (f xs)) (isPerm (f xs) xs)
-- where 'isSorted xs' is true iff  'xs' is sorted and
-- 'isPerm xs ys' is true iff 'xs' is a permutation of 'ys'.
{%endarend%}

Of course, specifications must always be correct, but one may opt for working with incomplete specifications
since sometimes it's too hard to write and prove the complete one. Nevertheless, it's useful to understand,
when a specification is complete. One useful necessary and sufficient condition of completeness for correct
specifications can be formulated as follows:

{%arend%}
\Pi (x y : A) -> P x -> P y -> x = y
{%endarend%}
