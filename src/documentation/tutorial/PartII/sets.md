---
title: Basic Set Theory
nav: set-theory
---

The source code for this module: [PartII/Sets.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartII/src/Sets.ard) \\
The source code for the exercises: [PartII/SetsEx.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartII/src/Exercises/SetsEx.ard)
{: .notice--success}

The types, which are sets according to the view adopted in the last modules, behave like sets in set theory.
This means that many theorems of set theory can be proven for the sets in this sense. 

For example, we can prove the Cantor's theorem saying that the cardinality of a set {%ard%}X{%endard%} is 
strictly less than the cardinality of the set of its subsets {%ard%}X -> \Prop{%endard%}.

The assertion that the cardinality is less (not necessarily strictly) means that there exists injection 
of {%ard%}X{%endard%} into {%ard%}X -> \Prop{%endard%}. Clearly, the equality predicate 
{%ard%}(=) : X -> (X -> \Prop){%endard%} is an injection.

The assetrion that the cardinality is strictly less means that, in addition, there is no surjection 
{%ard%}f : X -> (X -> \Prop){%endard%}. This can be easily proven by adopting the classical Cantor's
argument.

Note, however, that a number of theorems of the classical set theory are not provable in type theory
without assuming the excluded middle or the axiom of choice. For example, the Schroder-Bernstein 
theorem, which says that if for two sets there exist injective functions both ways between them then
there exists a bijection between them, is not provable without excluded middle. 

# Surjections, injections and bijections

We have already seen the definitions of injection and surjections, but let us briefly recall it. 
Note that the definition of surjection requires the propositional truncation.

{%arend%}
\func isInj {A B : \Set} (f : A -> B) => \Pi (x y : A) -> f x = f y -> x = y

\truncated \data Trunc (A : \Type) : \Prop
  | in A
  \where {
    \func map {A B : \Type} (f : A -> B) (x : Trunc A) : Trunc B \elim x
      | in a => in (f a)

    \lemma extract {A : \Type} (x : Trunc A) (p : isProp A) : \level A p \elim x
      | in a => a
  }

-- Note that \Sigma (a : A) (f a = b) is not
-- necessarily a proposition and should be truncated.
\func isSur {A B : \Set} (f : A -> B) : \Prop =>
     \Pi (b : B) -> Trunc (\Sigma (a : A) (f a = b))
  -- \Pi (b : B) ->        \Sigma (a : A) (f a = b)
{%endarend%}

We now give an obvious definition of a bijection and prove that bijectivity
is a conjuction of injectivity and surjectivity.

{%arend%}
\func isBij {A B : \Set} (f : A -> B) => \Sigma (g : B -> A) (\Pi (x : A) -> g (f x) = x) (\Pi (y : B) -> f (g y) = y)

\func isBij->isInj {A B : \Set} (f : A -> B) (p : isBij f) : isInj f => \lam x y q => sym (p.2 x) *> pmap p.1 q *> p.2 y

\func isBij->isSur {A B : \Set} (f : A -> B) (p : isBij f) : isSur f => \lam b => in (p.1 b, p.3 b)

\func sigmaEq' {A : \Type} (B : A -> \Prop) (t1 t2 : \Sigma (x : A) (B x)) (p : t1.1 = t2.1)
  => sigmaEq B t1 t2 p (Path.inProp _ _)

\func isInj+isSur->isBij {A B : \Set} (f : A -> B) (ip : isInj f) (sp : isSur f) : isBij f
  => \let t (b : B) => Trunc.extract (sp b) (\lam t1 t2 => sigmaEq' (\lam a => f a = b) t1 t2 (ip t1.1 t2.1 (t1.2 *> sym t2.2)))
     \in (\lam b => (t b).1, \lam a => ip _ _ (t (f a)).2, \lam b => (t b).2)
{%endarend%}

**Exercise 1:** Prove that the predecessor function {%ard%}pred{%endard%} on {%ard%}Nat{%endard%} is surjective.
{: .notice--info}

**Exercise 2:** Prove that {%ard%}suc{%endard%} is not surjective.
{: .notice--info}

**Exercise 3:** Let {%ard%}f : A -> B{%endard%} and {%ard%}g : B -> C{%endard%} be some functions.
    Prove that if {%ard%}f{%endard%} and {%ard%}g{%endard%} are surjective, then {%ard%}g `o` f{%endard%} is also surjective.
    Prove that if {%ard%}g `o` f{%endard%} is surjective, then {%ard%}g{%endard%} is also surjective.
{: .notice--info}

**Exercise 4:** Prove the Cantor's theorem.
{: .notice--info}


# A definition of Int, datatypes with conditions

Here we introduce a useful construct for data definitions, which allows quotioning
or, in other words, gluing, and apply it to the definition of the type {%ard%}Int{%endard%}
of integers.

Consider first the definition of the type of integers as the ordinary datatype containing
two copies of {%ard%}Nat{%endard%}: nonegative and nonpositive numbers.

{%arend%}
\data Int'
  | pos' Nat
  | neg' Nat
{%endarend%}

Totalities of elements defined by different constructors in an ordinary datatype do
not intersect. For example, we can prove that {%ard%}pos' n{%endard%} is always not
equal to {%ard%}neg' m{%endard%}. Sometimes it is not convenient: for example, 
we would like {%ard%}pos' 0{%endard%} to be the same as {%ard%}neg' 0{%endard%}.

It is possible to specify such identifications of constructors by supplementing
definitions of constructors with conditions. The syntax for conditions is the same
as for functions defined by pattern matching. The only differences are that
some cases can be uncovered and matching on the interval type {%ard%}I{%endard%} is allowed.

Let us modify the definition of integers as follows:

{%arend%}
\data Int
  | pos Nat
  | neg (n : Nat) \elim n {
    | 0 => pos 0
  }
{%endarend%}

The new definition {%ard%}Int{%endard%} now has a useful property that {%ard%}neg 0{%endard%}
evaluates to {%ard%}pos 0{%endard%}.

Whenever a function over such a type is defined, the typechecker checks if its 
values on equivalent constructors coincide. For example, the following definition
does not typecheck, because {%ard%}intEx (pos 0){%endard%} is 3, but 
{%ard%}intEx (pos 0){%endard%} is 7:

{%arend%}
-- This does not typecheck!
\func intEx (z : Int) : Nat
  | pos n => 3
  | neg n => 7
{%endarend%}

We can fix this by replacing the second pattern with {%ard%}neg (suc n){%endard%} and 
omitting the pattern {%ard%}neg 0{%endard%} since it evaluates:

{%arend%}
\func intEx' (z : Int) : Nat
  | pos n => 3
  | neg (suc n) => 7
{%endarend%}

Let us give a couple of examples of functions over {%ard%}Int{%endard%}:

{%arend%}
\func negative (x : Int) : Int
  | pos n => neg n
  | neg n => pos n

\func abs (x : Int) : Nat
  | pos n => n
  | neg n => n
{%endarend%}

**Exercise 5:** Define the function {%ard%}negPred : Int -> Int{%endard%} such that 
{%ard%}negPred x = x{%endard%} if {%ard%}x > 0{%endard%} and {%ard%}negPred x = x - 1{%endard%}
if {%ard%}x <= 0{%endard%}.
{: .notice--info}

**Exercise 6:** Define addition and multiplication for {%ard%}Int{%endard%}.
{: .notice--info}

**Exercise 7:** Define the datatype {%ard%}BinNat{%endard%} for the binary natural numbers.
    It should have three constructors: for 0, for even numbers 2n and for odd numbers 2n+1.
    This type contains several different representations of zero.
    Use datatypes with conditions to identify different representations of zero.
{: .notice--info}

**Exercise 8:** Define mutually inverse functions {%ard%}Nat -> BinNat{%endard%} and {%ard%}BinNat -> Nat{%endard%}
 and prove that they are mutually inverse. 
{: .notice--info}


# Quotient sets

Let {%ard%}A{%endard%} be a set together with an equivalence relation ~ on it. 
We can define the _quotient set_ {%ard%}A/~{%endard%} together with the function 
{%ard%}in~ : A -> A/~{%endard%} such that any two equivalent elements of {%ard%}A{%endard%}
are identified in {%ard%}A/~{%endard%}. 

{%arend%}
A : \Set
~ : A -> A -> \Prop
A/~ : \Set
in~ : A -> A/~
(in~ a = in~ a') <-> (a ~ a')
{%endarend%}

A function over {%ard%}A/~{%endard%} can be defined as a function over {%ard%}A{%endard%}
satisfying the condition that equivalent elements are mapped to equal elements. With
the proof of the condition omitted and using simplified syntax (the full definition is given below)
we can write:

{%arend%}
-- A simplification. This is not intended to be typechecking.
\func f (x : A/~) : B
   | in~ a => b
{%endarend%}

An important of example of quotient set -- the set of rational numbers, which is defined
as the set of pairs of natural numbers quotioned by the equivalence relation ~ such that
{%ard%}(n, m) ~ (n', m'){%endard%} iff {%ard%}n * m' = n' * m{%endard%}.

We can define the quotient set as a datatype with conditions: we simply add
an equality between {%ard%}inR a{%endard%} and {%ard%}inR a'{%endard%} if
{%ard%}R a a'{%endard%}.

{%arend%} 
\truncated \data Quotient (A : \Type) (R : A -> A -> \Type) : \Set
  | inR A
  | eq (a a' : A) (r : R a a') (i : I) \elim i {
    | left => inR a
    | right => inR a'
  }
{%endarend%}

Note that we have to use the truncation to the level of sets, otherwise we will
not get a set.

The equivalent elements are indeed equal:

{%arend%}
\func quotientEq {A : \Type} {R : A -> A -> \Type} (a a' : A) (r : R a a')
  : inR a = {Quotient A R} inR a'
  => path (eq a a' r)
{%endarend%}

We can prove, for example, that {%ard%}inR{%endard%} is surjective:

{%arend%}
\func inR-sur {A : \Type} {R : A -> A -> \Type} : isSur (inR {A} {R}) =>
  \lam [a] => \case \elim [a] \with {
    | inR a => in (a, idp)
  }
{%endarend%}

If we want to define a function over {%ard%}Quotient A R{%endard%} we need
to define a function on elements of the form {%ard%}inR a{%endard%} and 
on the constructor {%ard%}eq{%endard%}. The latter corresponds to a proof
that the function maps equivalent elements to equal values.

{%arend%}
\func quotientEx {A : \Type} {R : A -> A -> \Type} {B : \Set}
                 (f : A -> B) (p : \Pi (a a' : A) -> R a a' -> f a = f a')
                 (x : Quotient A R) : B \elim x
  | inR a => f a
  | eq a a' r i => p a a' r @ i
{%endarend%}

**Exercise 9:** Define the set of finite subsets of a set {%ard%}A{%endard%},
 that is of finite lists of elements of {%ard%}A{%endard%} defined up to permutations
 and repetitions of elements.
{: .notice--info}

