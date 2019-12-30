---
title: Case, Views, Decidable Predicates
nav: view
---

<!-- TODO: intro -->

# filter via \case and via helper

Case expressions, like in Haskell, can be used for pattern matching on arbitrary expressions. For example,
let us define the function {%ard%}filter{%endard%} that removes from a list {%ard%}xs : List A{%endard%} all
elements that do not satisfy some predicate {%ard%}p : A -> Bool{%endard%}:

{%arend%}
\func filter {A : \Type} (p : A -> Bool) (xs : List A) : List A \elim xs
  | nil => nil
  | cons x xs => \case p x \with {
    | true => cons x (filter p xs)
    | false => filter p xs
  }
{%endarend%}

Here we used case expression for pattern matching on the expression {%ard%}p x{%endard%}. Alternatively,
we could introduce a helper function, defined by pattern matching, and invoke it in the place of
{%ard%}\case{%endard%} usage:

{%arend%}
\func filter' {A : \Type} (p : A -> Bool) (xs : List A) : List A \elim xs
  | nil => nil
  | cons x xs => helper (p x) x (filter p xs)
  \where
    \func helper {A : \Type} (b : Bool) (x : A) (r : List A) : List A \elim b
      | true => cons x r
      | false => r
{%endarend%}

Actually, every usage of case expression can be replaced in this way with an invocation of a helper function. 
It is just sometimes more convenient to use short case expressions instead of introducing countless
amount of helpers.

# Remark on \elim vs \case

A definition of a function by pattern matching can be given either with {%ard%}\elim{%endard%} or with 
{%ard%}\case{%endard%}. These two ways are almost equivalent, but there is one small difference:
depending on whether {%ard%}f{%endard%} is defined via {%ard%}\case{%endard%} or via {%ard%}\elim{%endard%},
the expression {%ard%}f x{%endard%} evaluates to the {%ard%}\case{%endard%} expression or does not evaluate 
respectively. Consider, for example, the following two definitions: 

{%arend%}
\func f (x : Nat) : Nat => \case x \with { zero => 0 | suc n => n }
\func f' (x : Nat) : Nat | zero => 0 | suc n => n
{%endarend%}

{%ard%}f n{%endard%} evaluates to the body of the definition, whereas the expression {%ard%}f' n{%endard%}
is in normal form. The latter option makes normalized terms look nicer and for that reason is usually preferable.

# \case in dependently typed languages

Case expressions are more subtle in dependently typed languages than in languages like Haskell. Let us
assume, for example, we want to prove that {%ard%}p a = not (not (p a)){%endard%} for some predicate
{%ard%}p : A -> Bool{%endard%} and {%ard%}a : A{%endard%}. Of course, this statement can be proved as 
a consequence of a generalized statement {%ard%}x = not (not (x)){%endard%}, and that is the right
way to do it, but we would like to show how it can be proven with {%ard%}\case{%endard%}:

{%arend%}
\func not (b : Bool) : Bool
  | true => false
  | false => true

\func foo {A : \Type} (p : A -> Bool) (a : A) : p a = not (not (p a)) =>
   \case p a \as b \return b = not (not b) \with {
    | true => idp 
    | false => idp
  }
{%endarend%}

Here we specified explicitly the return type of the case expression by writing 
{%ard%}\return b = not (not b){%endard%} before the keyword {%ard%}\with{%endard%}. We do this because
this return type of {%ard%}\case{%endard%} depends on the expression {%ard%}p a{%endard%} that we match
on. In order to describe the dependence, we introduce new bound variable {%ard%}b{%endard%} by
writing {%ard%}\as b{%endard%} just after the expression {%ard%}p a{%endard%}.

In every clause we should return an expression, whose type is the expression obtained from the one written
after {%ard%}\return{%endard%} by substituting the corresponding pattern. In example above we have:

{%arend%}
| true => idp -- here we should return expression of type true = not (not true)
| false => idp -- and here of type false = not (not false)
{%endarend%}

As we said, we could use a helper function:

{%arend%}
\func foo' {A : \Type} (p : A -> Bool) (a : A) : p a = not (not (p a)) =>
  helper (p a)
  \where
    \func helper (b : Bool) : b = not (not b) \elim b
      | true => idp
      | false => idp
{%endarend%}

# \case with several arguments

We can pattern match on several expressions in {%ard%}\case{%endard%}. For example:

{%arend%}
\data Ordering | LT | EQ | GT

\func compare (x y : Nat) : Ordering =>
  \case x < y, y < x \with {
    | true, true => EQ -- this will never be matched
    | true, false => LT
    | false, true => GT
    | false, false => EQ
  }
{%endarend%}

# Proof of a fact about filter via \case

Let us consider one more example of a proof via {%ard%}\case{%endard%}: let us prove
that the length of a filtered list {%ard%}filter xs{%endard%} is at most the 
length of the original list {%ard%}xs{%endard%}:

{%arend%}
\data Empty

\func absurd {A : \Type} (e : Empty) : A

\data Unit | unit

\func \infix 4 <= (x y : Nat) : \Type
  | 0, _ => Unit
  | suc _, 0 => Empty
  | suc x, suc y => x <= y

\func length {A : \Type} (xs : List A) : Nat
  | nil => 0
  | cons _ xs => suc (length xs)

-- auxiliary helper lemma
\func <=-helper {x y : Nat} (p : x <= y) : x <= suc y \elim x, y
  | 0, _ => unit
  | suc x, 0 => absurd p
  | suc x, suc y => <=-helper p

\func filter-lem {A : \Type} (p : A -> Bool) (xs : List A) : length (filter p xs) <= length xs \elim xs
  | nil => unit
  | cons x xs => \case p x \as b \return length (\case b \with { | true => cons x (filter p xs) | false => filter p xs }) <= suc (length xs) \with {
    | true => filter-lem p xs
    | false => <=-helper (filter-lem p xs)
  }
{%endarend%}

# Matching on idp in \case 

When we pattern match on some expression {%ard%}e{%endard%}, the connection of this expression with the 
result of the pattern matching gets lost. For example, we can not even prove in {%ard%}expr{%endard%} inside an expression
of the form {%ard%}\case e \with { | pattern => expr }{%endard%} that {%ard%}e{%endard%} equals {%ard%}pattern{%endard%}.

Sometimes such connections are necessary. In these cases we can use the following trick: double pattern matching
on the original expression {%ard%}e{%endard%} and on {%ard%}idp{%endard%} with explicitly written type depending on
{%ard%}e{%endard%}. Consider an example:

{%arend%}
\func baz {A : \Type} (B : Bool -> \Type) (p : A -> Bool) (a : A) (pt : B true) (pf : B false) : B (p a) =>
    -- Not only the return type can be specified explicitly, but also 
    -- the type of expressions we do matching on.
    -- And we can use variables bounded in \as.
    \case p a \as b, idp : b = p a \with {
      | true, q => transport B q pt -- here q : true = p a
      | false, q => transport B q pf -- here q : false = p a
    }
{%endarend%}

And a helper version again:

{%arend%}
\func baz' {A : \Type} (B : Bool -> \Type) (p : A -> Bool) (a : A) (pt : B true) (pf : B false) : B (p a) => 
    helper B p a pt pf
           (p a) idp
  \where
    \func helper {A : \Type} (B : Bool -> \Type) (p : A -> Bool) (a : A) (pt : B true) (pf : B false)
                (b : Bool) (q : b = p a) : B (p a) \elim b
      | true => transport B q pt -- here q : true = p a
      | false => transport B q pf -- here q : false = p a
{%endarend%}

# One more example of \case

Let us consider one more example, demonstrating what we have just discussed:

{%arend%}
\func bar {A : \Type} (p q : A -> Bool) (a : A) (s : q a = not (p a))
  : not (q a) = p a =>
  \case p a \as x, q a \as y, s : y = not x \return not y = x \with {
    | true, true, s' => inv s'
    | true, false, _ => idp
    | false, true, _ => idp
    | false, false, s' => inv s'
  }

-- helper version
\func bar' {A : \Type} (p q : A -> Bool) (a : A) (s : q a = not (p a))
  : not (q a) = p a => helper (p a) (q a) s
  \where
    \func helper (x y : Bool) (s : y = not x) : not y = x \elim x, y
      | true, true => inv s
      | true, false => idp
      | false, true => idp
      | false, false => inv s
{%endarend%}

# Views

Views -- is a techique that allows to define some kind of custom pattern matching for datatypes.
For example, {%ard%}Nat{%endard%} has constructors {%ard%}zero{%endard%} and {%ard%}suc{%endard%}
and by default we pattern match on them whenever we define a function from {%ard%}Nat{%endard%}.
But we can also define a custom pattern matching for {%ard%}Nat{%endard%} as if {%ard%}Nat{%endard%}
had constructors, say, {%ard%}even{%endard%} and {%ard%}odd{%endard%}.

Let us define a datatype parameterised by the datatype we are defining custom pattern matching for
({%ard%}Nat{%endard%} in our example). The constructors of this datatype will correspond to
the constructors that we want to use for our custom pattern matching ({%ard%}even{%endard%} and 
{%ard%}odd{%endard%} in our example). Each constructor should have a parameter of the form {%ard%}n = expr{%endard%},
where {%ard%}expr{%endard%} represents the custom pattern. In our example we have the following:

{%arend%}
\data Parity (n : Nat)
  | even (k : Nat) (p : n = 2 * k)
  | odd (k : Nat) (p : n = 2 * k + 1)
{%endarend%}

Next, we define a function that converts elements of {%ard%}Nat{%endard%} to elements of {%ard%}Parity{%endard%}:

{%arend%}
\func parity (n : Nat) : Parity n
  | 0 => even 0 idp
  | suc n => \case parity n \with {
    | even k p => odd k (pmap suc p)
    | odd k p => even (suc k) (pmap suc p)
  }
{%endarend%}

Now, in order to pattern match on {%ard%}n : Nat{%endard%} we should invoke {%ard%}\case{%endard%}
on {%ard%}parity n{%endard%}. For example, let us define division by 2:

{%arend%}
\func div2 (n : Nat) : Nat => \case parity n \with {
  | even k _ => k
  | odd k _ => k
  }
{%endarend%}

# Decidable predicates

Here we will discuss predicates in propositions-as-types logic, that is functions {%ard%}P : A -> \Type{%endard%}.
A predicate is called _decidable_ if there is a proof that for all {%ard%}x : A{%endard%} either {%ard%}P x{%endard%}
or not {%ard%}P x{%endard%}. We can write the statement {%ard%}DecPred P{%endard%} saying that {%ard%}P{%endard%}
is decidable as follows:

{%arend%}
\data Decide (A : \Type)
  | yes A
  | no (A -> Empty)

\func DecPred {A : \Type} (P : A -> \Type) => \Pi (a : A) -> Decide (P a)
{%endarend%}

This notion of decidability is related to decidability in computability theory:
if a predicate is decidable in this sense, then there exists an algorithm that for every {%ard%}x : A{%endard%}
decides whether {%ard%}P x{%endard%} or not {%ard%}P x{%endard%}.

In particular, there exist undecidable predicates.
For example, we can define the following predicate {%ard%}P : Nat -> \Type{%endard%}: {%ard%}P n{%endard%} encodes
the statement "Turing machine with number n halts at the input n". A simpler example -- the predicate on pairs of
functions {%ard%}Nat -> Nat{%endard%}, saying that they are equal.

An example of decidable predicate:

{%arend%}
\func suc/=0 {n : Nat} (p : suc n = 0) : Empty => transport (\lam n => \case n \with { | 0 => Empty | suc _ => Unit }) p unit
 
-- the predicate \lam n => n = 0 is decidable
\func decide0 : DecPred (\lam (n : Nat) => n = 0) => \lam n =>
  \case n \as x \return Decide (x = 0) \with {
    | 0 => yes idp
    | suc _ => no suc/=0
  }
{%endarend%}

The above properties of decidability hold as long as our logic is intuitionistic. If we have the Law of Excluded
Middle, then all predicates are decidable, and, in fact, the opposite implication is also true.

# Decidable equality

Let us consider the predicate {%ard%}DecEq A{%endard%}, saying that type {%ard%}A{%endard%} has decidable equality on it: 

{%arend%}
\func DecEq (A : \Type) => \Pi (a a' : A) -> Decide (a = a')
{%endarend%}

We can define a typeclass analogous to Eq in Haskell, but with a proof of decidability of equality instead of a function 
{%ard%}== : A -> A -> Bool{%endard%}. This is better since in Haskell {%ard%}=={%endard%} can be absolutely any function,
not necessarily having anything to do with equality.

{%arend%}
\class Eq (A : \Type) {
  | decideEq : DecEq A
  -- Functions declared inside a class have instance of
  -- the class as their first implicit parameter.
  \func \infix 4 == (a a' : A) : Bool => \case decideEq a a' \with {
    | yes _ => true
    | no _ => false
  }
} \where {
  -- Function == is equivalent to =='.
  \func \infix 4 ==' {e : Eq} (a a' : e.A) : Bool => \case e.decideEq a a' \with {
    | yes _ => true
    | no _ => false
  }
}
{%endarend%}

Let us define an instance for the type of natural numbers:

{%arend%}
\func pred (n : Nat) : Nat
  | 0 => 0
  | suc n => n

\instance NatEq : Eq Nat
  | decideEq => decideEq
  \where
    \func decideEq (x y : Nat) : Decide (x = y)
      | 0, 0 => yes idp
      | 0, suc y => no (\lam p => suc/=0 (inv p))
      | suc x, 0 => no suc/=0
      | suc x, suc y => \case decideEq x y \with {
        | yes p => yes (pmap suc p)
        | no c => no (\lam p => c (pmap pred p))
      }

\func test1 : (0 == 0) = true => idp
\func test2 : (0 == 1) = false => idp
{%endarend%}

# Decidable predicates and functions A -> Bool

Decidable predicates {%ard%}A -> \Type{%endard%} correspond precisely to functions {%ard%}A -> Bool{%endard%}.
Let us define the conversion functions:

{%arend%}
\func FromBoolToDec {A : \Type} (p : A -> Bool) : \Sigma (P : A -> \Type) (DecPred P)
  => (\lam a => T (p a), \lam a => \case p a \as b \return Decide (T b) \with {
    | true => yes tt
    | false => no T-absurd
  })

\func FromDecToBool {A : \Type} (P : \Sigma (P : A -> \Type) (DecPred P)) : A -> Bool
  => \lam a => \case P.2 a \with {
    | yes _ => true
    | no _ => false
  }
{%endarend%}
