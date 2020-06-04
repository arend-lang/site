---
title: Propositions and Proofs
nav: syn-n-def
---

The source code for this module: [PartI/Proofs.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/Proofs.ard) \\
The source code for the exercises: [PartI/ProofsEx.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/Exercises/ProofsEx.ard)
{: .notice--success}

In this module we explain how to formulate and prove propositions in Arend.
We show how to express various logical connectives and demonstrate that they satisfy the required properties.

# Curry-Howard correspondence

Arend is based on a variant of Martin-Löf's type theory.
Such theories do not have a separate logical language to express propositions and their proofs.
Instead, they use the Curry-Howard correspondence to encode propositions as types.
The false proposition corresponds to the empty type and the true proposition corresponds to the unit type.
Different elements of a type can be thought of as different ways to prove corresponding proposition.
For example, the type of natural numbers corresponds to the proposition that natural numbers exist and every element of this type witnesses a proof of this proposition.

**Remark:** This correspondence will be refined in [Part II](/documentation/tutorial/PartII) of this tutorial, where we will argue that not every type should be though of as a proposition.
{: .notice--warning}

In order to illustrate the correspondence between the empty type {%ard%}Empty{%endard%} and the logical False, we can prove
that False implies everything by constructing an element of any type from an element in {%ard%}Empty{%endard%}:

{%arend%}
\func absurd {A : \Type} (e : Empty) : A
-- There are no patterns since Empty does not have constructors.

-- This can be expressed more explicitly by means of the absurd patterns.
-- This pattern indicates that the data type of the corresponding variable does not have constructors.
-- If such a pattern is used, the right hand side of the clause can (and should) be omitted.
\func absurd' {A : \Type} (e : Empty) : A \elim e
  | () -- absurd pattern
{%endarend%}

Of course, we can also prove that {%ard%} Unit {%endard%} corresponds to the logical True simply by constructing an element of this type:

{%arend%}
\func Unit-isTrue : Unit => unit
{%endarend%}

To formulate more complicated propositions, we need to define various logical connectives such as conjunction {%ard%} && {%endard%}, disjunction {%ard%} || {%endard%}, implication {%ard%} -> {%endard%}, and negation {%ard%} Not {%endard%}.
Let us begin with the implication.
If {%ard%} P -> Q {%endard%} is true, then the truth of {%ard%} P {%endard%} implies the truth of {%ard%} Q {%endard%}.
Thus, we can think of a proof of {%ard%} P -> Q {%endard%} as a function that transforms a proof of {%ard%} P {%endard%} into a proof of {%ard%} Q {%endard%}.
That is, the type corresponding to the implications is the type of functions {%ard%} P -> Q {%endard%}!

We already can prove various propositional tautologies.
For example, the identity function proves that {%ard%} P -> P {%endard%} holds for every proposition {%ard%} P {%endard%}.
The constant function {%ard%} \lam x y => x {%endard%} proves {%ard%} P -> Q -> P {%endard%}.
The composition function {%ard%} \lam g f x => g (f x) {%endard%} proves {%ard%} (Q -> S) -> (P -> Q) -> P -> S {%endard%}.

**Exercise 1:** Prove that {%ard%} (P -> Q -> R) -> (P -> Q) -> P -> R {%endard%}.
{: .notice--info}

**Exercise 2:** Prove that {%ard%} ((P -> Q -> R) -> P) -> (P -> R) -> R {%endard%}.
{: .notice--info}

Since {%ard%} P && Q {%endard%} is true if and only if {%ard%} P {%endard%} and {%ard%} Q {%endard%} are true,
we can say that a proof of {%ard%} P && Q {%endard%} is just a pair consisting of a proof of {%ard%} P {%endard%} and a proof of {%ard%} Q {%endard%}.
That is, the type corresponding to {%ard%} P && Q {%endard%} is simply the type of pairs:

{%arend%}
\func \infixr 3 && (P Q : \Type) => \Sigma P Q
{%endarend%}

It is easy to prove conjunction axioms:

{%arend%}
-- This function proves that P -> Q -> (P && Q)
\func &&-intro {P Q : \Type} (p : P) (q : Q) : \Sigma P Q => (p, q)

-- This function proves that (P && Q) -> P
\func &&-elim1 {P Q : \Type} (t : \Sigma P Q) : P => t.1

-- This function proves that (P && Q) -> Q
\func &&-elim2 {P Q : \Type} (t : \Sigma P Q) : Q => t.2
{%endarend%}

**Exercise 3:** Prove that {%ard%} ((P && Q) -> R) -> P -> Q -> R {%endard%}.
{: .notice--info}

**Exercise 4:** Prove that {%ard%} (P -> Q -> R) -> (P && Q) -> R {%endard%}.
{: .notice--info}

A proof of {%ard%} P || Q {%endard%} is either a proof of {%ard%} P {%endard%} or a proof of {%ard%} Q {%endard%}.
The type corresponding to this principle is the sum type:

{%arend%}
\data \infixr 2 || (P Q : \Type)
  | inl P
  | inr Q
{%endarend%}

It is easy to prove disjunction axioms:

{%arend%}
-- This function proves that P -> (P || Q)
\func ||-intro1 {P Q : \Type} (p : P) : P || Q => inl p

-- This function proves that Q -> (P || Q)
\func ||-intro2 {P Q : \Type} (q : Q) : P || Q => inr q

-- This function proves that (P -> R) -> (Q -> R) -> (P || Q) -> R
\func ||-elim {P Q R : \Type} (l : P -> R) (r : Q -> R) (x : P || Q) : R \elim x
  | inl p => l p
  | inr q => r q
{%endarend%}

**Exercise 5:** Prove that {%ard%} (P -> R) -> (Q -> R) -> P || Q -> R {%endard%}.
{: .notice--info}

**Exercise 6:** Prove that {%ard%} ((P || Q) -> (P && Q)) -> ((P -> Q) && (Q -> P)) {%endard%}.
{: .notice--info}

The negation {%ard%} Not P {%endard%} can be defined in terms of the implication as {%ard%} P -> Empty {%endard%}.

**Remark:** The logic of Arend is intuitionistic. This means that the law of excluded middle, the double negation elimination, and other classically valid principles are not provable in Arend.
In particular, it is not true that the conjunction {%ard%} P && Q {%endard%} can be expressed as {%ard%} Not (Not P || Not Q) {%endard%}.
Similarly, the disjunction {%ard%} P || Q {%endard%} cannot be expressed as {%ard%} Not (Not P && Not Q) {%endard%} and the implication {%ard%} P -> Q {%endard%} cannot be expressed as {%ard%} Not P || Q {%endard%}.
{: .notice--warning}

**Exercise 7:** Russell's paradox shows that there is no set of all sets. If such a set exists, then we can form the set `B` of sets which are not members of themselves.
Then `B` belongs to itself if and only if it is not.
This implies a contradiction.
Cantor's theorem states that there is no set `X` with a surjection from `X` onto the set of subsets of `X`.
Its proof also constructs a proposition which is true if and only if it is false.
Prove that more generally the existence of any such proposition implies a contradiction.
{: .notice--info}

Finally, let us discuss quantifiers.
A proof of {%ard%} forall (x : A). P(x) {%endard%} should give us a proof of {%ard%} P(a) {%endard%} for every element {%ard%} a : A {%endard%}.
Thus, this proposition corresponds to the type of dependent functions {%ard%} \Pi (x : A) -> P x {%endard%}.
A proof of {%ard%} exists (x : A). P(x) {%endard%} consists of an element {%ard%} a : A {%endard%} and a proof of {%ard%} P(a) {%endard%}.
Thus, this proposition corresponds to the type of dependent pairs {%ard%} \Sigma (x : A) (P x) {%endard%}.

**Exercise 8:** Prove that if, for every {%ard%} x : Nat {%endard%}, {%ard%} P x {%endard%} is true, then there exists {%ard%} x : Nat {%endard%} such that {%ard%} P x {%endard%} is true.
{: .notice--info}

**Exercise 9:** Prove that if there is no {%ard%} x : Nat {%endard%} such that {%ard%} P x {%endard%} holds, then {%ard%} P 3 {%endard%} is false.
{: .notice--info}

**Exercise 10:** Prove that if, for every {%ard%} x : Nat {%endard%}, {%ard%} P x {%endard%} implies {%ard%} Q x {%endard%},
then the existence of an element {%ard%} x : Nat {%endard%} for which {%ard%} P x {%endard%} is true implies the existence of an element {%ard%} x : Nat {%endard%} for which {%ard%} Q x {%endard%} is true.
{: .notice--info}

**Exercise 11:** Prove that if, for every {%ard%} x : Nat {%endard%}, either {%ard%} P x {%endard%} is false or {%ard%} Q x {%endard%} is false, then {%ard%} P 3 {%endard%} implies that {%ard%} Q 3 {%endard%} is false.
{: .notice--info}

# Examples of propositions and proofs

Here we will give several simple examples of propositions and proofs, using what we have discussed so far. 
To express various propositions, we will use the function {%ard%}T{%endard%} that interprets {%ard%}true : Bool{%endard%}
as the proposition True (type {%ard%}Unit{%endard%}) and {%ard%}false : Bool{%endard%} as the proposition False (type {%ard%}Empty{%endard%}):

{%arend%}
\func T (b : Bool) : \Type
  | true => Unit
  | false => Empty
{%endarend%}

Now let us prove some statements about the two-element type {%ard%}Bool{%endard%} defined earlier.
We formulate some properties of {%ard%}Bool{%endard%}, expressable in terms of equality predicate for {%ard%}Bool{%endard%}:

{%arend%}
\func \infix 4 == (x y : Bool) : Bool
  | true, true => true
  | false, false => true
  | _ , _ => false
{%endarend%}

For example, propositions {%ard%}T (x == x){%endard%} and {%ard%}T (not (not x) == x){%endard%} can be proven by case analysis: 

{%arend%}
\func not-isInvolution (x : Bool) : T (not (not x) == x)
  | true => unit -- if x is true, then T (not (not true) == true) evaluates to Unit
  | false => unit -- if x is false, then T (not (not false) == false) again evaluates to Unit

-- proof of reflexivity of == is analogous 
\func ==-refl (x : Bool) : T (x == x)
  | true => unit
  | false => unit
{%endarend%}

In both cases in both proofs we simply return {%ard%}unit{%endard%}. Note that we cannot return {%ard%}unit{%endard%} without case analysis since
both {%ard%}T (not (not x) == x){%endard%} and {%ard%}T (x == x){%endard%} do not evalute to {%ard%}Unit{%endard%}. The following code does not typecheck:

{%arend%}
\func not-isInvolution' (x : Bool) : T (not (not x) == x) => unit
{%endarend%}

It is not possible to prove false statements in this way:

{%arend%}
\func not-isIdempotent (x : Bool) : T (not (not x) == not x)
  | true => {?} -- goal expression, an element of Empty is expected
  | false => {?} -- goal expression, an element of Empty is expected

-- we can prove negation of not-isIdempoten
\func not-isIdempotent' (x : Bool) : T (not (not x) == not x) -> Empty
  | true => \lam x => x -- a proof of Empty -> Empty
  | false => \lam x => x -- again a proof of Empty -> Empty
{%endarend%}

Let us also prove something involving quantification. For example, the statement 
"for every {%ard%}x : Bool{%endard%} there exists {%ard%}y : Bool{%endard%} such that x == y":
{%arend%}
-- Sigma-types are used to express existential quantification
\func lemma (x : Bool) : \Sigma (y : Bool) (T (x == y)) => (x, ==-refl x)
{%endarend%}

The following is a proof of rather awkward statement "if every {%ard%}x : Bool{%endard%} equals itself, then {%ard%}true : Bool{%endard%}
equals {%ard%}true : Bool{%endard%}":

{%arend%}
\func higherOrderFunc (f : \Pi (x : Bool) -> T (x == x)) : T (true == true) => f true
{%endarend%}

# Identity type

The way how we defined equality {%ard%}=={%endard%} for {%ard%}Bool{%endard%} above is not actually satisfactory. Its definition
is specific for {%ard%}Bool{%endard%}, we need to make analogous definitions for all other types and each time prove, say, that it is
an equivalence relation. 

Instead, we define an identity type for all types at once. Its definition is located in Prelude (type {%ard%}Path{%endard%} and its
infix form {%ard%}={%endard%}). We will not get into details for now, all that we currently need is the proof of reflexivity {%ard%}idp : a = a{%endard%}, which is also defined in Prelude.

Now, all the equalities that we proved for {%ard%}=={%endard%} can similarly be proved for {%ard%}={%endard%}. For example, 
the equality {%ard%}not (not x) = x{%endard%}:

{%arend%}
\func not-isInvolution'' (x : Bool) : not (not x) = x
  | true => idp
  | false => idp
{%endarend%}

And as before, we cannot prove false statements:

{%arend%}
\func not-isIdempotent'' (x : Bool) : not (not x) = not x
  | true => {?} -- goal expression, non-existing proof of true = false is expected
  | false => {?} -- goal expression, non-existing proof of false = true is expected
{%endarend%}

**Exercise 12:** Prove associativity of `and` and `or`.
{: .notice--info}

**Exercise 13:** Prove that 2 * 2 equals to 4.
{: .notice--info}

**Exercise 14:** Prove associativity of the list concatenation.
{: .notice--info}
