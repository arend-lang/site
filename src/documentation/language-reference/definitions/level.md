---
title: Level
---

This module is devoted to a number of tools useful for working with homotopy levels of [universes](../expressions/universes).

## Use level

The homotopy level of a definition is inferred automatically, but sometimes it is possible to prove that it has a smaller level.
For example, we can define the following data types:

{% arend %}
\data Empty
\data Dec (P : \Prop) | yes P | no (P -> Empty)
{% endarend %}

The type of {%ard%} Empty {%endard%} is inferred to {%ard%} \Prop {%endard%}, which is the right universe for the type.
However, this is not as easy for the type {%ard%} Dec P {%endard%}: the type of {%ard%} Dec P {%endard%} is inferred to {%ard%} \Set0 {%endard%},
whereas it can be proven that {%ard%} Dec P {%endard%} is (-1)-type.
{%ard%} Dec {%endard%} can be placed in {%ard%} \Prop {%endard%} by writing the proof, that any two elements of this type are equal, in the {%ard%} \where {%endard%} block of {%ard%} Dec {%endard%}.
The proof must be written in the corresponding function, starting with keywords {%ard%} \use \level {%endard%} instead of {%ard%} \func {%endard%}:

{% arend %}
\data Empty
\data Dec (P : \Prop) | yes P | no (P -> Empty)
  \where
    \use \level isProp {P : \Prop} (d1 d2 : Dec P) : d1 = d2
      | yes x1, yes x2 => path (\lam i => yes (Path.inProp x1 x2 @ i))
      | yes x1, no e2 => \case e2 x1 \with {}
      | no e1, yes x2 => \case e1 x2 \with {}
      | no e1, no e2 => path (\lam i => no (\lam x => (\case e1 x \return e1 x = e2 x \with {}) @ i))
{% endarend %}

Functions {%ard%} \use \level {%endard%} can be specified for {%ard%} \data {%endard%}, {%ard%} \class {%endard%}, and {%ard%} \func {%endard%} definitions.
They must have a particular type.
First parameters of such a function must be parameters of the data type (or the function) or (some) fields of the class.
The rest of parameters together with the result type must prove that the data type (or the function, or the class) has some homotopy level.
That is, it must prove {%ard%} ofHLevel (D p_1 ... p_k) n {%endard%} for some constant {%ard%} n {%endard%},
where {%ard%} D {%endard%} is the data type (or the function, or the class), {%ard%} p_1, ... p_k {%endard%} are its parameters (or fields), and {%ard%} ofHLevel {%endard%} is defined as follows:

{% arend %}
\func \infix 2 ofHLevel_-1+ (A : \Type) (n : Nat) : \Type \elim n
  | 0 => \Pi (a a' : A) -> a = a'
  | suc n => \Pi (a a' : A) -> (a = a') ofHLevel_-1+ n
{% endarend %}

## Level of a type

Sometimes we need to know that some type has a certain homotopy level.
For example, the result type of a [lemma](functions#lemmas) 
or a [property](records#properties) must be a proposition.
If the type does not belong to the corresponding universe, but it can be proved that it has the correct homotopy level,
the keyword {%ard%} \level {%endard%} can be used to convince the typechecker to accept the definition.
This keywords can be specified in the result type of a function, a lemma, a field, or a case expression.
Its first argument is the type and the second is the proof that it belongs to some homotopy level.

For example, if {%ard%} A {%endard%} is a type such that {%ard%} p : \Pi (x y : A) -> x = y {%endard%}, then a lemma that proves {%ard%} A {%endard%} can be defined as follows:

{% arend %}
\lemma lem : \level A p => ...
{% endarend %}

Similarly, a property of type {%ard%} A {%endard%} can be defined as follows:

{% arend %}
\record R {
  \property p : \level A p
}
{% endarend %}

While defining a function or a case expression over a truncated type with values in {%ard%} A {%endard%},
some clauses can be omitted if {%ard%} A {%endard%} belongs to an appropriate universe.
If it is not, but there is a proof that it has the required homotopy level, then the keyword {%ard%} \level {%endard%} can be used to
convince the typechecker that some clauses can be omitted.
For example, if {%ard%} Trunc {%endard%} is a propositional truncation with constructor {%ard%} inT : A -> Trunc A {%endard%}, {%ard%} A {%endard%} and {%ard%} B {%endard%} are types,
{%ard%} g : A -> B {%endard%} is function, and {%ard%} p : \Pi (x y : B) -> x = y {%endard%}, then the function, extending {%ard%} g {%endard%} to {%ard%} Trunc A {%endard%} can be defined simply as follows:

{% arend %}
\func f (t : Trunc A) : \level B p
  | inT a => g a
{% endarend %}

Similarly, the keyword {%ard%} \level {%endard%} can be used in case expressions:

{% arend %}
\func f' (t : Trunc A) => \case t \return \level B p \with {
  | inT a => g a
}
{% endarend %}
