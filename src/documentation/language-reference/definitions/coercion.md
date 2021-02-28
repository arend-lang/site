---
title: Coercion
toc: false
---

Sometimes it is convenient to interpret elements of type {%ard%} A {%endard%} as elements of type {%ard%} B {%endard%} and use
elements of {%ard%} A {%endard%} in places, where elements of {%ard%} B {%endard%} are expected. For example, 
natural numbers are also integer numbers, integer numbers are also rational numbers, and so on. There is a mechanism,
which allows this by marking a function {%ard%} f {%endard%} from {%ard%} A {%endard%} to {%ard%} B {%endard%}  as a _coercing function_. Once {%ard%} f : A -> B {%endard%} is declared
as a coercing function, whenever an expression {%ard%} a : A {%endard%} is used in a place, where type {%ard%} B {%endard%} is expected, {%ard%} a {%endard%} will be
automatically replaced with {%ard%} f a : B {%endard%}. 

A coercing function can be defined either for a {%ard%} \data {%endard%} or a {%ard%} \class {%endard%} definition.
It should be written inside the {%ard%} \where {%endard%} block for this definition and it should begin with {%ard%} \use \coerce {%endard%} instead 
of {%ard%} \func {%endard%}. For example, {%ard%} Bool {%endard%} can be coerced to {%ard%} Nat {%endard%} as follows:

{% arend %}
\data Bool | true | false
  \where
    \use \coerce toNat (b : Bool) : Nat
      | true => 1
      | false => 0
{% endarend %}

It is possible to coerce a given definition either from or to other definition.
A function, which coerces from a given definition, must have this definition as the type of its last parameter.
A function, which coerces to a given definition, must have this definition as its result type.
For example, {%ard%} Nat {%endard%} can be coerced to {%ard%} Bool {%endard%} as follows:

{% arend %}
\data Bool | true | false
  \where
    \use \coerce fromNat (n : Nat) : Bool
      | 0 => false
      | 1 => true
      | suc (suc n) => fromNat n
{% endarend %}

It is possible to define several coercing functions for a single type.

If some data type or record can be coerced to a function, then elements of this type can be applied to arguments, in which case the coercing function will be inserted.

# Fields and constructors

A field or a constructor can be marked with the {%ard%} \coerce {%endard%} keyword like this:

{% arend %}
\record R (\coerce A : \Type) (a : A)
\data D | \coerce con1 Nat | con2
{% endarend %}

Then the marked field or constructor will be used just as coercing functions.
