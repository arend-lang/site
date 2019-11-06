---
title: Records and Classes
toc: false
nav: records
---

In this module we introduce very useful kinds of definitions: records and classes.

We also discuss the mechanism of coercions.

# Records: \new, \cowith, projections, pattern matching

In the previous modules we saw two ways to arrange a sequence of types {%ard%}A1{%endard%}, ...,
{%ard%}An{%endard%} into a composite type of tuples: Sigma-types 
{%ard%}\Sigma A1 ... An{%endard%} and datatypes {%ard%}\data Tuples | tuple A1 ... An{%endard%}.

For example, a type of pairs of natural numbers can be defined as {%ard%}\Sigma Nat Nat{%endard%}. 
In this case elements of a pair {%ard%}x : \Sigma Nat Nat{%endard%} are accessed by means of projections
{%ard%}x.1{%endard%} and {%ard%}x.2{%endard%}. Or, alternatively, one can realize this type as a datatype
{%ard%}\data NatPair{%endard%} with projections defined by pattern matching:

{%arend%}
\data NatPair | natPair Nat Nat

\func natFst (p : NatPair) : Nat
  | natPair x _ => x

\func natSnd (p : NatPair) : Nat
  | natPair _ y => y
{%endarend%}

The advantage of Sigma-type option is eta-equivalence: if {%ard%}x : \Sigma Nat Nat{%endard%}, then
{%ard%}(x.1, x.2) == x{%endard%}, where {%ard%}=={%endard%} is computational equality. Eta-equivalence
doesn't hold for datatypes: {%ard%}natPair (natFst x) (natSnd x){%endard%} is not computationally equal
to {%ard%}x{%endard%}, one should prove that they are equal and use {%ard%}transport{%endard%} every
time one wants to replace the one with the other. 

Record types provide the third option:

{%arend%}
\record NatPair'
  | fst : Nat
  | snd : Nat
{%endarend%}

The major advantage of records over Sigma-types is that they allow to name components, which are
called _fields_: we can
write {%ard%}x.fst{%endard%} and {%ard%}x.snd{%endard%} instead of {%ard%}x.1{%endard%} and
{%ard%}x.2{%endard%}. And eta-equivalence also applies to elements of records.

Every field of a record is simply a function that has an instance of the record
as its first implicit parameter:

{%arend%}
-- fst : \Pi {x : NatPair'} -> Nat
\func foo (p : NatPair') => fst {p}
{%endarend%}

There is a namespace corresponding to a record, which contains all the fields of the record:

{%arend%}
\func foo' (p : NatPair') => NatPair'.fst {p}
{%endarend%}

The syntax with dot {%ard%}p.snd{%endard%} can only be used to access fields if {%ard%}p{%endard%}
is a variable and its type is specified explicitly:

{%arend%}
\func bar (p : NatPair') => p.snd

-- (f x).snd -- This is not allowed. It can be replaced with one of the following variants:
-- \let e : NatPair' => f x \in e.snd
-- snd {f x}

-- This code will not typecheck since the type of p is not specified explicitly
-- \func baz {p p' : NatPair'} (q : p = p') => pmap (\lam p => p.fst) q
{%endarend%}

An element of a record can be created using the keyword {%ard%}\new{%endard%}:

{%arend%}
\func zeroPair => \new NatPair' {
  | fst => 0
  | snd => 0
  }
{%endarend%}

Eta-equivalence for records, thus, means that 
{%ard%}\new NatPair' { | fst => p.fst | snd => p.snd }{%endard%} is computationally equal to
{%ard%}p{%endard%}:

{%arend%}
\func etaNatPair' (p : NatPair') : p = \new NatPair' { | fst => p.fst | snd => p.snd }
  => idp
{%endarend%}

The pattern matching on variables of record types can be done using the same tuple patterns as
used for pattern matching on variables of Sigma-types:

{%arend%}
\func sum (p : NatPair') => fst {p} + p.snd

\func sum' (p : NatPair') : Nat
  | (a, b) => a + b
{%endarend%}

If we want to define a function that returns an element of a record, we can do this by means of
_copattern matching_ using the keyword {%ard%}\cowith{%endard%}:

{%arend%}
-- This function is equivalent to zeroPair defined above.
-- \cowith is followed with a set of clauses, each starting
-- with | and specifying a field and its value
\func zeroPair' : NatPair' \cowith
  | fst => 0
  | snd => 0
{%endarend%}

# Partial implementation

Given a record, it is possible to form new records out of it via _partial implementation_, that is
by means of assigning values to some of its fields. If {%ard%}C{%endard%} is a record with fields
{%ard%}f1{%endard%}, ..., {%ard%}fn{%endard%}, then {%ard%}C { | f_{i_1} => e_{i_1} ... | f_{i_k} => e_{i_k} }{%endard%}
is a record formed by elements of the record {%ard%}C{%endard%}, where corresponding fields are implemented accordingly.

For example, {%ard%}NatPair' { | fst => 0 }{%endard%} is the type of elements of the record {%ard%}NatPair'{%endard%}, whose
first component is {%ard%}0{%endard%}. This type is, thus, equivalent to the type {%ard%}Nat{%endard%}.
We call such types _anonimous extensions_.

{%arend%}
\func PartialEx : \Type => NatPair' { | fst => 0 }

\func ppp : NatPair' { | fst => 0 } => \new NatPair' { | snd => 1 }
{%endarend%}

Anonimous extensions of a record are subtypes of the record. If {%ard%}p{%endard%} is of type of the form
{%ard%}C { ... }{%endard%}, where the subset F of fields of {%ard%}C{%endard%} is implemented, then {%ard%}p{%endard%} is also
of type of the form {%ard%}C { ... }{%endard%}, where fields from a subset F' of F are implemented and these implementations 
agree with the implementations in the former case. For example:

{%arend%}
\func partial (p : NatPair' { | fst => 0 | snd => 1 }) : PartialEx => p

\func PartialEx' => NatPair' { | fst => 3 | snd => 7 }
{%endarend%}

The operator {%ard%}\new{%endard%} can be applied to any expression that evaluates to a record or its
anonimous extension provided all fields are implemented. For example:

{%arend%}
\func new => \new PartialEx'
{%endarend%}

# Parameters, visibility of fields

Record types can have parameters:

{%arend%}
\record Pair (A B : \Type)
  | fst : A
  | snd : B
{%endarend%}

Elements of such records can be created using {%ard%}\new{%endard%} or {%ard%}\cowith{%endard%} as before:

{%arend%}
\func pairExample : Pair Nat (Nat -> Nat)
  => \new Pair { | fst => 1 | snd (x : Nat) => x }
{%endarend%}

Actually parameters of a record are also its fields. The example above can be equivalently rewritten as follows:
{%arend%}
\func pairExample'
  => \new Pair { | A => Nat | B => Nat -> Nat | fst_ => 1 | snd_ (x : Nat) => x }

\func pairExample''
  => \new Pair Nat (Nat -> Nat) 1 (\lam (x : Nat) => x)
{%endarend%}

There is (almost) no difference between fields and parameters. In particular, it is perfectly fine to
define all fields as parameters. For example, the following is an equivalent version of {%ard%}NatPair{%endard%}:

{%arend%}
\record NatPair'' (fst'' snd'' : Nat)

\func natPair''ex => \new NatPair'' {
  | fst'' => 0
  | snd'' => 0
}

{%endarend%}

And, conversly, the type {%ard%}Pair{%endard%} has equivalent definition without parameters:

{%arend%}
\record Pair'
  | A : \Type
  | B : \Type
  | fst : A
  | snd : B
{%endarend%}

# Dependent records, a type of positive natural numbers

Records can be dependent, that is fields can depend on previous fields. This makes them fully equivalent to
Sigma-types, the only difference is that components of a record are named.

For example, the set of positive natural numbers { n : Nat | T (isPos n) } can be expressed as Sigma-type
{%ard%}\Sigma (n : Nat) (T (isPos n)){%endard%} or as a record:

{%arend%}
\data Bool | true | false

-- compare this definition of T with the one in module Basics
\data T (b : Bool) \with
  | true => tt

\func isPos (n : Nat) : Bool
  | 0 => false
  | suc _ => true

\record PosNat (n : Nat) (p : T (isPos n))
{%endarend%}

# Monoid

Another example of dependent records -- the type of monoids. We define this type as a _class_ using keyword
{%ard%}\class{%endard%} instead of {%ard%}\record{%endard%}. Classes are very similar to records and almost
equivalent to them. But there are some nice features that classes have and records don't. We will discuss
classes in more detail below.

{%arend%} 
\class Monoid (A : \Type)
  | id : A
  | \infixl 6 * : A -> A -> A
  | *-assoc (x y z : A) : (x * y) * z = x * (y * z)
  -- | *-assoc : \Pi (x y z : A) -> (x * y) * z = x * (y * z)
  | id-left (x : A) : id * x = x
  | id-right (x : A) : x * id = x

\func baz (m : Monoid Nat 0 (Nat.+)) => m.*-assoc
{%endarend%}

Classes and records can extend other records and classes. Some fields can be implemented in these extensions,
this is useful when all instances of the extension are supposed to implement the field in the same way:

{%arend%}
\class CommMonoid \extends Monoid
  | *-comm (x y : A) : x * y = y * x
  | id-right x => *-comm x id *> id-left x 
-- id-right follows from id-left for commutative monoids
{%endarend%}

We will discuss extensions in more detail below.

# Classes, instances

The only difference between classes and records is that for classes an instance inferrence procedure is implemented.
This procedure is analogous to the one in Haskell.

Global instances of a class can be defined using keyword {%ard%}\instance{%endard%}. For example, there are two 
natural instances of the class {%ard%}Monoid{%endard%} for natural numbers: monoid on {%ard%}+{%endard%} and
monoid on {%ard%}*{%endard%}.

{%arend%}
\instance +-NatMonoid : Monoid Nat
  | id => 0
  | * => Nat.+
  | *-assoc => {?}
  | id-left => {?}
  | id-right => {?}

\instance *-NatMonoid : Monoid Nat
  | id => 1
  | * => Nat.*
  | *-assoc => {?}
  | id-left => {?}
  | id-right => {?}

-- alternative definition of the latter:
\instance *-NatMonoid' : Monoid Nat 1 (Nat.*) {?} {?} {?}
{%endarend%}

The first explicit pararameter of a class is of special significance and is called _classifying field_ of a class.
It plays an important role in instance inference algorithm. Basically, in case there are no local instances, the algorithm
searchs for a first appropriate global instance, appropriate in the sense that its classifying field coincides with
some expected type. 

Note, that the type of a class field is determined in the same way as in case of records. For example, for {%ard%}*{%endard%}:

{%arend%}
* {M : Monoid} (x y : M.A) : M.A
{%endarend%}

Consider the following examples:
 
{%arend%}
-- ok, +-NatMonoid is inferred since it was declared the first
-- id-left x here is equivalent to id-left {+-NatMonoid} x
\func +-test (x : Nat) : 0 Nat.+ x = x => id-left x
-- error, because +-NatMonoid is inferred, not *-NatMoniod
\func *-test (x : Nat) : 1 Nat.* x = x => id-left x
{%endarend%}

Such global instances behave like ordinary functions defined by copattern matching:

{%arend%}
\func instEx => +-NatMonoid.id-left

\func instExF (M : Monoid) => M.id

\func instEx' => instExF +-NatMonoid
{%endarend%}

Arend classes can be used as typeclasses in Haskell. For example, {%ard%}Eq{%endard%} can be written as follows:
{%arend%}
\class Eq (A : \Type)
  | \infix 3 == (x y : A) : Bool

-- function refl from Haskell can be defined in two ways
-- refl :: Eq a => a -> Bool
-- refl x = x == x
\func refl {A : \Type} {e : Eq A} (a : A) => a == a

\func refl' {E : Eq} (a : E) => a == a

-- \func xxxx => refl 1
{%endarend%}

# Coercions

Classifying field of a class has a number of nice properties. For example, if in some place an element of type 
{%ard%}X{%endard%} is expected and {%ard%}X{%endard%} is the type of the classifying field of a class {%ard%}C{%endard%},
then any object of type {%ard%}C{%endard%} can be used in this place. The classifying field will be inserted automatically.

In the following example {%ard%}M.A{%endard%} will be inserted instead of {%ard%}M{%endard%} in {%ard%}(x : M){%endard%} since
an element of type {%ard%}\Type{%endard%} is expected:

{%arend%}
\func CF-coerce (M : Monoid) (x : M) => x
{%endarend%}

This kind of substitutions are called _coercions_, we say that a class can be coerced to its classifying field. The mechanism
of coercions in Arend allows also to define coercions between datatypes, classes and records. In order to be able to use
elements of type {%ard%}A{%endard%}, where elements of type {%ard%}B{%endard%} are expected, one should define a function
{%ard%}f : A -> B{%endard%} in the {%ard%}\where{%endard%}-block of either {%ard%}A{%endard%} or {%ard%}B{%endard%} as a coercion
by using keywords {%ard%}\use \coerce{%endard%}. Elements {%ard%}a{%endard%} of type {%ard%}A{%endard%} will then be replaced
with {%ard%}f a{%endard%} if they are used in a context, where {%ard%}B{%endard%} expected.

Consider the following example:

{%arend%}
\data XXX | con

\data YYY | con' XXX Nat | con''
  \where {
    -- We can define coercions TO this type.
    -- The return type of the function must be YYY.
    \use \coerce fromXXX (x : XXX) => con' x 0
    
    -- We can also define coercions FROM this type.
    -- The type of the last parameter of the function must 
    -- be YYY.
    \use \coerce toXXX (y : YYY) => con
  }

\func fff (y : YYY) => y

-- Elements of type XXX are implicitly converted to type YYY by function fromXXX.
\func ggg => fff con

-- Implicit convertion from Nat to Int is done in this way:
\func hhh : Int => 0
{%endarend%}

# Class and record extensions, diamond problem

Records and classes can extend other classes. The list of records and classes extended by a given class can be specifyed 
after the keyword {%ard%}\extends{%endard%} as shown in the following example:

{%arend%}
\record Base (A : \Type)

\record Base' (A : \Type)

\record X \extends Base
  | a : A

\record Y \extends Base'
  | b : A

\record Z \extends X, Y

\func zzz => \new Z {
  | A => {?}
  | a => {?}
  | Base'.A => {?}
  | b => {?}
  }

\func zzzz (z : Z) => Base'.A {z}
{%endarend%}

This means that the set of fields of a given class (or record) contain all fields declared in the class plus all the 
fields from the classes and records that it extends.

The record {%ard%}Z{%endard%} in the example above has four fields: {%ard%}Base.A{%endard%}, {%ard%}Base'.A{%endard%},
{%ard%}a{%endard%} and {%ard%}b{%endard%}. But if {%ard%}X{%endard%} and {%ard%}Y{%endard%} both extended the same
record, say, {%ard%}Base{%endard%}, then {%ard%}Z{%endard%} would have had three fields:

{%arend%}
\record X' \extends Base
  | aa : A

\record Y' \extends Base
  | bb : A

-- Z' has three fields: aa, bb, A
\record Z' \extends X', Y'
{%endarend%}

Consider an example from algebra: the type of rings. One can define this type as follows:

{%arend%}
-- let's introduce the type of abelian monoids
\class AbGroup \extends CommMonoid {
  | inverse : A -> A
  | inv-left (x : A) : inverse x * x = id
  | inv-right (x : A) : x * inverse x = id
}

-- we omit distributivity
\class Ring \extends AbGroup
  | mulMonoid : Monoid A
{%endarend%}

In order to distinguish the structure of addition from the structure of multiplication we do not extend {%ard%}Monoid{%endard%},
but add it as a field instead. Note that we specify explicitly the underlying classifying field of {%ard%}mulMonoid{%endard%} to make
it the same as the one in the abelian group of addition.


TODO: finish this
If we try to define the type of rings that extends abelian group of addition and monoid of multiplication,
we will fail. 

-- Определим еще один тип абелевых групп, который не наследует моноиды.
\class AbGroup' (A : \Type) {
  -- Здесь нужно перечислить все поля из Monoid, CommMonoid и AbGroup.
}

-- Если мы попытаеся определить тип колец следующим образом, то у нас ничего не получится, так как структуры сложения и умножения будут совпадать.
\class Ring' \extends AbGroup', Monoid
  | Monoid.A => AbGroup'.A

# Functor

We conclude by demontrating another important example: the class of functors.

{%arend%}
\class Functor (F : \Type -> \Type)
  | fmap {A B : \Type} (f : A -> B) : F A -> F B
  | fmap-id {A : \Type} (y : F A) : fmap (\lam (x : A) => x) y = y
  | fmap-comp {A B C : \Type} (f : A -> B) (g : B -> C) (y : F A)
    : fmap (\lam x => g (f x)) y = fmap g (fmap f y)
{%endarend%}
