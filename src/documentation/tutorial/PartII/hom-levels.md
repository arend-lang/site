---
title: Homotopy levels
nav: hom-levels
---

# The universe \Prop

The universe {%ard%}\Prop{%endard%} consists of all propositions, that is of all types 
{%ard%}A : \Type{%endard%} satisfying the predicate {%ard%}isProp{%endard%}:

{%arend%}
\func isProp (A : \Type) => \Pi (x y : A) -> x = y
{%endarend%}

This means that there exist functions in both directions between {%ard%}\Prop{%endard%} and the 
subuniverse {%ard%}\Sigma (A : \Type) (isProp A){%endard%} of {%ard%}\Type{%endard%}, consisting of
all propositions in {%ard%}\Type{%endard%}. We denote the latter universe as {%ard%}PropInType{%endard%}.

By definition {%ard%}\Prop{%endard%} embeds into {%ard%}PropInType{%endard%}. Firstly,
{%ard%}\Prop{%endard%} is a subuniverse of {%ard%}\Type{%endard%}, that is 
{%ard%}P : \Prop{%endard%} implies {%ard%}P : \Type{%endard%}. Secondly, every {%ard%}P : \Prop{%endard%}
is a proposition by an axiom {%ard%}Path.inProp P{%endard%} located in Prelude.

The construction of a function in the opposite direction from {%ard%}PropInType{%endard%} to
{%ard%}\Prop{%endard%} is also simple, but requires an additional language construct 
{%ard%}\use \level{%endard%}. 

The {%ard%}\use \level{%endard%} construct allows to place a data definition {%ard%}D A_1 ... A_n{%endard%}
in the universe {%ard%}\Prop{%endard%} as long as there is a proof of 
{%ard%}\Pi (a_1 : A_1) ... (a_n : A_n) -> isProp (D a_1 ... a_n){%endard%}. In order to do that one 
should write a function with corresponding result type in the \where-block of {%ard%}D{%endard%} and
with {%ard%}\use \level{%endard%} keywords instead of {%ard%}\func{%endard%}.  

<!--
We will discuss this construct in full generality a bit later, here
we use it as a means to place a data definition {%ard%}D A_1 ... A_n{%endard%} in the universe {%ard%}\Prop{%endard%}
as long as there is a proof of {%ard%}\Pi (a_1 : A_1) ... (a_n : A_n) -> isProp (D a_1 ... a_n){%endard%}:
-->

{%arend%}
\data PropInType-to-Prop (A : \Type) (p : isProp A)
  | inc A
  \where {
    -- Here we prove that 'PropInType-to-Prop' satisfies 'isProp'.
    -- This results in 'PropInType-to-Prop A p : \Prop' for all 'A' and 'p'.
    -- Without '\use \level' 'PropInType-to-Prop A p' would not be in '\Prop'
    --   unless 'A' is in '\Prop'.
    \use \level dataIsProp {A : \Type} {p : isProp A} 
                     (d1 d2 : PropInType-to-Prop A p) : d1 = d2 \elim d1, d2
      | inc a1, inc a2 => pmap inc (p a1 a2)
  }
{%endarend%}

As we will discuss below, there are universes {%ard%}\Set{%endard%} of all sets and, in general,
{%ard%}\n-Type{%endard%} of all types of homotopy level n. The {%ard%}\use \level{%endard%} construct
can be used similarly in these cases, see <!-- TODO:ref --> for details.

The embedding of {%ard%}\Prop{%endard%} into {%ard%}PropInType{%endard%} is inverse to the map
{%ard%}PropInType-to-Prop{%endard%}, but we have not yet introduced all the tools necessary to prove that.
<!--TODO:ref-->

# The universe \Set

Recall that in the previous module we noted that the equality {%ard%}x=y{%endard%} is not always a proposition
and defined sets as those types {%ard%}A{%endard%}, for which equality {%ard%}a=a'{%endard%} between any two 
elements {%ard%}a a' : A{%endard%} is a propoposition:

{%arend%}
\func isSet (A : \Type) => \Pi (x y : A) -> isProp (x = y)
{%endarend%}

There is a universe {%ard%}\Set{%endard%} of all sets. Just as the universe {%ard%}\Type{%endard%} is not
a single universe, but a hierarchy of universes {%ard%}\Type n{%endard%} parameterized by the predicative
level {%ard%}n{%endard%}, {%ard%}\Set{%endard%} is also a predicative hierarchy {%ard%}\Set n{%endard%}.

The universe {%ard%}\Set n{%endard%} is equivalent to the subuniverse {%ard%}\Sigma (A : \Type n) (isSet A){%endard%}
of {%ard%}\Type n{%endard%}. Denote {%ard%}\Sigma (A : \Type) (isSet A){%endard%} as {%ard%}SetInType{%endard%}. 

Let us construct a function from {%ard%}\Set{%endard%} to {%ard%}SetInType{%endard%}. Such a construction relies on 
the following property of the universe {%ard%}\Set{%endard%}: for every set {%ard%}A{%endard%}
in {%ard%}\Set{%endard%} its equality type lies in the universe {%ard%}\Prop{%endard%}. We can thus 
use {%ard%}Path.inProp{%endard%} to prove {%ard%}isSet A{%endard%} for sets in {%ard%}\Set{%endard%}:

{%arend%}
\func Set-to-SetInType (A : \Set \lp) : \Sigma (A : \Type \lp) (isSet A) =>
       (A, \lam x y => Path.inProp (x = y))
{%endarend%}

The inverse function can be constructed with the use of {%ard%}\use \level{%endard%} in the similar way as the function
{%ard%}PropInType-to-Prop{%endard%}.

 
# Universes \n-Type

Universes {%ard%}\Prop{%endard%} and {%ard%}\Set{%endard%} are particular instances of universes of all types of 
a given homotopy level. In general, we have a hierarchy {%ard%}\n-Type{%endard%} of universes parameterized by
homotopy level n. The homotopy level can be specified as the second argument to {%ard%}\Type{%endard%} (after 
predicative level) or before {%ard%}Type{%endard%}:

{%arend%}
\func bak => \Type 30 66
\func bak' => \66-Type 30
-- With predicative level omitted.
\func bak'' => \66-Type
{%endarend%}

There are two equivalent ways to refer to the universe of sets: as {%ard%}\Set{%endard%} or as {%ard%}\0-Type{%endard%}. 
For every predicative level n the universe {%ard%}\Set n{%endard%} is the same as {%ard%}\0-Type n{%endard%}.
The universe of propositions, however, can only be referred to as {%ard%}\Prop{%endard%}, it is not allowed to write
{%ard%}\\(-1)-Type{%endard%}. The universe {%ard%}\Prop{%endard%} is slightly aside since it is impredicative, that is
it does not have predicative level.

The universes form a hierarchy according to the following rule: {%ard%}A : \Type n m{%endard%} implies 
{%ard%}A : \Type (n+1) (m+1){%endard%}. In particular, {%ard%}A : \Prop{%endard%} implies {%ard%}A : \Type n m{%endard%}.

Recall the definition of {%ard%}hasLevel{%endard%} from the previous module:

{%arend%}
-- The predicate saying "A has level suc-l - 1"
\func hasLevel (A : \Type) (suc-l : Nat) : \Type \elim suc-l
  | 0 => isProp A
  | suc suc-l => \Pi (x y : A) -> (x = y) `hasLevel` suc-l
{%endarend%}

For any natural number n>0, the equivalence between {%ard%}\\(n-1)-Type{%endard%} and the subuniverse 
{%ard%}\Sigma (A : \Type) (A `hasLevel` n){%endard%} can be constructed in the same way as for
{%ard%}\Set{%endard%}.

The computation of homotopy levels of types is in many respects similar to the computation of predicative
levels. There are two important distinctions of homotopy levels. Firstly, the level of {%ard%}\Pi{%endard%} is equal
to the level of its codomain: if {%ard%}A : \Type n m{%endard%} and {%ard%}B : A -> \Type n' m'{%endard%}, then 
{%ard%}(\Pi (x : A) -> B x) : \Type (\max n n') m'{%endard%}. Secondly, if {%ard%}A : \\(n+1)-Type{%endard%},
then {%ard%}a=a' : \n-Type{%endard%} for all {%ard%}a a' : A{%endard%}.

# Truncated data, propositional truncation

As we have seen, by means of {%ard%}\use \level{%endard%} a data definition {%ard%}D{%endard%} can be placed in the universe of
homotopy level n in case {%ard%}D{%endard%} can be proven to be of homotopy level n. A data definition can be also _enforced_
to be in the universe of a given homotopy level by using the keyword {%ard%}\truncated{%endard%}. In that case the universe
of the data definition must, of course, be specified explicitly. For example, the projection of types to propositions, which is called
_propositional truncation_, is a truncated data:

{%arend%}
-- Proposition 'Trunc A' says "A is nonempty".
\truncated \data Trunc (A : \Type) : \Prop
  | trunc A

-- Example: 'Trunc Nat'.
\func truncNat : trunc 0 = trunc 1 => Path.inProp (trunc 0) (trunc 1)

-- We can prove the negation of "Empty is nonempty".
\func Trunc-Empty (t : Trunc Empty) : Empty \elim t
  | trunc a => a
{%endarend%}

Truncating a data has one crucial consequence: any function defined by recursion over a truncated data must have the 
codomain lying in the universe of the data. For example, the following function does not typecheck:

{%arend%}
-- This does not typecheck!
\func ex1 (t : Trunc Nat) : Nat
  | trunc n => n

-- But we can define 'ex2' since 0 = 0 is in \Prop.
\func ex2 (t : Trunc Nat) : 0 = 0
  | trunc n => idp
{%endarend%}

Elimination principle for {%ard%}Trunc A{%endard%} is restricted to propositions. It says that if {%ard%}B{%endard%}
is a proposition and there is a function {%ard%}A -> B{%endard%}, then {%ard%}Trunc A{%endard%} implies {%ard%}B{%endard%}:

{%arend%}
\func Trunc-elim {A : \Type} {B : \Prop} (f : A -> B) (a : Trunc A) : B \elim a
  | trunc a => f a
-- The eliminator computes on constructor:
-- Trunc-elim f (trunc a) ===> f a
{%endarend%}

Note that we can alternatively define the propositional truncation as a function reflecting this elimination
principle. Recall, that in this way we can define, say, Church-style natural numbers:

{%arend%}
\func Nat-church => \Pi (X : \Type) -> (X -> X) -> X -> X

\func zero-church : Nat-church => \lam X f x => x
\func one-church : Nat-church => \lam X f x => f x
-- ...
{%endarend%}

In case of the propositional translation we have the following:

{%arend%}
\func Trunc' (A : \Type) : \Prop => \Pi (X : \Prop) -> (A -> X) -> X

\func trunc' {A : \Type} (a : A) : Trunc' A => \lam X f => f a

\func Trunc'-elim {A : \Type} {B : \Prop} (f : A -> B) (a : Trunc' A) : B
  => a B f
{%endarend%}

In some simple cases there is no need to truncate the data or to use {%ard%}\use \level{%endard%} since
the data is placed in the universe automatically. For example, a data is placed in {%ard%}\Prop{%endard%}
if it has at most one constructor and types of all the parameters of the constructor are in {%ard%}\Prop{%endard%}:

{%arend%}
\data T (b : Bool) \with
   | true => tt

\func T-test (b : Bool) : \Prop => T b
{%endarend%}

For functions defined by pattern matching the minimal appropriate universe is inferred:

{%arend%}
\func T' (b : Bool) : \Type
  | true => \Sigma
  | false => Empty

\func T'-test (b : Bool) : \Prop => T' b
{%endarend%}

# Propositions ∨ and ∃

We are now ready to define propositional operations "or" and "exists", which were left undefined in the 
previous module. Types {%ard%}Either{%endard%} and {%ard%}\Sigma{%endard%}, the Curry-Howard "or" and "exists"
respectively, are not propositions even if they are applied to propositions, but we can fix it by applying propositional
truncation. "or" can be equivalently defined either as a truncation of {%ard%}Either{%endard%} or as a 
{%ard%}\truncated \data{%endard%}:

{%arend%}
\data Either (A B : \Type) | inl A | inr B

\truncated \data \fixr 2 Or (A B : \Type) : \Prop
  | inl A
  | inr B

\func \fixr 2 Or' (A B : \Type) : \Prop => Trunc (Either A B)
{%endarend%}

It is easy to see that {%ard%}Or{%endard%} satisfies the required properties: {%ard%}A -> A `Or` B{%endard%}
(constructor {%ard%}inl{%endard%}), {%ard%}B -> A `Or` B{%endard%} (constructor {%ard%}inr{%endard%}) and
for any proposition {%ard%}C{%endard%} and all types {%ard%}A{%endard%}, {%ard%}B{%endard%} if 
{%ard%}A -> C{%endard%} and {%ard%}B -> C{%endard%}, then {%ard%}A `Or` B -> C{%endard%}. The latter is
the recursor for {%ard%}Or{%endard%}:

{%arend%}
\func Or-rec {A B C : \Prop} (f : A -> C) (g : B -> C) (p : A `Or` B) : C \elim p
  | inl a => f a
  | inr b => g b
{%endarend%}

Similarly, "exists" is the propositional truncation of {%ard%}\Sigma{%endard%}:

{%arend%}
\func exists (A : \Type) (B : A -> \Prop) => Trunc (\Sigma (x : A) (B x))
{%endarend%}

Note that the predicate "A is nonempty" defined via {%ard%}exists{%endard%} as 
{%ard%}exists A (\lam _ => Unit){%endard%} ("there exists a : A such that True is true") is equivalent to
{%ard%}Trunc A{%endard%}.

We can use this definition of "exists", for example, to give a proper definition of the 
image of a function:

{%arend%}
\func image {A B : \Type} (f : A -> B) => \Sigma (b : B) (Trunc (\Sigma (a : A) (f a = b)))
{%endarend%}

Note that the definition if the image without truncation is not correct:

{%arend%}
\func image' {A B : \Type} (f : A -> B) => \Sigma (b : B) (\Sigma (a : A) (f a = b))

-- image {Nat} {\Sigma} (\lam _ => ()) == \Sigma
-- image' {Nat} {\Sigma} (\lam _ => ()) == Nat
{%endarend%}

# Equality of types, 'iso'

Consider the following question: given any type, when are its elements equal? 
We have already seen, say, that two pairs are equal iff their components are equal, two functions
are equal iff they are equal pointwise and so on. By now we can offer a characterization of equality
for all types, except {%ard%}\Type{%endard%} and other universes.

Consider several examples of equalities between types:

{%arend%}
\func eq1 : Maybe Unit = Bool => {?}
\func eq2 : (\Sigma Nat Nat) = Nat => {?}
\func eq3 : Bool = Nat => {?}
{%endarend%}

In the first two cases we can prove neither the equalities {%ard%}eq1{%endard%} and {%ard%}eq2{%endard%} nor
their negations. However, the last equality {%ard%}eq3{%endard%} can certainly be disproved: 
{%ard%}Bool = Nat{%endard%} implies that there is a bijection between {%ard%}Bool{%endard%} and
{%ard%}Nat{%endard%}, the assertion which is clearly refutable.

<!--

-- 7. Равенство типов, iso.

-- Мы раньше задавались вопросом когда равны два элемента некоторого типа.
-- Например, мы видели, что две пары равны тогда и только тогда, когда они равны покомпонентно.
-- Две функции равны тогда и только тогда, когда они равны поточечно.
-- Мы можем предложить такую характеризацию для всех типов кроме \Type.

-- Посмотрим на примеры равенств между типами.
-- Можем ли мы доказать, что следующие равенства верны или ложны?
-- ? : Maybe Unit = Bool
-- ? : (\Sigma Nat Nat) = Nat
-- ? : Bool = Nat
-- Для первых двух мы ничего не можем доказать, а про последнее мы можем доказать, что оно ложно.
-- Причина заключается в том, что A = B влечет, что между A и B есть биекция, а между Bool и Nat не может быть биекции.

-- Таким образом, естественно сказать, что два типа равны, если между ними есть биекция.
-- Мы будем использовавть слово "биекция" только для множеств, а для произвольных типов мы будем говорить "эквивалентность", но определение этого понятия такое же.

\func Equiv (A B : \Type) => \Sigma (f : A -> B)
                                    (g : B -> A)
                                    (\Pi (x : A) -> g (f x) = x)
                                    (\Pi (y : B) -> f (g y) = y)

-- p : A = B
-- transport (\lam X => X) p : A -> B

-- Мы можем показать, что если A = B, то между ними есть эквивалентность.
\func equality=>equivalence (A B : \Type) (p : A = B) : Equiv A B =>
  transport (Equiv A) p (\lam x => x, \lam x => x, \lam x => idp, \lam x => idp)

-- Функция iso, определенная в прелюдии, говорит, что верно и обратное.
\func equivalence=>equality (A B : \Type) (e : Equiv A B) : A = B =>
  path (iso e.1 e.2 e.3 e.4)

-- Если у нас есть эквивалентность f : A -> B, то мы можем написать следующую функцию:
-- \lam a => coe (iso f g p q) a right : A -> B
-- Равна ли эта функция исходной f?
-- Ответ: да, так как для coe есть следующее правило:
-- coe (iso f g p q) a right == a

\func transport {A : \Type} (B : A -> \Type) {a a' : A} (p : a = a') (b : B a) : B a'
  => coe (\lam i => B (p @ i)) b right

-- Мы можем переписать это правило через transport вместо coe:
\func test (A B : \Type) (e : Equiv A B)
  : transport (\lam X => X) (equivalence=>equality A B e) = e.1
  => idp

-- Мы хотим не только, чтобы Equiv A B -> A = B, но и чтобы тип A = B был эквивалентен типу функций, являющимися эквивалентностями.
-- Правило, описанное выше позволяет доказать эту эквивалентность в одну сторону.
-- Ее можно доказать и в обратную (почти), но это доказательство я приводить не буду.
-- Так как эта аксиома потребуется в ДЗ, я приведу ее без доказательства (но только для множеств, т.к. для произвольных типов ее нужно немного модифицировать).

\func UA (A B : \Set) : Equiv (A = B) (Equiv A B) => (equality=>equivalence A B, equivalence=>equality A B, LRL A B, RLR A B)
  \where {
    \func LRL (A B : \Set) (p : A = B) : equivalence=>equality A B (equality=>equivalence A B p) = p => {?}
    \func RLR (A B : \Set) (e : Equiv A B) : equality=>equivalence A B (equivalence=>equality A B e) = e => {?}
  }

-- 8. Пример применения унивалентности.

-- Пусть у нас есть некоторый предикат
-- P : (A -> B) -> \Type
-- Пусть у нас есть две функции f и g, которые равны поточечно.
-- Правда ли, что если верно P f, то верно и P g?
-- ? : P f -> P g

-- Так как у нас есть функциональная экстенсиональность, то поточечное равенство функций влечет, что они равны, а следовательно для них верны одни и те же свойства.
-- Если бы у нас ее не было, мы не могли бы доказать этот факт.

-- Для типов можно задать аналогичный вопрос.
-- Унивалентность позволяет нам, доказав какое-то утверждение для одного типа, получить его доказателсьтво для любого равномощного ему.
-- Например, мы знаем, что равенство на Nat разрешимо.
-- Отсюда следует, что равенство на любой счетном множестве тоже разрешимо.
-- Мы можем доказать это и без унивалентности, но доказательство будет сложнее и для каждого предиката нужно выписывать своё доказательство, и существуют предкаты, для которых это вообще не верно без унивалентности.

\data Dec (E : \Type)
  | yes E
  | no (Not E)

\func DecEq (A : \Type) => \Pi (x y : A) -> Dec (x = y)

\func NatDecEq : DecEq Nat => {?} -- Мы это доказывали ранее.

\func isCountable (X : \Type) => Equiv Nat X

\func countableDecEq (X : \Type) (p : isCountable X) : DecEq X =>
  transport DecEq (equivalence=>equality Nat X p) NatDecEq

-- 8. Пропозициональная экстенсиональность.

-- Частный случай унивалентности -- это экстенсиональность для утверждений.
-- Чтобы доказать, что два утверждения равны, достаточно доказать, что одно влечет второе, и второе влечет первое.

\func propExt {A B : \Prop} (f : A -> B) (g : B -> A) : A = B =>
  equivalence=>equality A B (f, g, \lam x => Path.inProp _ _, \lam y => Path.inProp _ _)

-- 9. \Prop является множеством

-- Это можно доказать, но мы не будем этого делать.
\func prop-isSet : isSet \Prop => \lam P Q => {?}

-- 10. \Set не является множеством.

-- Равенства между двумя множествами -- это просто биекции между ними.
-- Следовательно тип таких равенств не является утверждением, так как существуют множества с двумя различными биекциями между ними.
-- Другими словами, \Set не является множеством.

\func not-not (b : Bool) : not (not b) = b
  | true => idp
  | false => idp

\func true/=false (p : true = false) : Empty => absurd (transport T p ())

\func Set-isNotSet (p : isSet \Set) : Empty =>
  \let -- Сначала мы определяем равенство между idp и равенством, соответствующим not.
       | idp=not => p Bool Bool
                      idp -- : Bool = Bool
                      (equivalence=>equality Bool Bool (not, not, not-not, not-not)) -- : Bool = Bool
       -- Теперь легко показать, что биекции, соответствующие этим двум равенствам, равны.
       -- То есть, что тождественная функция равна not.
       | id=not : (\lam x => x) = not => pmap (transport (\lam X => X)) idp=not
       -- Теперь легко получить противоречие.
  \in true/=false (pmap (\lam f => f true) id=not)
-->
