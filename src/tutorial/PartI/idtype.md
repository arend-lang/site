---
title: Equality
toc: false
nav: equality
---

In the previous modules we treated the identity type {%ard%}={%endard%} in a rather hand-wavy manner as in most of the cases
we needed just reflexivity {%ard%}idp {A : \Type} {a : A} : a = a{%endard%}. Here we will get into details of the definition
of the identity type and explain some key aspects of it, which will be important for writing more advanced proofs. Along the
way we introduce the _interval type_ {%ard%}I{%endard%}, whose properties are essentially determined by the function
{%ard%}coe{%endard%}, playing the role of _eliminator_ for {%ard%}I{%endard%}. In order to clarify this we briefly
recall the general concept of eliminator.

# Symmetry, transitivity, Leibniz principle 

First of all, we show that the identity type satisfies some basic properties of equality: it is equivalence relation and 
it satisfies the Leibniz principle.

The Leibniz principle says that if {%ard%}a{%endard%} and {%ard%}a'{%endard%} satisfy the same properties, then they are
equal. It can be easily proven that {%ard%}={%endard%} satisfies this principle: 

{%arend%}
\func Leibniz {A : \Type} {a a' : A}
  (f : \Pi (P : A -> \Type) -> \Sigma (P a -> P a') (P a' -> P a)) : a = a'
  => (f (\lam x => a = x)).1 idp
{%endarend%}

The inverse Leibniz principle (which we will call merely Leibnitz principle as well) says that if {%ard%}a = a'{%endard%}, then
{%ard%}a{%endard%} and {%ard%}a'{%endard%} satisfy the same properties, that is if {%ard%}P a{%endard%} is true, then 
{%ard%}P a'{%endard%} is true. The proof of this is easy, but requires some constructs that will be introduced very shortly
further in this module: 

{%arend%}
\func transport {A : \Type} (B : A -> \Type) {a a' : A} (p : a = a') (b : B a) : B a'
    => coe (\lam i => B (p @ i)) b right
{%endarend%}

Using this latter Leibniz principle, it is easy to prove that {%ard%}={%endard%} satisfies (almost) all the properties
of equality. For example, the following properties: 

{%arend%}
-- symmetry
\func sym {A : \Type} {a a' : A} (p : a = a') : a' = a
    => transport (\lam x => x = a) p idp

-- transitivity
\func trans {A : \Type} {a a' a'' : A} (p : a = a') (q : a' = a'') : a = a''
    => transport (\lam x => a = x) q p

-- congruence
\func pmap {A B : \Type} (f : A -> B) {a a' : A} (p : a = a') : f a = f a'
    => transport (\lam x => f a = f x) p idp
{%endarend%}

# Definition of =

The central ingredient of the definition of the identity type is the _interval type_ {%ard%}I{%endard%} contained in Prelude.
The type {%ard%}I{%endard%} looks like a two-element datatype with constructors {%ard%}left{%endard%} and {%ard%}right{%endard%},
but actually it's not: these constructors are made equal (by means of {%ard%}coe{%endard%}). Of course, pattern matching on
{%ard%}I{%endard%} is prohibited since it can be used to derive {%ard%}Empty = Unit{%endard%}.  

The equality {%ard%}left = right{%endard%} implies that some {%ard%}a : A{%endard%} and {%ard%}a' : A{%endard%} are equal if and only if
there exists a function {%ard%}f : I -> A{%endard%} such that {%ard%}f left ==> a{%endard%} and {%ard%}f right ==> a'{%endard%}
(where {%ard%}==>{%endard%} denotes computational equality). The type {%ard%}a = {A} a'{%endard%} is defined simply as the type
of all functions {%ard%}f : I -> A{%endard%} satisfying this property. The constructor {%ard%}path (f : I -> A) : f left = f right{%endard%}
allows to construct equality proofs out of such functions and the function {%ard%}@ (p : a = a') (i : I) : A{%endard%} makes the
inverse operation:

{%arend%}
path f @ i ==> f i -- beta-equivalence
path (\lam i => p @ i) ==> p -- eta-equivalence
{%endarend%}

In order to prove reflexivity {%ard%}idp{%endard%} we can simply take the constant function {%ard%}\lam _ => a : I -> A{%endard%}:

{%arend%}
\func idp {A : \Type} {a : A} : a = a => path (\lam _ => a)
{%endarend%}

If {%ard%}f : A -> B{%endard%} and {%ard%}g : I -> A{%endard%}, then {%ard%}g{%endard%} determins a proof of the equality 
{%ard%}g left = g right{%endard%} and the congruence {%ard%}pmap{%endard%} can be interpreted as simply the composition of
{%ard%}f{%endard%} and {%ard%}g{%endard%}. This observation suggests an alternative definition of {%ard%}pmap{%endard%}: 

{%arend%}
\func pmap {A B : \Type} (f : A -> B) {a a' : A} (p : a = a') : f a = f a'
    => path (\lam i => f (p @ i))
{%endarend%}

This definition of {%ard%}pmap{%endard%} behaves better than others with respect to computational properties. For example, 
{%ard%}pmap id{%endard%} is computationally the same as {%ard%}id{%endard%} and {%ard%}pmap (f . g){%endard%} is
computationally the same as {%ard%}pmap f . pmap g{%endard%}, where (.) is composition:

{%arend%}
\func pmap-idp {A : \Type} {a a' : A} (p : a = a') : pmap {A} (\lam x => x) p = p
    => idp
{%endarend%}

# Functional extensionality

Function extensionality is a principle saying that if two functions {%ard%}f{%endard%} and {%ard%}g{%endard%} are equal
pointwise, then they are equal functions. Our definition of equality allows us to prove this principle very easily:    

{%arend%}
\func funExt {A : \Type} (B : A -> \Type) {f g : \Pi (a : A) -> B a}
    (p : \Pi (a : A) -> f a = g a) : f = g
    => path (\lam i => \lam a => p a @ i)
{%endarend%}

This useful principle is unprovable in many other intensional dependently typed theories. In such theories function extensionality
can be introduced as an axiom, that is as a function without implementation, however adding new axioms worsens computational properties
of the theory. For example, if we add the axiom of excluded middle {%ard%}lem{%endard%}, then we can define a constant 
{%ard%}ugly_num : Nat{%endard%} that does not evaluate to any concrete natural number:   

{%arend%}
\func lem : \Pi (X : \Type) -> Either X (X -> Empty)
\func ugly_num : Nat => \case lem Nat \with { | Left => 0 | Right => 1 }
{%endarend%}

# Eliminators

-- Элиминатор для Nat
\func Nat-elim (P : Nat -> \Type)
               (z : P zero)
               (s : \Pi (n : Nat) -> P n -> P (suc n))
               (x : Nat) : P x \elim x
  | zero => z
  | suc n => s n (Nat-elim P z s n)

-- Рекурсор для Nat
\func Nat-rec (P : \Type)
              (z : P)
              (s : Nat -> P -> P)
              (x : Nat) : P \elim x
  | zero => z
  | suc n => s n (Nat-rec P z s n)

-- Элиминатор для Bool (рекурсор для Bool -- это просто if).
\func Bool-elim (P : Bool -> \Type)
                (t : P true)
                (f : P false)
                (x : Bool) : P x \elim x
  | true => t
  | false => f

{-
\func coe (P : I -> \Type)
          (a : P left)
          (i : I) : P i \elim i
  | left => a
-}

# left = right

-- Чтобы доказать, что в I действительно только один элемент, нам нужно использовать функцию coe, определенную в прелюдии.
-- О ней можно думать как об элиминаторе для I.
-- Она говорит, что для определения функции над I достаточно определить ее для left.
-- Для сравнения элиминатор для Bool говорит, что для определения функции над Bool достаточно определить ее для true и false.

-- Используя coe, легко доказать, что любой i : I равен left.
\func left=i (i : I) : left = i
  -- | left => idp
  => coe (\lam i => left = i) idp i

-- В частности left = right.
\func left=right : left = right => left=i right

# coe and transport

-- Функция coe тесно связана с transport.
-- Мы определили transport через coe.

-- \func transport {A : \Type} (B : A -> \Type) {a a' : A} (p : a = a') (b : B a) : B a'
--     => coe (\lam i => B (p @ i)) b right
-- Пусть B' == \lam i => B (p @ i).
-- Тогда
-- B' : I -> \Type
-- B' left == B a
-- B' right == B a'
--
-- \lam x => coe B' x right : B' left -> B' right

-- В ДЗ нужно будет показать, что через transport определеяется частный случай coe.

# Proofs of non-equalities

-- Чтобы доказать, что true не равно false, достаточно определить функцию T : Bool -> \Type, которая на true равна населенному типу, а на false пустому.
-- Тогда из true = false легко вывести противоречие, используя transport.
\func true/=false (p : true = false) : Empty => T-absurd (transport T p tt)

-- Мы не можем доказать, что left не равно right, так как мы не можем определить такую функцию для I ни рекурсивно, ни через \data.
{-
\func TI (b : I)
  | left => \Sigma
  | right => Empty

\data TI' (b : I) \with
  | left => ti
-}

