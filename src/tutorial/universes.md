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

-- Еще несколько примеров:
\func test1 => id Nat 0
\func test2 => id \Type0 Nat
\func test3 => id (\Type0 -> \Type1) (\lam X => X)
\func test4 => id _ id
\func test4' => id (\Pi (A : \Type) -> A -> A) id

-- При обращении к определению можно явно указать его уровень, то есть чему будет равен параметр \lp:
\func test5 => id (\Type \lp) Nat
-- Либо так:
\func test5' => id (\level (\suc \lp) _) (\Type \lp) Nat
-- Второй вариант синтаксиса полезен когда уровень является константой:
\func test6 => id (\level 2 _) \Type1 \Type0
-- Если при обращению к определению уровень не указан явно, он будет выведен автоматически как и в случае с \Type.
-- В большинстве случаев нет необходимости указывать уровень явно.

-- Параметры \data не влияют на его уровень.
\data Magma' (A : \Type)
  | con (A -> A -> A)

\func test7 : \Type \lp => Magma' \lp Nat

-- Уровень класса зависит от того, какие поля реализованы.
\class Magma (A : \Type)
  | \infixl 6 ** : A -> A -> A

-- Например, уровень Magma \lp -- это \Type (\suc \lp), так как в определении Magma \lp появляется вселенная \Type \lp.
\func test8 : \Type (\suc \lp) => Magma \lp

-- Но уровень Magma \lp Nat -- это просто \Type 0, так как в нереализованных полях Magma Nat не встречаются вселенные.
\func test9 : \Type \lp => Magma \lp Nat

\class Functor (F : \Type -> \Type)
  | fmap {A B : \Type} : (A -> B) -> F A -> F B

\data Maybe (A : \Type) | nothing | just A

-- Уровень Functor \lp будет \Type (\suc \lp) даже если поле F реализовано, так как в поле fmap тоже появляется \Type \lp.
\func test10 : \Type (\suc \lp) => Functor \lp Maybe

# Induction principles

-- Элиминатор для рекурсивного типа данных -- это просто принцип индукции для него.
-- Мы можем определять свои принципы индукции, которые удобнее использовать, чем стандартные.
-- Например, для натуральных чисел мы можем определить принцип индукции, который позволяет использовать индукционную гипотезу для любого числа, меньшего данного, а не только для числа, меньшего на 1.
\func Nat-ind (E : Nat -> \Type)
  (r : \Pi (n : Nat) -> (\Pi (k : Nat) -> T (k < n) -> E k) -> E n)
  (n : Nat) : E n => {?} -- Доказательство упражнение

# Induction-recursion

-- Рекурсия-рекурсия -- это принцип, позволяющий определять взаимно рекурсивные функции.
-- Пример: функции isEven и isOdd.
\func isEven (n : Nat) : Bool
  | 0 => true
  | suc n => isOdd n

\func isOdd (n : Nat) : Bool
  | 0 => false
  | suc n => isEven n

-- Индукция-индукция -- это принцип, позволяющий определять взаимно рекурсивные типы данных.
-- Когда мы определяем взаимно рекурсивный тип данных, нужно явно указывать его тип.
-- Пример: типы IsEven и IsOdd.
\data IsEven (n : Nat) : \Type \with
  | 0 => zero-isEven
  | suc n => suc-isEven (IsOdd n)

\data IsOdd (n : Nat) : \Type \with
  | suc n => suc-isOdd (IsEven n)

-- Индукция-рекурсия -- это принцип, позволяющий определять тип данных, взаимно рекурсивный с функцией.
-- Мы увидим пример такого определения ниже.

# Universes

-- \Type0 -- это тип, элементы которого -- это малые типы.
-- Такой тип называется вселенной.
-- Мы можем определить свою вселенную, состоящую только из определенного набора типов.

\data Type
  | nat
  | list Type
  | arr Type Type

-- Мы должны еще определить функцию, которая переводит элементы Type в настоящие типы.
\func El (t : Type) : \Type0 \elim t
  | nat => Nat
  | list t => List (El t)
  | arr t1 t2 => El t1 -> El t2

\func idc (t : Type) (x : El t) : El t => x

-- Если мы хотим определить вселенную, в которой у нас есть заисимые типы, то такое определение должно быть индуктивно-рекурсивным.
\data Type' : \Type0
  | nat'
  | list' Type'
  | pi' (a : Type') (El' a -> Type')

\func El' (t : Type') : \Type0 \elim t
  | nat' => Nat
  | list' t => List (El' t)
  | pi' t1 t2 => \Pi (a : El' t1) -> El' (t2 a)

# Completeness of specification

-- Спецификация для некоторого значения a типа A -- это просто предикат вида P : A -> \Type.
-- То есть спецификация -- это просто свойство элемента, которое мы хотим про него доказать.

-- Спецификация корректна, если верно P a.
-- Спецификация полна, если P x влечет x = a для любого x : A.

-- Например, пусть у нас есть функция, вычисляющая факториал fac : Nat -> Nat.
-- P1 -- корретная спецификация для fac, но не полная.
-- \func P1 (f : Nat -> Nat) => f 3 = 6
-- P2 -- полная, но не корректная
-- \func P2 (f : Nat -> Nat) => Empty
-- P3 -- полная и корректная спецификация для fac.
-- \func P3 (f : Nat -> Nat) => \Sigma (f 0 = 1) (\Pi (n : Nat) -> f (suc n) = suc n * f n)

-- Полная и корректная спецификация для функции сортировки:
-- \func P (f : List A -> List A) => \Pi (xs : List A) -> \Sigma (isSorted (f xs)) (isPerm (f xs) xs)
-- где isSorted xs верно тогда и только тогда, когда список xs отсортирован, а isPerm xs ys верно тогда и только список xs является перестановкой списка ys.

-- Разумеется, мы хотим, чтобы спецификация была, по крайней мере, корректной.
-- Мы можем не требовать полноты, если полную спецификацию слишком сложно проверить, и нам достаточно истинности частичной спецификации.
-- Тем не менее полезно понимать когда спецификация является полной.

-- Есть простое необходимое (и достаточное для корректных спецификаций) условие полноты, которое не зависит от элемента, для которого задается спецификация:
-- \Pi (x y : A) -> P x -> P y -> x = y
-- То есть должно существовать не более одного элемента, на котором предикат верен.
