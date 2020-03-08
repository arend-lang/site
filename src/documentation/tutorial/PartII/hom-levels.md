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
{%ard%}\use \level{%endard%}. We will discuss this construct in full generality a bit later, here
we use it as a means to place a data definition {%ard%}D A_1 ... A_n{%endard%} in the universe {%ard%}\Prop{%endard%}
as long as there is a proof of {%ard%}\Pi (a_1 : A_1) ... (a_n : A_n) -> isProp (D a_1 ... a_n){%endard%}:

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

The embedding of {%ard%}\Prop{%endard%} into {%ard%}PropInType{%endard%} is inverse to the map
{%ard%}PropInType-to-Prop{%endard%}, but we have not yet introduced constructs necessary to prove that.
<!--TODO:ref-->

# The universe \Set

# Homotopy levels

<!--

-- 1. Вселенная \Prop и ее эквивалентность с подвселенной \Type.

-- У нас естьспециальная вселенная \Prop, состоящая из типов, удовлетворяющих предикату isProp, то есть из утверждений.
\func isProp (A : \Type) => \Pi (x y : A) -> x = y

-- Мы можем построить функции между \Prop и \Sigma (A : \Type) (isProp A).
\func Prop1 => \Prop
\func Prop2 => \Sigma (A : \Type) (isProp A)

\func pathInProp {A : \Prop} : isProp A => \lam _ _ => idp

-- В одну сторону легко построить функцию, так как любой элемент \Prop является типом и в прелюдии объявленая функция, утверждающая, что любой такой тип является утверждением.
\func Prop1-to-Prop2 (P : \Prop) : Prop2 => (P, pathInProp)

-- Чтобы определить функция в обратную сторону, нам понадобится новая конструкция.
\data Prop2-to-Prop1' (A : \Type) (p : isProp A)
  | inc A
  \where {
    -- Когда мы пишем \use \level, после этого нужно определить функцию, доказывающую утверждение вида \Pi (a_1 : A_1) ... (a_n : A_n) -> D a_1 ... a_n `hasLevel` n для некоторого n,
    -- где D -- это тип данных или класс, для которого это утверждение доказывется (\use \level должен находиться в \where-блоке D), а A_1 ... A_n -- типы его параметров.
    -- Если D -- это класс, то A_1 .. A_n -- это типы любого набора полей D.
    -- После этого гомотопический уровень D становится равным n.

    -- Здесь мы доказываем, что Prop2-to-Prop1' удовлетворяет предикату isProp.
    -- Таким образом, верно, что Prop2-to-Prop1' A p : \Prop для всех A и p.
    -- Без этой функции тип Prop2-to-Prop1' A p будет иметь тот же уровень, что и A.
    \use \level dataIsProp {A : \Type} {p : isProp A} (d1 d2 : Prop2-to-Prop1' A p) : d1 = d2 \elim d1, d2
      | inc a1, inc a2 => pmap inc (p a1 a2)
  }

-- Функции Prop1-to-Prop2 и Prop2-to-Prop1 взаимно обратны, но мы пока не можем доказать этого.
\func Prop2-to-Prop1 (P : Prop2) : \Prop => Prop2-to-Prop1' P.1 P.2

-- 2. Вселенная \Set и ее эквивалентность с подвселенной \Type.

-- Вселенная \Set n эквивалентна \Sigma (A : \Type n) (isSet A).
\func isSet (A : \Type) => \Pi (x y : A) -> isProp (x = y)

-- Аналогичное функции можно определить для \Set, но мы определим только функцию в одну сторону.
\func Set1 => \Set
\func Set2 => \Sigma (A : \Type) (isSet A)

-- Для равенств есть следующее правило.
-- Если A : \(n+1)-Type и a,a' : A, то a = a' : \n-Type

-- Таким оразом, мы можем доказать, что любой элемент \Set удовлетворяет предикату isSet при помощи Path.inProp следующим образом.
-- Многие индуктивные определения попадают во вселенную \Set.
-- Таким образом, мы можем доказать, что они удовлетворяют isSet, при помощи Path.inProp.
-- Именно таким образом мы доказывали, что Nat удовлетворяет ему, в предыдущей лекции.
\func Set1-to-Set2 (P : \Set) : Set2 => (P, \lam x y => pathInProp {x = y})

-- 3. Гомотопический уровень.

-- Типы параметризованы двумя уровнями.
-- Про первый мы уже говорили раньше.
-- Мы будем называть его предикативным уровнем.
-- Второй называется гомотопическим уровнем.

-- Его можно указывать вторым аргументом к \Type или перед Type.
\func bak => \Type 30 66
\func bak' => \66-Type 30

-- Гомотопический уровень начинается не с 0, а с -1, но вселенная с этим уровнем обозначается просто \Prop.
-- У этой вселенной нет предикативного уровня.
\func foo => \Prop

-- У всех остальных вселенных есть оба уровня.
-- Для вселенных, имеющих гомотопический уровень 0, есть специальный синтаксис.
-- Вместо \Type n 0 можно писать \Set n.
\func bar => \Type 30 0
\func bar' => \Set 30

-- Вселенные вкладываются друг в большие вселенные.
-- A : \Type n m => A : \Type (n+1) (m+1)
-- В частности \Prop является наименьшей вселенной.
-- A : \Prop => A : \Type n m

-- Мы можем определить n-уровень индуктивным образом:
\func hasLevel (A : \Type) (n : Nat) : \Type \elim n
  | 0 => isProp A
  | suc n => \Pi (x y : A) -> (x = y) `hasLevel` n

-- Таким образом, isProp A -- это A `hasLevel` 0, а isSet A -- это A `hasLevel` 1.
\func baz => Nat `hasLevel` 1

-- Еще одно полезное свойство гомотопических уровней -- это то, что гомотопический уровень \Pi-типа равен уровню кодомена.
-- A : \Type n m
-- B : A -> \Type n' m'
-- (\Pi (x : A) -> B x) : \Type (\max n n') m'

-- 4. \truncated \data, пропозициональное обрезание.

-- Еще одна новая конструкция: \truncated \data.
-- Она позволяет поместить \data в любой гомотопический уровень.
-- У типа данных, объявленного таким образом, есть одно ограничение.
-- Когда определяется рекурсивная фунция над ним, ее кодомен должен лежать в указанной вселенной.
\truncated \data Trunc (A : \Type) : \Prop
  | trunc A

\func H {A : \Type} {B : \Prop} (f : A -> B) (a : Trunc A) : B \elim a
  | trunc a => f a
  -- H (trunc a) === f a

-- Например, мы не можем определить функцию ex1, так как Nat не лежит во вселенной \Prop.
-- \func ex1 (t : Trunc Nat) : Nat
--   | trunc n => n

-- Но мы можем определить ex2, так как 0 = 0 лежит во вселенной \Prop.
\func ex2 (t : Trunc Nat) : 0 = 0
  | trunc n => idp

-- Trunc A называется (пропозициональным) обрезанием A.
-- Trunc A -- это утверждение, верное тогда и только тогда, когда тип A населен.
-- Если A населен, то очевидно и Trunc A населен.

-- Докажем, что Trunc Empty пуст.
-- Это легко сделать, так как Empty является утверждением.
\func Trunc-Empty (t : Trunc Empty) : Empty \elim t
  | trunc a => a

-- Тип данных будет находится во вселенной \Prop, если у него максимум один конструктор и типы всех параметры этого конструктора лежат в \Prop.
-- Например, T лежит в \Prop.
-- \data T (b : Bool) \with
--   | true => tt

\func T-test (b : Bool) : \Prop => T b

-- 4. Или, существует.

-- Теперь мы можем определить операции "или" и "существует" над утверждениями.
-- Мы можем определить "или" как обрезание Either, либо через \truncated \data.
-- \data Either (A B : \Type) | inl A | inr B
-- \func \fixr 2 Or (A B : \Prop) : \Prop => Trunc (Either A B)

\truncated \data \fixr 2 Or (A B : \Prop) : \Prop
  | inl A
  | inr B

-- "Или" должен удовлетворять трем свойствам:
-- 1. A -> A `Or` B
-- 2. B -> A `Or` B
-- 3. Для любого утверждения C если A -> C и B -> C, то A `Or` B -> C.
-- Первые два свойства -- это просто конструкторы Or, а последнее -- это просто его рекурсор:
\func Or-rec {A B C : \Prop} (f : A -> C) (g : B -> C) (p : A `Or` B) : C \elim p
  | inl a => f a
  | inr b => g b

-- "Существует" тоже легко определяется через Trunc:
\func exists (A : \Type) (B : A -> \Prop) => Trunc (\Sigma (x : A) (B x))

-- 5. Предикат "тип не пуст".

\data Unit | unit

-- В логике первого порядка утверждение о том, что множество A населено, определяется как "существует a : A такой, что верно истинное утверждение".
-- Мы можем повторить это определение:
\func isInhabited' (A : \Type) : \Prop => exists A (\lam _ => Unit)

-- Но у нас есть более простой вариант (который эквивалентен предыдущему определению):
\func isInhabited (A : \Type) : \Prop => Trunc A

-->
