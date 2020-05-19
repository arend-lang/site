---
title: Equality
nav: equality
---

The source code for this module: [equality.zip](code/equality.zip).
{: .notice--success}

In the previous modules we treated the identity type {%ard%}={%endard%} in a rather hand-wavy manner as in most of the cases
we needed just reflexivity {%ard%}idp {A : \Type} {a : A} : a = a{%endard%}. Here we will get into details of the definition
of the identity type and explain some key aspects of it, which will be important for writing more advanced proofs. Along the
way we introduce the _interval type_ {%ard%}I{%endard%}, whose properties are essentially determined by the function
{%ard%}coe{%endard%}, playing the role of _eliminator_ for {%ard%}I{%endard%}. In order to clarify this we briefly
recall the general concept of eliminator.

# Symmetry, transitivity, Leibniz principle 

First of all, we show that the identity type satisfies some basic properties of equality: it is an equivalence relation and 
it satisfies the Leibniz principle.

The Leibniz principle says that if {%ard%}a{%endard%} and {%ard%}a'{%endard%} satisfy the same properties, then they are
equal. It can be easily proven that {%ard%}={%endard%} satisfies this principle: 

{%arend%}
\func Leibniz {A : \Type} {a a' : A}
  (f : \Pi (P : A -> \Type) -> \Sigma (P a -> P a') (P a' -> P a)) : a = a'
  => (f (\lam x => a = x)).1 idp
{%endarend%}

The inverse Leibniz principle (which we will call merely Leibniz principle as well) says that if {%ard%}a = a'{%endard%}, then
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
\func inv {A : \Type} {a a' : A} (p : a = a') : a' = a
    => transport (\lam x => x = a) p idp

-- transitivity
\func trans {A : \Type} {a a' a'' : A} (p : a = a') (q : a' = a'') : a = a''
    => transport (\lam x => a = x) q p

-- congruence
\func pmap {A B : \Type} (f : A -> B) {a a' : A} (p : a = a') : f a = f a'
    => transport (\lam x => f a = f x) p idp
{%endarend%}

**Exercise 1:** Define congruence for functions with two arguments via transport.
It is allowed to use any functions defined via transport.
{: .notice--info}

**Exercise 2:** Prove that {%ard%}transport{%endard%} can be defined via {%ard%}pmap{%endard%} and {%ard%}repl{%endard%} and vice versa.
The function {%ard%}repl{%endard%} says that if two types are equal then there exists a function between them.
{: .notice--info}

# Definition of =

The central ingredient of the definition of the identity type is the _interval type_ {%ard%}I{%endard%} contained in Prelude.
The type {%ard%}I{%endard%} looks like a two-element data type with constructors {%ard%}left{%endard%} and {%ard%}right{%endard%},
but actually it is not: these constructors are made equal (by means of {%ard%}coe{%endard%}). Of course, pattern matching on
{%ard%}I{%endard%} is prohibited since it can be used to derive {%ard%}Empty = Unit{%endard%}.  

The equality {%ard%}left = right{%endard%} implies that some {%ard%}a : A{%endard%} and {%ard%}a' : A{%endard%} are equal if and only if
there exists a function {%ard%}f : I -> A{%endard%} such that {%ard%}f left ==> a{%endard%} and {%ard%}f right ==> a'{%endard%}
(where {%ard%}==>{%endard%} denotes computational equality). The type {%ard%}a = {A} a'{%endard%} is defined simply as the type
of all functions {%ard%}f : I -> A{%endard%} satisfying this property. The constructor {%ard%}path (f : I -> A) : f left = f right{%endard%}
allows to construct equality proofs out of such functions and the function {%ard%}@ (p : a = a') (i : I) : A{%endard%} does the
inverse operation:

{%arend%}
path f @ i ==> f i -- beta-equivalence
path (\lam i => p @ i) ==> p -- eta-equivalence
{%endarend%}

In order to prove reflexivity {%ard%}idp{%endard%} we can simply take the constant function {%ard%}\lam _ => a : I -> A{%endard%}:

{%arend%}
\func idp {A : \Type} {a : A} : a = a => path (\lam _ => a)
{%endarend%}

**Exercise 3:** Prove that {%ard%}left = right{%endard%} without using {%ard%}transport{%endard%} or {%ard%}coe{%endard%}.
{: .notice--info}

If {%ard%}f : A -> B{%endard%} and {%ard%}g : I -> A{%endard%}, then {%ard%}g{%endard%} determines a proof of the equality 
{%ard%}g left = g right{%endard%} and the congruence {%ard%}pmap{%endard%} can be interpreted as simply the composition of
{%ard%}f{%endard%} and {%ard%}g{%endard%}. This observation suggests an alternative definition of {%ard%}pmap{%endard%}: 

{%arend%}
\func pmap {A B : \Type} (f : A -> B) {a a' : A} (p : a = a') : f a = f a'
    => path (\lam i => f (p @ i))
{%endarend%}

This definition of {%ard%}pmap{%endard%} behaves better than others with respect to computational properties. For example, 
{%ard%}pmap id{%endard%} is computationally the same as {%ard%}id{%endard%} and {%ard%}pmap (f . g){%endard%} is
computationally the same as {%ard%}pmap f . pmap g{%endard%}, where (.) is the composition:

{%arend%}
\func pmap-idp {A : \Type} {a a' : A} (p : a = a') : pmap {A} (\lam x => x) p = p
    => idp
{%endarend%}

**Exercise 4:** Prove that {%ard%}a = {A} a'{%endard%} and {%ard%}b = {B} b'{%endard%} implies {%ard%}(a,b) = {\Sigma A B} (a',b'){%endard%} without using {%ard%}transport{%endard%}.
{: .notice--info}

**Exercise 5:** Prove that {%ard%}p = {\Sigma (x : A) (B x)} p'{%endard%} implies {%ard%}p.1 = {A} p'.1{%endard%} without using {%ard%}transport{%endard%}.
{: .notice--info}

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
\func lem : \Pi (X : \Type) -> Either X (X -> Empty) => {?}
\func ugly_num : Nat => \case lem Nat \with { | Left => 0 | Right => 1 }
{%endarend%}

**Exercise 6:** Prove that {%ard%}(\lam x => not (not x)) = (\lam x => x){%endard%}.
{: .notice--info}

# Eliminators

Elimination principles for a data type {%ard%}D{%endard%} specify what kind of data
should be provided in order to define a function from {%ard%}D{%endard%} to a non-dependent or
dependent type. And, essentially, these principles say that it is enough to show how "generators" 
(that is constructors) of {%ard%}D{%endard%} are mapped to a type {%ard%}A{%endard%} and
that that would uniquely determine a function {%ard%}D -> A{%endard%}. For example, eliminators 
for {%ard%}Nat{%endard%} and {%ard%}Bool{%endard%}:

{%arend%}
-- Dependent eliminator for Nat (induction).
\func Nat-elim (P : Nat -> \Type)
               (z : P zero)
               (s : \Pi (n : Nat) -> P n -> P (suc n))
               (x : Nat) : P x \elim x
  | zero => z
  | suc n => s n (Nat-elim P z s n)

-- Non-dependent eliminator for Nat (recursion).
\func Nat-rec (P : \Type)
              (z : P)
              (s : Nat -> P -> P)
              (x : Nat) : P \elim x
  | zero => z
  | suc n => s n (Nat-rec P z s n)

-- Dependent eliminator for Bool (recursor for Bool is just 'if').
\func Bool-elim (P : Bool -> \Type)
                (t : P true)
                (f : P false)
                (x : Bool) : P x \elim x
  | true => t
  | false => f
{%endarend%}

**Exercise 7:** Define factorial via Nat-rec (i.e., without recursion and pattern matching).
{: .notice--info}

**Exercise 8:** Prove associativity of Nat.+ via Nat-elim (i.e., without recursion and pattern matching).
{: .notice--info}

**Exercise 9:** Define recursor and eliminator for {%ard%} \data D | con1 Nat | con2 D D | con3 (Nat -> D) {%endard%}.
{: .notice--info}

**Exercise 10:** Define recursor and eliminator for {%ard%}List{%endard%}.
{: .notice--info}

The function {%ard%}coe{%endard%} thus defines dependent eliminator for {%ard%}I{%endard%},
it says that in order to define {%ard%}f : \Pi (i : I) -> P i{%endard%} for some {%ard%}P : I -> \Type{%endard%}
it is enough to specify {%ard%}f left{%endard%}:

{%arend%}
\func coe (P : I -> \Type)
          (a : P left)
          (i : I) : P i \elim i
  | left => a
{%endarend%}

**Exercise 11:** We defined {%ard%}transport{%endard%} via {%ard%}coe{%endard%}.
It is possible to define a special case of {%ard%}coe{%endard%} via {%ard%}transport{%endard%}.
Define {%ard%} coe0 (A : I -> \Type) (a : A left) : A right {%endard%} via {%ard%}transport{%endard%}.
Is it possible to define {%ard%}transport{%endard%} via {%ard%}coe0{%endard%}?
{: .notice--info}

**Exercise 12:** Define a function {%ard%} B right -> B left {%endard%}.
{: .notice--info}

# left = right

With the use of the function {%ard%}coe{%endard%}, we now prove that {%ard%}I{%endard%} has one element:

{%arend%}
\func left=i (i : I) : left = i
  -- | left => idp
  => coe (\lam i => left = i) idp i

-- In particular left = right.
\func left=right : left = right => left=i right
{%endarend%}

# coe and transport

Functions {%ard%}coe{%endard%} and {%ard%}transport{%endard%} are closely related. Recall the
definition of {%ard%}transport{%endard%} given earlier in this module:

{%arend%}
\func transport {A : \Type} (B : A -> \Type) {a a' : A} (p : a = a') (b : B a) : B a'
     => coe (\lam i => B (p @ i)) b right
{%endarend%}

Denote {%ard%}\lam i => B (p @ i){%endard%} as {%ard%}B'{%endard%}. Then {%ard%}B' : I -> \Type{%endard%},
{%ard%}B' left ==> B a{%endard%}, {%ard%}B' right ==> B a'{%endard%} and 
{%ard%}\lam x => coe B' x right : B' left -> B' right{%endard%}.

# Proofs of non-equalities

In order to prove that {%ard%}true{%endard%} is not equal to {%ard%}false{%endard%} it is enough to define a
function {%ard%}T : Bool -> \Type{%endard%} such that {%ard%}T true{%endard%} is the unit type and 
{%ard%}T false{%endard%} is the empty type. Then the contradiction can be easily derived from 
{%ard%}true = false{%endard%} by means of {%ard%}transport{%endard%}:

{%arend%}
\func true/=false (p : true = false) : Empty => transport T p unit
{%endarend%}

Note that it is not possible to prove that {%ard%}left{%endard%} is not equal to {%ard%}right{%endard%} 
since such {%ard%}T{%endard%} cannot be defined neither recursively nor inductively:

{%arend%}
-- This function does not typecheck!
\func TI (b : I)
  | left => \Sigma
  | right => Empty
{%endarend%}

**Exercise 13:** Prove that {%ard%}0{%endard%} does not equal to {%ard%}suc x{%endard%}.
{: .notice--info}

**Exercise 14:** Prove that {%ard%}fac{%endard%} does not equal to {%ard%}suc{%endard%}.
{: .notice--info}
