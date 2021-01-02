---
title: Basics
nav: syn-n-def
---

The source code for this module: [PartI/Basics.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/Basics.ard) \\
The source code for the exercises: [PartI/BasicsEx.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartI/src/Exercises/BasicsEx.ard)
{: .notice--success}

In this module we explain the syntax and some key constructs of the Arend language, required to get started with
writing definitions, propositions and proofs.

Arend has the following kinds of definitions: functions, data definitions, classes and records. As of now, we only consider
functions and data definitions, exposition of classes and records is deferred to [Records and Classes](records). 

Some of the most basic definitions are built into the language and contained in the module Prelude. For example, Prelude
contains
types {%ard%}Nat{%endard%} and {%ard%}Int{%endard%} of natural and integer numbers respectively and the equality
type {%ard%}={%endard%}.   

# Lexical structure

All keywords in Arend start with backslash {%ard%}\\ {%endard%}. For example, function and data definitions start with
keywords {%ard%}\func{%endard%} and {%ard%}\data{%endard%} respectively.

Numerals, if they occur in terms, are always interpreted as elements of types {%ard%}Nat{%endard%} or {%ard%}Int{%endard%}:
non-negative numerals are of type {%ard%}Nat{%endard%}, negative numerals are of type {%ard%}Int{%endard%}.

Arend allows considerable amount of freedom in the choice of identifiers. With a few exceptions, names of definitions, variables
etc may contain upper or lower case letters, digits and characters from the list `~!@#$%^&*-+=<>?/|[]:_`.

# Functions

Function definitions start with the keyword {%ard%}\func{%endard%}. Functions in Arend are mathematical functions.
In particular, this means that they are _pure_ and do not interact with the environment via input-output.

The simplest definition of a function must contain the name of a function
and its body. For example, the zero constant function `f` without parameters can be defined as follows: 

{% arend %}
\func f => 0 -- constant function
{- Haskell:
   f = 0
-}
{% endarend %}

The body of {%ard%}f{%endard%} is just the numeral {%ard%}0{%endard%} of type {%ard%}Nat{%endard%}. The result type 
{%ard%}Nat{%endard%} of {%ard%}f{%endard%} in this case is inferred by the typechecker, but it can also be specified explicitly:

{% arend %}
\func f' : Nat => 0 -- constant with explicit type
{- Haskell:
   f :: Nat
   f = 0
-}
{% endarend %}  

In case a function has parameters, they can be specified together with their types just after the name of the
function as shown below:

{% arend %}
\func id (x : Nat) => x -- identity function on natural numbers
\func id' (x : Nat) : Nat => x  -- the same, but with explicit result type
{- Haskell:
   id :: Nat -> Nat
   id x = x
-}
\func foo (x _ : Nat) (_ : Int) => x -- simply returning the first argument
{- Haskell:
   foo :: Nat -> Nat -> Int -> Nat
   foo x y z = x
-}
{% endarend %}

As demonstrated in the definition of {%ard%}foo{%endard%}, if a parameter is not used, you can omit the specification
of its name by using the symbol `_`. Also, if several consecutive parameters have the same type, they can be merged:
{%ard%}(x _ : Nat){%endard%} is equivalent to {%ard%}(x : Nat) (_ : Nat){%endard%}.

Note that in contrast to Haskell, types of parameters should always be specified:

{% arend %}
-- \func id'' x => x -- this definition is not correct!
{- Haskell:
   id'' x = x
-}
{% endarend %}

Equivalently, parameters of a function can be moved from the signature to the body by means of lambda expressions:

{%arend%}
 -- types of parameters cannot be inferred as before
\func foo' => \lam (x _ : Nat) (_ : Int) => x
-- but types of parameters can be omitted if the result type is specified explicitly
\func foo'' : Nat -> Nat -> Int -> Nat => \lam x _ _ => x  
{- Haskell:
   foo'' :: Nat -> Nat -> Int -> Nat
   foo'' = \x y z -> x
-}
{%endarend%}

In the examples above we specified the bodies of functions by simply writing a term after the symbol {%ard%}=>{%endard%}.
Of course, there are more sophisticated ways to define the body of a function, for example, in case the function is recursive.
Namely, functions can also be defined by _pattern matching_, we will consider such functions [below](#data-definitions).

# Infix operators

<!-- TODO: illustrate the concepts by giving an example of an expression and explaining how it is parsed -->

By default all binary operators, just as normal functions, are prefix. In order to define an infix operator one should specify before the name
of the operator one of the keywords 
{%ard%}\infix{%endard%}, {%ard%}\infixl{%endard%} or {%ard%}\infixr{%endard%} together with a positive integer for priority:

{%arend%}
\func \infixl 6 $$ (x y : Nat) => x
\func test => 3 $$ 7 -- test returns 3
{- Haskell:
   infixl 6 $$
   ($$) x y = x
   test = 3 $$ 7
-}
{%endarend%}

Priority can be any positive integer between 1 and 9.

Any binary operator, even if it was not declared as infix, can be used in infix form by means of surrounding it with {%ard%}\` \`{%endard%}. 

{%arend%}
\func ff (x y : Nat) => x
\func ff_test => 0 `ff` 1
{- Haskell:
   ff x y = x
   ff_test = 3 `ff` 7
-}
{%endarend%}

Any infix operator can also be used in the prefix from:

{%arend%}
\func \infix 6 %% (x y : Nat) => x
\func %%-test => %% 3 7 -- no need to surround %% with ( )
{- Haskell:
   infix 5 %%
   (%%) x y = x
   pp_test = (%%) 3 7
-}
{%endarend%}

**Exercise 1:** Define priorities of the functions f1, f2, f3, f4, f5 and f6 so that the function 'test' typechecks.
{: .notice--info}
{%arend%}
\func f1 (x y : Nat) => x
\func f2 : Nat => 0
\func f3 (f : Nat -> Nat) (z : Nat) : Int => 0
\func f4 : Nat => 0
\func f5 => f1
\func f6 => f4

\func test => f1 f2 f3 f4 f5 f6
{%endarend%}

# Data definitions

Data definitions allow to define new _inductive_ and _higher-inductive_ types by specifying their ''generating'' elements,
called _constructors_. 

In the simplest case, when constructors do not have parameters, an inductive type is just a finite set formed by its constructors.
For example, the empty type {%ard%}Empty{%endard%}, the one-element unit type {%ard%}Unit{%endard%} and the two-element type 
{%ard%}Bool{%endard%} of boolean values with two constructors {%ard%}true{%endard%} and {%ard%}false{%endard%} can be defined as follows: 

{%arend%}
\data Empty
{- Haskell:
   data Empty
-}

\data Unit | unit
{- Haskell:
   data Unit = Unit
-}

\data Bool | false | true
{- Haskell:
   data Bool = False | True
-}
{%endarend%}

Defining a function on {%ard%}Bool{%endard%} naturally corresponds to specifying its values on {%ard%}true{%endard%}
and {%ard%}false{%endard%} via the mechanism called _pattern matching_. For example, functions {%ard%}not{%endard%} and
{%ard%}if{%endard%} can be defined as follows:

{%arend%}
\func not (x : Bool) : Bool \with -- keyword \with can be omitted
  | true => false
  | false => true
{- Haskell:
   not :: Bool -> Bool
   not True = False
   not False = True
-}

\func if (x : Bool) (t e : Nat) : Nat \elim x
  | true => t
  | false => e
{- Haskell:
   if :: Bool -> Nat -> Nat -> Nat
   if True t e = t
   if False t e = e
-}

{%endarend%}

Typically, inductive types have constructors with parameters. In contrast to parameters of functions, it is allowed 
to write {%ard%}cons T{%endard%} instead of {%ard%}cons (_ : T){%endard%}.
 
Types of these parameters may refer to the inductive type
itself, for example, as we will shortly see in case of the type of natural numbers. However, there is an important restriction:
all occurrences of an inductive type in types of parameters of constructors must be _strictly positive_. This means that 
the inductive type cannot occur to the left of ->. If such definitions were allowed, it would have been possible to
define the type of ''all untyped lambda terms'' {%ard%}K{%endard%}. In particular, non-terminating terms
could have been coded as elements of {%ard%}K{%endard%}.

{%arend%}
\data K | k (K -> K)
\func I => k (\lam x => x)
\func Kc => k (\lam x => k (\lam _ => x))
\func app (f a : K) : K \elim f
  | k f' => f' a
\func omega => k (\lam x => app x x)
{%endarend%}

Let us turn to another example: the type of natural numbers. Definitions of the type {%ard%}Nat{%endard%}
and of operations {%ard%}+{%endard%}, {%ard%}*{%endard%} from Prelude can be reproduced as follows:

{%arend%}
\data Nat | zero | suc Nat

-- the following functions are equivalent
\func three => suc (suc (suc zero))
\func three' => 3

-- there is no limit on the size of numbers
\func bigNumber => 1000000000000000000000000

\func \infixl 6 + (x y : Nat) : Nat \elim y
  | 0 => x
  | suc y => suc (x + y)
{- Haskell:
   (+) :: Nat -> Nat -> Nat
   x + Zero = x
   x + Suc y = Suc (x + y)
-}

-- If n is a variable, then n + 2 evaluates to suc (suc n),
-- but 2 + n does not as it is already in the normal form.
-- This behaviour depends on the definition of +, namely,
-- the argument chosen for pattern matching.

\func \infixl 7 * (x y : Nat) : Nat \elim y
  | 0 => 0
  | suc y => x * y + x
{- Haskell:
   (*) :: Nat -> Nat -> Nat
   x * Zero = 0
   x * Suc y = x * y + x
-}
{%endarend%}

This is not the only way to define a type of natural numbers. The definition above corresponds to unary representation
of natural numbers. The type of binary natural numbers can be defined as follows: 

{%arend%}
\data BinNat
    | zero'
    | sh+1 BinNat -- x*2+1
    | sh+2 BinNat -- x*2+2
{%endarend%}

Efficiency-wise this definition is obviously much better. However, it is much less convenient for proofs by
induction, than the definition of {%ard%}Nat{%endard%} above. And actually the type {%ard%}Nat{%endard%} from Prelude
is efficient as well, because actual implementations of arithmetic operations differ from those above and
efficiently hard coded in ad hoc way.

**Exercise 2:** Define the function 'if', which takes a boolean value b and two elements of an arbitrary type A and return the first element when b equals to true and the second one otherwise.
{: .notice--info}

**Exercise 3:** Define \|\| via 'if'. 
{: .notice--info}

**Exercise 4:** Define the power and the factorial functions for natural numbers. 
{: .notice--info}
{%arend%}
\func \infixr 8 ^ (x y : Nat) => {?}

\func fac (x : Nat) => {?}
{%endarend%}

**Exercise 5:** Define mod and gcd. 
{: .notice--info}

# Termination, div

Functions can be recursive, but they cannot refer to themselves in an arbitrary way. If the recursion were unrestricted,
every proposition could have been trivially proven: 
{%arend%}
\func theorem : 0 = 1 => theorem
{%endarend%}

Moreover, the typechecking procedure in dependently typed language needs to check termination. Consequently, the language
cannot be Turing complete, because typechecking becomes undecidable in this case. 
 
Intensional Martin-Löf type theory avoids this kind of issues by ensuring that all definable functions are total, that is
their evaluation terminates on every input.
It is thus typical for theorem provers, that have Martin-Lof type theory in the core of their type system, to require
all functions to terminate and all recursive functions to be defined by _structural recursion_. And this also
applies to Arend.

For example, consider the division function {%ard%}div{%endard%} for natural numbers. An obvious but not correct
definition may look like this:

{%arend%}
\func div (x y : Nat) : Nat => if (x < y) 0 (suc (div (x - y) y))
{%endarend%}

There are two problems with this definition. Firstly, evaluation of {%ard%}div x 0{%endard%} does not terminate.
Secondly, the recursion is not structural. Structural recursion requires arguments of recursive calls to be 
structurally simpler than the original argument.

A recursive function can often be turned into structurally recursive function by introducing additional parameter, which decreases 
with the increase of the level of recursive calls. Initial value of this parameter can be set to an upper bound to the
number of recursive steps: 
{%arend%}
\func div (x y : Nat) => div' x x y
  \where
    \func div' (s x y : Nat) : Nat \elim s
        | 0 => 0
        | suc s => if (x < y) 0 (suc (div' s (x - y) y))
{%endarend%}

# Polymorphism

Some definitions are polymorphic, that is they can be naturally parameterized by a type. Such definitions
can be stated with the use of the type {%ard%}\Type{%endard%} of all types. For example, the polymorphic identity
function can be stated as follows:

{%arend%}
\func id (A : \Type) (a : A) => a
{- Haskell:
   id :: a -> a
   id x = x
-}

\func idType : \Pi (A : \Type) (a : A) -> A => id
{- Haskell:
   idType :: a -> a
   idType = id
-}
{%endarend%}

The type {%ard%} \Pi (a : A) -> B {%endard%} is the type of dependent functions, which generalizes the type of ordinary functions {%ard%} A -> B {%endard%}.
The codomain of a dependent function may vary dependening on the argument.
For example, the type {%ard%} \Pi (b : Bool) -> if b Nat Bool {%endard%} is the type of functions which accept an argument of type {%ard%} Bool {%endard%} and return either a natural number or a boolean value, depending its argument.
If we pass {%ard%} true {%endard%} to such a function, it returns an element of {%ard%} Nat {%endard%}; otherwise, it returns an element of {%ard%} Bool {%endard%}.

The type {%ard%} \Pi (A : \Type) (a : A) -> A {%endard%} can be equivalently written as {%ard%} \Pi (A : \Type) -> A -> A {%endard%} since its codomain does not depend on the second argument.
This is the type functions which accept a type {%ard%} A {%endard%} and return a function of type {%ard%} A -> A {%endard%}.

Note that {%ard%}\Type{%endard%} is not a type of _all_ types: the famous Girard's paradox states that intensional Martin-Lof's
type theory is inconsistent with the type of all types.
This problem is solved with a hierarchy of universes, which will be discussed [later](universes).
Fortunately, the user does not need to care about these levels for the most part.
Levels are inferred automatically and hidden from the user, unless he or she uses forbidden circularities, in which case typechecker will generate an error.

# Implicit arguments

It is quite often the case that some arguments in a function application are completely determined by others. In 
such cases user may ask typechecker to infer these arguments by writing {%ard%}_{%endard%} in place of them. For 
example, an application of {%ard%}id{%endard%} function defined above may look as follows:  

{%arend%}
\func idTest => id _ 0
{%endarend%}

In this case the typechecker can infer {%ard%}Nat{%endard%} as the value of the first argument, because it must be
the type of the second argument, which is {%ard%}Nat{%endard%}. If the typechecker fails to infer an argument, it
generates an error.

If a parameter of a definition is expected to be always or most of the times determined by others, it can be specified
as _implicit_ by surrounding it in curly braces. In this case the corresponding arguments can be skipped altogether:
  
{%arend%}
\func id' {A : \Type} (a : A) => a

\func id'Test => id' 0
\func id'Test' => id' {Nat} 0 -- implicit arguments can be specified explicitly
{%endarend%}

Of course, the argument inference algorithm is limited and it cannot do too fancy things. Consider, for instance, the following
example:

{%arend%}
\func example' {n : Nat} (p : n + n = 3) => 0
{%endarend%}

In this case the inference algorithm will fail to infer {%ard%}n{%endard%} from the type of {%ard%}p{%endard%} since 
{%ard%}n{%endard%} occurs only inside the invocation of the function {%ard%}+{%endard%}. For example, in the invocation
{%ard%}example' pp{%endard%}, where {%ard%}pp : 8 = 3{%endard%}, the algorithm will not infer that {%ard%}n{%endard%}
is {%ard%}4{%endard%}.

On the other hand, the algorithm will be able infer {%ard%}n{%endard%} and {%ard%}m{%endard%} in the following example:

{%arend%}
\func example'' {n m : Nat} (p : suc n = m) => 0
\func example''Test (pp : 8 = 3) => example'' pp
{%endarend%}

The difference is that in this case {%ard%}n{%endard%} and {%ard%}m{%endard%} occur in invocations of {%ard%}\data{%endard%}
({%ard%}={%endard%} is defined via {%ard%}Path{%endard%}, which is a data type) and the constructor {%ard%}suc{%endard%}.
Since {%ard%}\data{%endard%} and constructors are injective, the algorithm can always infer {%ard%}n{%endard%} and {%ard%}m{%endard%}
in such cases. For example, in the invocation {%ard%}example'' pp{%endard%}, where {%ard%}pp : 8 = 3{%endard%}, the algorithm
will infer that {%ard%}m{%endard%} must be {%ard%}3{%endard%} and {%ard%}n{%endard%} must be {%ard%}7{%endard%}.

# List, append

By now we have discussed all the things necessary to properly define the polymorphic type of lists:

{%arend%}
\data List (A : \Type) | nil | cons A (List A)
{- Haskell:
   data List a = Nil | Cons a (List a)
-}

-- Constructors have implicit parameters for each of the parameters of data type
\func emptyList => nil {Nat}

-- Operator 'append'
\func \infixl 6 ++ {A : \Type} (xs ys : List A) : List A \elim xs
  | nil => ys
  | cons x xs => cons x (xs ++ ys)
{- Haskell:
   (++) :: List a -> List A -> List a
   Nil ++ ys = ys
   cons x xs ++ ys = cons x (xs ++ ys)
-}

{%endarend%}

**Exercise 6:** Define the map function.
{: .notice--info}

**Exercise 7:** Define the transpose function. It takes a list of lists considered as a matrix and returns a list of lists which represents the transposed matrix.
{: .notice--info}

# Tuples and Sigma-types

Given two types {%ard%}A{%endard%} and {%ard%}B{%endard%}, one can construct the type {%ard%}\Sigma A B{%endard%}
of pairs {%ard%}(a, b){%endard%}, where {%ard%}a : A{%endard%} and {%ard%}b : B{%endard%}. The type {%ard%}\Sigma A B{%endard%}
is equivalent to the data type defined as follows:

{%arend%}
\data Pair | pair A B
{%endarend%}

More generally, for any family of types {%ard%}A1{%endard%}, ..., {%ard%}An{%endard%} one can form the type 
{%ard%}\Sigma A1 ... An{%endard%} of tuples {%ard%}(a1, ..., an){%endard%}, where {%ard%}ai : Ai{%endard%}.
A trivial example -- the type {%ard%}\Sigma{%endard%}, which is equivalent to the one-element type {%ard%}Unit{%endard%}.

The tuples can be dependent in the sense that {%ard%}Ai{%endard%} can depend on {%ard%}a1{%endard%}, ..., {%ard%}a{i-1}{%endard%}.
Let us give a few examples of dependent {%ard%}\Sigma{%endard%}-types:
* The type {%ard%}\Sigma (A : \Type) (A -> A){%endard%} consists of pairs {%ard%}(A,f){%endard%}, where {%ard%}A{%endard%} is a type and {%ard%}f{%endard%} is a function of type {%ard%} A -> A {%endard%}.
* The type {%ard%}\Sigma (b : Bool) (if b Nat Bool){%endard%} consists of pairs {%ard%}(b,e){%endard%}, where {%ard%}b{%endard%} is a boolean value and the type of {%ard%}e{%endard%} is {%ard%}if b Nat Bool{%endard%}.
  In particular, pairs {%ard%}(true,7){%endard%} and {%ard%}(false,true){%endard%} belong to this type, but pairs {%ard%}(false,7){%endard%} and {%ard%}(true,true){%endard%} do not.
* We will see that, for every pair of natural numbers {%ard%}n,m : Nat{%endard%}, there is a type {%ard%}n < m{%endard%} of proofs that one of them is less than the other.
  Then we can define the type {%ard%}\Sigma (n : Nat) (n <= 10){%endard%} which consists of natural numbers less than {%ard%}10{%endard%}.
  To be more precise, it consists of pairs {%ard%}(n,p){%endard%}, where {%ard%}n{%endard%} is a natural number and {%ard%}p{%endard%} is a proof that it less than {%ard%}10{%endard%}.
* More interesting example -- the type {%ard%}\Sigma (n : Nat) (\Sigma (k : Nat) (n = k * k)){%endard%} of natural numbers {%ard%}n{%endard%}
  that are full squares: its elements are pairs {%ard%}(n, p){%endard%}, where {%ard%}n{%endard%} is a natural number and 
  {%ard%}p : \Sigma (k : Nat) (n = k * k){%endard%} is a proof that {%ard%}n{%endard%} is a square. 

If {%ard%}x{%endard%} is an element of type {%ard%}\Sigma A1 ... An{%endard%}, i-th component of {%ard%}x{%endard%}, where
i is a numeral, can be accessed by the projection operator {%ard%}x.i{%endard%}. Note that eta equivalence holds for 
Sigma-types: if {%ard%}x : \Sigma A1... An{%endard%}, then {%ard%}(x.1, ..., x.n){%endard%} is computationally equal
to {%ard%}x{%endard%}.  

# Type synonyms

There is no need for type synonyms in dependently types language since we can simply define a function returning the type,
synonym of which is being defined:

{%arend%}
\func NatList => List Nat
{- Haskell:
   type NatList = List Nat
-}
{%endarend%}

# Namespaces and modules

Each definition can be accompanied by {%ard%}\where{%endard%} block in the end. In contrast to Haskell, {%ard%}\where{%endard%} block
is attached to the whole definition, not to a particular clause:

{%arend%}
\func f => g \where \func g => 0
{%endarend%}

Definitions in {%ard%}\where{%endard%} block in almost all respects behave just as normal definitions. The only difference is that
it has different namespace:

{%arend%}  
\func gTest => f.g
{%endarend%}

Alternatively, one can use {%ard%}\let{%endard%}, which is, however, limited and simpler than 'let' in Haskell. In Arend,
{%ard%}\let{%endard%} cannot contain recursive functions and each variable can only depend on previous variables: 

{%arend%}
\func letExample => \let
    | x => 1
    | y => x + x
    \in x + y * y
{%endarend%}

Definitions in Arend can be grouped in _modules_:

{%arend%}
\module M1 \where {
    \func f => 82
    \func g => 77
    \func h => 25
}

-- definitions f, g and h are unavailable in the current namespace
-- they should be accessed with the prefix M1.
\func moduleTest => (M1.f,M1.g,M1.h)
{%endarend%}

If a module is opened by the {%ard%}\open{%endard%} command, then its definitions can be accessed directly without the prefix:

{%arend%}
\module M2 \where {
   \open M1
   \func t => f
   \func t' => g
   \func t'' => h
}
{%endarend%}

It is possible to open just some particular definitions in a module:

{%arend%}
\module M3 \where {
   \open M1(f,g)
   \func t => f
   \func t' => g
   \func t'' => M1.h -- h is not opened and must be accessed with prefix
}
{%endarend%}

For every definition there is a corresponding module:

{%arend%}
\module M4 \where {
   \func functionModule => 34
     \where {
       \func f1 => 42
       \func f2 => 61
       \func f3 => 29
     }
   \func t => functionModule.f1
   \func t' => functionModule.f2
   \func t'' => (f1, f3)
     \where \open functionModule(f1,f3) 
	-- this \open affects everything in \where-block for t''as well as t''
}
{%endarend%}

In case there are clashes between names of definitions in different modules, these definitions can be either hidden or renamed:

{%arend%}
\module M5 \where {
    \open M2 \hiding (t') -- open all definitions except for t'
    \open M3 (t \as M3_t) -- open just t and rename it to M3_t
    \open M4 \using (t \as M4_t) -- open all definition and rename t to M4_t
    \func t'' => (M3_t, M4_t, t', t, functionModule, functionModule.f1, functionModule.f2, functionModule.f3)
    \func t''' => (t'', M2.t'', M4.t'') 
	-- t'' in the current module clashes with t'' from M2 and M4,
	-- the latter definitions should be accessed with prefix
}
{%endarend%}

The command {%ard%}\import X{%endard%} makes file X visible in the current file. Moreover, {%ard%}\import{%endard%} does
everything that {%ard%}\open{%endard%} does, all the constructs for {%ard%}\open{%endard%} are applicable to {%ard%}\import{%endard%} as well:

{%arend%}
-- The sources directory should contain a file named Test.ard (which contains definitions foobar and foobar2)
-- and a directory named TestDir with files Test.ard and Test2.ard in it.

\import Test (foobar \as foobar', foobar2)
\import TestDir.Test
-- if you want to make file visible, but do not want to make \open, you can write the following:
\import TestDir.Test2()
{%endarend%}
