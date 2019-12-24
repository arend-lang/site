---
title: Simple Examples
nav: data-n-proofs
---

In this module we illustrate the concepts that we discussed in the previous module through a bunch of examples of definitions and proofs.

We define the function {%ard%}sort{%endard%} that sorts lists by insertion sort and the function {%ard%}reverse{%endard%} that reverses
them. 

We discuss two more examples of proofs: we prove that {%ard%}reverse{%endard%} is an involution and that {%ard%}+ : Nat -> Nat -> Nat{%endard%}
is associative. 

Next, we turn to a several examples of datatypes. For a given type {%ard%}A{%endard%}, we exhibit two possible definitions of the type
of fixed length vectors of elements of {%ard%}A{%endard%}, one of which is based on _datatypes with constructor patterns_. We conclude with a
discussion of possible definitions of the type of all finite sets.


# Insertion sort and reverse

Among the sorting algorithms, perhaps, the simplest to define in a dependently typed language is the insertion sort. The kind of recursion
used in the insertion sort parallels the inductive definition of the type {%ard%}List{%endard%}.

If our list is {%ard%}nil{%endard%}, then we have nothing to do and simply return {%ard%}nil{%endard%}. Otherwise, if the list is of the form
{%ard%}cons x xs{%endard%}, invoke sort recursively on {%ard%}xs{%endard%} and insert {%ard%}x{%endard%} into the result using the function 
{%ard%}insert{%endard%}, in turn defined by recursion on {%ard%}List{%endard%}:

{%arend%}
\func if {A : \Type} (b : Bool) (t e : A) : A \elim b
  | true => t
  | false => e

\func sort {A : \Type} (less : A -> A -> Bool) (xs : List A) : List A \elim xs
  | nil => nil
  | cons x xs => insert less x (sort less xs)
  \where
    \func insert {A : \Type} (less : A -> A -> Bool) (x : A) (xs : List A) : List A \elim xs
      | nil => cons x nil
      | cons x' xs => if (less x x') (cons x (cons x' xs)) (cons x' (insert less x xs))
{%endarend%}

In case the predicate {%ard%}less{%endard%} defines a linear order, the result of the function {%ard%}sort{%endard%} is a sorted permutation of
its argument {%ard%}xs{%endard%}. This specification of correctness of {%ard%}sort{%endard%} can be phrased in Arend as follows:

{%arend%}
\func isLinOrder {A : \Type} (pred : A -> A -> Bool) : Bool => {?}
\func isSorted {A : \Type} (xs : List A) : Bool => {?}
-- isPerm says that xs' is permutation of xs
\func isPerm {A : \Type} (xs xs' : List A) : Bool => {?}
\func sort-isCorrect {A : \Type} (less : A -> A -> Bool) (xs : List A)
       : T (isLinOrder less) -> T (isSorted (sort less xs) && isPerm xs (sort less xs)) => {?}
{%endarend%}

It is possible to write definitions of the predicates and a proof for {%ard%}sort-isCorrect{%endard%} with the arsenal of language
constructs that we have introduced by now. However, as we will see in the subsequent modules, there are better ways to do this, and 
for that reason we omit the details here. A proper proof will be given in the module TODO: ref.

Consider another, simpler, operation on lists: reversion. We define the function {%ard%}reverse{%endard%} that reverses 
a list {%ard%}xs{%endard%} via an auxiliary function that accumulates reversed sublists in the extra parameter {%ard%}acc{%endard%}:

{%arend%}
\func reverse {A : \Type} (xs : List A) : List A => rev nil xs
  \where
    \func rev {A : \Type} (acc xs : List A) : List A \elim xs
      | nil => acc
      | cons x xs => rev (cons x acc) xs

-- reverse (cons x xs) => rev nil (cons x xs) => rev (cons x nil) xs
-- reverse (reverse (cons x xs)) => reverse (rev (cons x nil) xs) => rev nil (rev (cons x nil) xs)
{%endarend%}

Below we prove that {%ard%}reverse{%endard%} is an involution.

# Examples of proofs: +-assoc and reverse-isInvolution
 
If you try to prove {%ard%}reverse (reverse xs) = xs{%endard%} directly by induction, then you will stuck at proving the equality 
{%ard%}rev nil (rev (cons x nil) xs) = cons x xs{%endard%}, because induction hypothesis is too weak. The statement should be strengthened in
order to make induction hypothesis stronger. Namely, we should prove a more general property of {%ard%}reverse.rev{%endard%} and conclude
that {%ard%}reverse{%endard%} is involution as a consequence:

{%arend%}
\func reverse-isInvolutive {A : \Type} (xs : List A) : reverse (reverse xs) = xs => rev-isInv nil xs
  \where
    \func rev-isInv {A : \Type} (acc xs : List A) : reverse (reverse.rev acc xs) = reverse.rev xs acc \elim xs
      | nil => idp
      | cons x xs => rev-isInv (cons x acc) xs
{%endarend%}

For the proof of associativity of {%ard%}+{%endard%} we need the following property of {%ard%}={%endard%} (congruence): if
{%ard%}f : A -> B{%endard%}, {%ard%}x, y : A{%endard%} and there is a proof {%ard%}p : x = y{%endard%}, then 
there is a proof {%ard%}pmap f p : f x = f y{%endard%}. The proof of {%ard%}(x + y) + z = x + (y + z){%endard%}
is, of course, by induction, but one should carefully choose the parameter for induction. In our case, because
we defined {%ard%}+{%endard%} by recursion on the right argument, we should choose {%ard%}z{%endard%}: 

{%arend%}
\func +-assoc (x y z : Nat) : (x + y) + z = x + (y + z) \elim z
  | 0 => idp
  | suc z => pmap suc (+-assoc x y z)
-- we can apply pmap because of the reductions:
-- (x + y) + suc z => suc ((x + y) + z)
-- x + (y + suc z) => x + suc (y + z) => suc (x + (y + z))
{%endarend%}

# Vectors of fixed length

Assume we want to define a type of _vectors_, that is of lists, whose length is fixed and
parameterized by {%ard%}n : Nat{%endard%}. One way to do this is by writing recursive function
with codomain {%ard%}\Type{%endard%}: 

{%arend%}
\func vec (A : \Type) (n : Nat) : \Type \elim n
  | 0 => \Sigma
  | suc n => \Sigma A (vec A n)

\func head {A : \Type} (n : Nat) (xs : vec A (suc n)) => xs.1

\func tail {A : \Type} (n : Nat) (xs : vec A (suc n)) => xs.2
{%endarend%}

Alternatively, we can realize this type as a datatype. It is a bit tricky since the datatype
{%ard%}Vec (A : \Type) (n : Nat){%endard%} has constructor {%ard%}fcons A (Vec A m){%endard%}
if {%ard%}n{%endard%} is {%ard%}suc m{%endard%} and constructor {%ard%}fnil{%endard%} if {%ard%}n{%endard%}
is {%ard%}0{%endard%}. Such datatypes can be defined using _constructors with patterns_:

{%arend%}
\data Vec (A : \Type) (n : Nat) \elim n
  | 0 => fnil
  | suc n => fcons A (Vec A n)

\func Head {A : \Type} {n : Nat} (xs : Vec A (suc n)) : A \elim xs
  | fcons x _ => x

\func Tail {A : \Type} {n : Nat} (xs : Vec A (suc n)) : Vec A n \elim xs
  | fcons _ xs => xs
{%endarend%}

There are several reasons, why the latter definition with datatypes is preferable. Firstly,
{%ard%}Vec{%endard%} has named constructors, so we explicitly see which constructor we are
dealing with. Secondly, in pattern matching we can use names for parameters of constructors
instead of mere projections {%ard%}.1{%endard%}, {%ard%}.2{%endard%}, etc. These things
make definitions like {%ard%}Vec{%endard%} much more convenient to work with than 
{%ard%}vec{%endard%}.

Below we use double recursion on {%ard%}n{%endard%} and {%ard%}xs{%endard%} to define the 
function {%ard%}first{%endard%} that returns the first element of a vector and the function
{%ard%}append{%endard%} that appends a vector to other vector. Note that the output of
{%ard%}first{%endard%} is not defined for the empty vector. This is typically resolved
by using {%ard%}Maybe{%endard%} datatype as codomain:

{%arend%}
\data Maybe (A : \Type) | nothing | just A

\func first {A : \Type} {n : Nat} (xs : Vec A n) : Maybe A \elim n, xs
  | 0, fnil => nothing
  | suc n, fcons x xs => just x

\func append {A : \Type} {n m : Nat} (xs : Vec A n) (ys : Vec A m) : Vec A (m + n) \elim n, xs
  | 0, fnil => ys
  | suc _ , fcons x xs => fcons x (append xs ys)
{%endarend%}

Implicit arguments in Arend make possible to define rather useless, exotic function
that computes the length of a vector:

{%arend%}
\func length {A : \Type} {n : Nat} (xs : Vec A n) => n
{%endarend%}

# Finite sets, lookup

There are several variants of definition of a type of finite sets as well. For example,
one can define it as a subtype of {%ard%}Nat{%endard%}:

{%arend%}
\func fin (n : Nat) => \Sigma (x : Nat) (T (x < n))
{%endarend%}

Or as a recursive function:

{%arend%}
\func Fin' (n : Nat) : \Set0
  | 0 => Empty
  | suc n => Maybe (Fin' n)
{%endarend%}

Or as a datatype:

{%arend%}
\data Fin (n : Nat) \with
  | suc n => { fzero | fsuc (Fin n) }
{%endarend%}

Consider several examples:

{%arend%}
-- Fin 0 -- empty type
\func absurd {A : \Type} (x : Fin 0) : A

\func fin0 : Fin 3 => fzero
\func fin1 : Fin 3 => fsuc fzero
\func fin2 : Fin 3 => fsuc (fsuc fzero)
-- The following does not typecheck
-- \func fin3 : Fin 3 => fsuc (fsuc (fsuc fzero))
{%endarend%}

It can be easily proven that {%ard%}Fin 3{%endard%} has no more than three elements.
Specifically, it can be proven that every element of {%ard%}Fin 3{%endard%} is either
{%ard%}fin0{%endard%}, {%ard%}fin1{%endard%} or {%ard%}fin2{%endard%}:

{%arend%}
\func atMost3 (x : Fin 3) : Either (x = fin0) (Either (x = fin1) (x = fin2)) \elim x
  | fzero => inl idp
  | fsuc fzero => inr (inl idp)
  | fsuc (fsuc fzero) => inr (inr idp)
  | fsuc (fsuc (fsuc ()))
{%endarend%}

The embedding to {%ard%}Nat{%endard%} can be defined as follows:

{%arend%}
\func toNat {n : Nat} (x : Fin n) : Nat
  | {suc _}, fzero => 0
  | {suc _}, fsuc x => suc (toNat x)
{%endarend%}

The type {%ard%}Fin n{%endard%} can be particularly useful, for example, in a definition
of a safe lookup in a vector:

{%arend%}
\func lookup {A : \Type} {n : Nat} (xs : Vec A n) (i : Fin n) : A \elim n, xs, i
  | suc _, fcons x _, fzero => x
  | suc _, fcons _ xs, fsuc i => lookup xs i
{%endarend%}
