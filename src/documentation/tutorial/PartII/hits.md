---
title: Spaces and Homotopy Theory
nav: hits
---

The source code for this module: [PartII/Spaces.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartII/src/Spaces.ard) \\
The source code for the exercises: [PartII/SpacesEx.ard](https://github.com/arend-lang/tutorial-code/blob/master/PartII/src/Exercises/SpacesEx.ard)
{: .notice--success}

By now we have been mostly living in the world of propositions and sets, where the structure of the type
{%ard%}x = y{%endard%} is degenerate so that we could think of it either as a mere propositional equality type or as a set
of bijections between {%ard%}x{%endard%} and {%ard%}y{%endard%} if {%ard%}x y : \Set{%endard%} are sets (by univalence). 

In this module we will undertake a brief detour to a nondegenerate side of homotopy type theory, where
it becomes important that the type {%ard%}x = y{%endard%} is actually the type of paths between points {%ard%}x{%endard%} and
{%ard%}y{%endard%} of a space. 

We give several examples of datatypes of spaces, namely, spheres of various dimensions and the torus.
One way to think about these types is as being generated not only by usual constructors, but also by
_path-constructors_. The corresponding elimination principles are called _higher recursion/induction_.

Under the types-are-spaces view one can prove various theorems from homotopy theory. As an example, we discuss
type-theoretic version of the classical proof that the fundamental group of the circle is isomorphic to integers.
We also discuss the Eilenberg-Maclane spaces and equivalence between the category of connected pointed 1-types and
the category of groups.

# Types as spaces

In [Part I](/documentation/tutorial/PartI) we defined the equality type {%ard%}x = y{%endard%}, where {%ard%}x y : A{%endard%}, as the
type {%ard%}I -> A{%endard%} of functions {%ard%}f{%endard%} such that {%ard%}f left ==> x{%endard%}
and {%ard%}f right ==> y{%endard%}. We showed that this type behaves as you would expect equality
to behave. 

An obvious observation about this definition, which we now make explicitly: if we think of types as topological
spaces, the type {%ard%}I{%endard%} as the interval and functions as continuous functions, then {%ard%}x = y{%endard%}
is precisely _the type of paths_ between {%ard%}x{%endard%} and {%ard%}y{%endard%}.

Let us explore this view a bit further. Consider a dependent type {%ard%}B : I -> \Type{%endard%} over {%ard%}I{%endard%}
and a point {%ard%}b : B left{%endard%}. Eliminator for {%ard%}I{%endard%}, the function {%ard%}coe{%endard%}, can be used
to lift the path {%ard%}left = right{%endard%} to a path {%ard%}p := path (\lam i => coe B b i){%endard%} starting at {%ard%}b{%endard%}.
This path in general goes across different types {%ard%}B i{%endard%} and lies in the heterogeneous type of paths 
{%ard%}Path B b (coe B b right){%endard%}. The right point {%ard%}transport B p b ==> (coe B b right){%endard%} can
be thought of as {%ard%}b{%endard%} transported along the path {%ard%}p{%endard%}.

Thus one can recognise that {%ard%}B{%endard%} defines _a fibration_ over {%ard%}I{%endard%} and {%ard%}(\lam i => coe B b i) : \Pi (i : I) -> B i{%endard%}
is a section of the fibration. More generally, dependent types {%ard%}B : A -> \Type{%endard%} correspond to fibrations {%ard%}p1 : \Sigma A B -> A{%endard%} (here 
{%ard%}p1{%endard%} is the projection to the first component) over {%ard%}A{%endard%} with fibers {%ard%}B x{%endard%}
over points {%ard%}x : A{%endard%} and the total space {%ard%}\Sigma A B{%endard%}. Note that if {%ard%}b : B x{%endard%}, then
heterogeneous paths {%ard%}Path (\lam i => B (p @ i)) b (transport B p b){%endard%} correspond to paths in the total space of fibration
(that is a homogeneous path in {%ard%}\Sigma A B{%endard%}) lying over {%ard%}p{%endard%}. We will discuss examples of
fibrations (namely, universal cover and path fibration) of topological nature in the section about the fundamental group of the circle below.

Another important remark: if {%ard%}f : A -> B{%endard%} is a "bijection" between types, namely, it satisfies {%ard%}isBij{%endard%}
where {%ard%}\Set{%endard%} replaced with {%ard%}\Type{%endard%}, then the types {%ard%}A{%endard%} and {%ard%}B{%endard%}
correspond to _homotopy equivalent_ spaces and {%ard%}f{%endard%} is an equivalence. The function {%ard%}iso{%endard%} allows 
to construct a path between such spaces and the univalence says that the type of equivalences between types is equivalent to the 
type of paths between the types.
 
# Spaces: spheres, torus

We can use datatypes with conditions to define the circle: just take the interval {%ard%}I{%endard%}
and glue its two endpoints {%ard%}left{%endard%} and {%ard%}right{%endard%}. Specifically, we add
the constructor {%ard%}base{%endard%} for the basepoint, the loop constructor {%ard%}loop I{%endard%} and
conditions saying that endpoints of the loop evaluate to the basepoint: {%ard%}loop left ==> base{%endard%},
{%ard%}loop right ==> base{%endard%}.

{%arend%}
\data Circle
  | base
  | loop I \with {
    | left => base
    | right => base
  }
{%endarend%}

Higher dimensional spheres are also easy to define using the construction called _suspension_. For a type
{%ard%}A{%endard%} its suspension {%ard%}Susp A{%endard%} is a type with two points {%ard%}S{%endard%}
and {%ard%}N{%endard%} and for every element {%ard%}a : A{%endard%} a path {%ard%}merid a i{%endard%}
between {%ard%}S{%endard%} and {%ard%}N{%endard%}: {%ard%}merid a left ==> S{%endard%},
{%ard%}merid a right ==> N{%endard%}.

{%arend%}
\data Susp (A : \Type)
   | S | N
   | merid A (i : I) \elim i {
      	| left => S
        | right => N
   }
{%endarend%}

The spheres can now be defined inductively as follows:

{%arend%}
\func Sphere (n : Nat) : \Type \lp \oo
    | 0 => Susp Empty
    | suc n => Susp (Sphere n)
{%endarend%}

It is easy to see that the type {%ard%}Circle{%endard%} is equivalent to the type {%ard%}Sphere 1{%endard%}:

{%arend%}
\func CircleToSphere1 (x : Circle) : Sphere 1
    | base => S
    | loop i => (path (merid N) *> inv (path (merid S))) @ i 

\func Sphere1ToCircle (x : Sphere 1) : Circle
    | S => base
    | N => base
    | merid S i => loop i
    | merid N i => base
    | merid (merid () _) _
{%endarend%}  

**Exercise 1:** Prove that {%ard%}CircleToSphere1{%endard%} and {%ard%}Sphere1ToCircle{%endard%} are mutually
inverse.
{: .notice--info}

Consider another elementary topological space: the torus. We can directly apply the standard way of constructing
the torus by identifying opposite sides of the square.

{%arend%}
\data Torus
  | point
  | line1  I \with { left => point | right => point }
  | line2  I \with { left => point | right => point }
  | face I I \with {
    | left, i => line2 i
    | right, i => line2 i
    | i, left => line1 i
    | i, right => line1 i
  }
{%endarend%}

**Exercise 2:** Prove that {%ard%}Torus{%endard%} is equivalent to the direct product {%ard%}\Sigma Circle Circle{%endard%}
of circles.
{: .notice--info}


# Higher induction principles

We have shown how to define spaces using the interval type and ordinary datatypes with conditions. The types of spaces defined
in this way thus satisfy the ordinary elimination principle for datatypes with conditions. 

Alternatively, we can look at the type of a space as being generated by ordinary constructors, called _point-constructors_,
together with higher level _path-constructors_. For example, the circle is generated by the point-constructor {%ard%}base{%endard%}
and the path-constructor {%ard%}loop : base = base{%endard%}, the 2-sphere is generated by {%ard%}base{%endard%} and
2-path-constructor {%ard%}surf : idp {base} = idp {base}{%endard%}, and so on. 

Let us illustrate the idea of how to formulate the higher recursion and higher induction principles in the simple case of the circle.
The higher recursion principle for the circle says, that a function from {%ard%}Circle{%endard%}
to a type {%ard%}B{%endard%} can be defined by choosing a point {%ard%}b : B{%endard%} and a loop {%ard%}l : b = b{%endard%} in
{%ard%}B{%endard%}.

{%arend%}
\func circRec {B : \Type} {b : B} (l : b = b) (x : Circle) : B \elim x 
    | base => b
    | loop i => l @ i
{%endarend%}

If we denote {%ard%}circRec {b} l{%endard%} as {%ard%}f : Circle -> B{%endard%}, then {%ard%}f base ==> b{%endard%} and 
{%ard%}pmap f (path loop) = l{%endard%}.

This can be generalized to the higher induction principle, that is to the case when {%ard%}B : Circle -> \Type{%endard%} is a dependent type.
In that case we should pick a point {%ard%}b : B base{%endard%} and specify a _dependent loop_ in {%ard%}B{%endard%}. Since we
do have in Arend heterogeneous path types, we can specify a dependent loop simply as an element in {%ard%}Path (\lam i => B (loop i)) b b{%endard%}.
However, in some cases it is more convenient to use characterisation of dependent loops in terms of homogeneous path types:
it can be shown that dependent loops correspond to paths {%ard%}transport B (path loop) b = b{%endard%}.

{%arend%}
\func concat {A : I -> \Type} {a : A left} {a' a'' : A right} (p : Path A a a') (q : a' = a'') : Path A a a'' \elim q
  | idp => p

\func circInd (B : Circle -> \Type) (b : B base) (l : transport B (path loop) b = b) (x : Circle) : B x \elim x
  | base => b
  | loop i => (concat {\lam i => B (loop i)} (path (\lam i => coe (\lam j => B (loop j)) b i)) l) @ i
{%endarend%}

Below, while proving theorems about the fundamental group, we will see that this induction principle is useful.

# The fundamental group

In the module [Equality](/documentation/tutorial/PartI/idtype) we showed how the equality type of a 1-type {%ard%}X{%endard%} gives rise to
a groupoid structure on {%ard%}X{%endard%}. This is precisely the groupoid of paths in the space {%ard%}X{%endard%}:
morphisms between points {%ard%}x : X{%endard%} and {%ard%}y : Y{%endard%} are paths between {%ard%}x{%endard%} and {%ard%}y{%endard%}.
In particular, the loops {%ard%}x = x{%endard%} at a point {%ard%}x : X{%endard%} form a group with composition as the group operation.
This group {%ard%}pi1(X, x){%endard%} is called _the fundamental group_ of {%ard%}X{%endard%}. In the Arend standard library the 
corresponding instance of the class {%ard%}Group{%endard%} is called {%ard%}Aut{%endard%}.

{%arend%}
-- The instance of 'Group' defined in 'Algebra.Group.Aut' 
\instance Aut {A : \1-Type} (a : A) : Group (a = a)
  | ide => idp
  | * => *>
  | ide-left => idp_*>
  | ide-right _ => idp
  | *-assoc => *>-assoc
  | inverse => inv
  | inverse-left => inv_*>
  | inverse-right => *>_inv

\func pi1-1 (X : \1-Type) (x : X) => Aut x

\func pi1Mult {X : \1-Type} {x : X} (a b : pi1-1 X x) => a * b
{%endarend%}

Assume {%ard%}X{%endard%} is connected, that is for all pairs {%ard%}x y : X{%endard%} the proposition {%ard%}TruncP (x = y){%endard%} holds,
where {%ard%}TruncP{%endard%} is the propositional truncation.
It is easy to see, that the definition {%ard%}pi1(X, x){%endard%} does not depend on {%ard%}x{%endard%} in the sense that
the groups {%ard%}pi1-1(X, x){%endard%} for different choice of {%ard%}x{%endard%} are isomorphic.
This group assigned to a space is one of the simplest examples of an algebraic invariant of a space: the fundamental groups of homotopy equivalent
spaces are isomorphic.

**Exercise 3:** Let {%ard%}X : \1-Type{%endard%} be connected. Prove that the groups {%ard%}pi1-1 X x{%endard%} and {%ard%}pi1-1 X y{%endard%} are
isomorphic for all {%ard%}x y : X{%endard%}.
{: .notice--info}

The definition of {%ard%}pi1-1{%endard%} above can, of course, be generalized from 1-types to arbitrary types by means of truncation.

{%arend%}
\truncated \data Trunc1 (A : \Type) : \1-Type
  | trunc A

\func pi1 (X : \Type) (x : X) : Group => pi1-1 (Trunc1 X) (trunc x)

\truncated \data Trunc0 (A : \Type) : \Set
  | trunc A

-- Equivalently, we can truncate 'x = x'.
-- The group structure 'Aut' can be straightforwardly translated to this case.
\func pi1' (X : \Type) (x : X) : \Set => Trunc0 (x = x)
{%endarend%}

Exercise 3 implies that {%ard%}pi1{%endard%} maps connected pointed spaces to groups:

{%arend%}
\func isConnected (X : \Type) => \Pi (x y : X) -> TruncP (x = y)

-- The class 'Pointed' is defined in 'Homotopy.Pointed'.
\func pi1 (A : \Sigma (X : Pointed) (isConnected X)) : Group  => pi1-1 (Trunc1 A.1) (trunc base)
{%endarend%}

As we will see later in this module, there is an inverse function {%ard%}K1 : Group -> \Sigma (X : Pointed) (isConnected X){%endard%}, called
the _Eilenberg-Maclane space_. The corresponding functors of {%ard%}pi1{%endard%} and {%ard%}K1{%endard%} establish equivalence of the category
of pointed connected 1-types and the category of groups.


# The fundamental group of the circle

Let us now consider an example of a calculation of the fundamental group. We will outline the proof from the Arend standard library that for {%ard%}Sphere1{%endard%} holds
{%ard%}(base1 = base1) = Int{%endard%}, where {%ard%}Sphere1{%endard%} is {%ard%}Circle{%endard%} and {%ard%}base1{%endard%} is {%ard%}base{%endard%}
in the notation we used above. This implies that {%ard%}pi1 Sphere1 base1 = Int{%endard%} as well as that {%ard%}Sphere1{%endard%} is 1-type.

The type-theoretic proof of {%ard%}(base1 = base1) = Int{%endard%} follows quite closely the classical homotopy-theoretic proof. First note, that
it is very easy to construct a "winding" homomorphism from the group {%ard%}Int{%endard%} to the group {%ard%}base1 = base1{%endard%}, which sends the generator
{%ard%}1{%endard%} to the generator {%ard%}path loop{%endard%}:

{%arend%}
\func wind (x : Int) : base1 = base1
  | pos 0 => idp
  | pos (suc n) => wind (pos n) *> path loop
  | neg (suc n) => wind (neg n) *> inv (path loop)
{%endarend%}
 
In order to costruct the inverse map we will need to define a fibration over the circle, called the _universal cover_.
This amouts to constructing a specific dependent type, which we denote as {%ard%}code{%endard%}.
 
Geometrically the universal cover of the circle is a winding of the real line over the circle and
can be visualized as a helix. Note that {%ard%}code x{%endard%} would be the fiber over {%ard%}x{%endard%} and {%ard%}\Sigma (x : Sphere1) (code x){%endard%}
the total space, that is the real line in our case.
If {%ard%}y : code base1{%endard%} is a point in the fiber over {%ard%}base1{%endard%},
then a loop {%ard%}l : base1 = base1{%endard%} can be lifted to a path {%ard%}y = transport code l y{%endard%} in the covering space, where {%ard%}transport code l y{%endard%}
is a point in the same fiber. 

This gives us a map from loops {%ard%}base1 = base1{%endard%} to points in the fiber over {%ard%}base1{%endard%}.
We can identify the fiber with {%ard%}Int{%endard%} so that the map becomes a homomorphism of groups: simply set {%ard%}code base1 ==> Int{%endard%}
and define {%ard%}code (loop i){%endard%} in such a way that transporting of {%ard%}n{%endard%} along {%ard%}path loop{%endard%} results in 
{%ard%}n + 1{%endard%}. The latter can be easily done by means of employing nontrivial structure of equality of types given by {%ard%}iso{%endard%}
and univalence: mutually inverse automorphisms {%ard%}isuc{%endard%} (which is {%ard%}(+1){%endard%}) and {%ard%}ipred{%endard%}(which is {%ard%}(-1){%endard%}) of
{%ard%}Int{%endard%} define a loop on {%ard%}Int{%endard%}, which we can use!

{%arend%}
\func code (x : Sphere1) : \Set0
  | base1 => Int
  | loop i => iso isuc ipred ipred_isuc isuc_ipred i
{%endarend%}

We can now define the map {%ard%}encode{%endard%} that maps a path {%ard%}p : base1 = x{%endard%} to the point in the fiber {%ard%}code x{%endard%},
which is the transport of {%ard%}0{%endard%} along {%ard%}p{%endard%}:

{%arend%}
\func encode (x : Sphere1) (p : base1 = x) : code x => transport code p 0
{%endarend%}

Thus we have defined functions in both directions {%ard%}wind : Int -> base1 = base1{%endard%} and {%ard%}encode base1 : base1 = base1 -> Int{%endard%}.
It remains to prove that they are mutually inverse. The key idea is inspired by the classical proof: prove equivalence between universal cover
and the path fibration {%ard%}\lam x : Sphere1 => base1 = x{%endard%}, which represents all the paths in {%ard%}Sphere1{%endard%} with
one endpoint fixed at {%ard%}base1{%endard%}. The equivalence of fibers over {%ard%}base1{%endard%}, that is of {%ard%}code base1 ==> Int{%endard%} and
{%ard%}base1 = base1{%endard%}, would follow.

We have already defined the map {%ard%}encode{%endard%} from path fibration to universal cover. The inverse function 
{%ard%}decode (x : Sphere1) : code x -> base1 = x{%endard%} can be defined using the higher induction principle for the circle, which we described above.
The full definition of  {%ard%}decode{%endard%} as well as the proofs {%ard%}encode_decode{%endard%}, {%ard%}decode_encode{%endard%} that
{%ard%}encode{%endard%} and {%ard%}decode{%endard%} are mutually inverse are technical, we omit them here. The rest of the proof can be found in the
Arend standard library.

# Eilenberg-Maclane space

Given a group {%ard%}G{%endard%} we now construct a pointed connected 1-type {%ard%}K1 G{%endard%} such that the fundametal group of {%ard%}K1 G{%endard%} is 
{%ard%}G{%endard%}. The type {%ard%}K1 G{%endard%} is called the _Eilenberg-Maclane space_. This type can be defined as the type with the base point {%ard%}base{%endard%},
for every {%ard%}g : G{%endard%} the loop constructor {%ard%}loop g i{%endard%} and for every {%ard%}g g' : G{%endard%} the 2-cell {%ard%}relation g g' i j{%endard%},
which equalizes the composition of loops {%ard%}path (loop g) *> path (loop g'){%endard%} and the loop {%ard%}path (loop (g * g')){%endard%}.

{%arend%}
\data K1 (G : Group)
  | base
  | loop G (i : I) \elim i {
    | left => base
    | right => base
  }
  | relation (g g' : G) (i : I) (j : I) \elim i, j {
    | left, j => base
    | right, j => loop g' j
    | i, left => loop g i
    | i, right => loop (g * g') i
  }

\func K1-connected (G : Group) : isConnected (K1 G)
  => {?}
    
\func grp-to-ptconn (G : Group) : \Sigma (X : Pointed) (isConnected X) => (\new Pointed (K1 G) { | base => base}, K1-connected G)
{%endarend%}

**Exercise 4:** Prove that {%ard%}K1 G{%endard%} is connected.
{: .notice--info}

Note that {%ard%}relation g g'{%endard%} fills the square with {%ard%}path (loop g){%endard%} (top), {%ard%}path (loop g'){%endard%} (right),
{%ard%}path (loop (g * g')){%endard%} (bottom) and {%ard%}idp{%endard%} (left). Therefore {%ard%}path (loop g) *> path (loop g') = path (loop (g * g')){%endard%}.

The homomorphism, analogous to {%ard%}wind : Int -> base1 = base1{%endard%} for {%ard%}Sphere1{%endard%}, is simply {%ard%}\lam g => path (loop g) : G -> base = base{%endard%}.

The proof that {%ard%}(base = base) = G{%endard%} employs the same ideas as in the proof {%ard%}(base1 = base1) = Int{%endard%} for {%ard%}Sphere1{%endard%}. Namely,
we need to define the universal cover {%ard%}code : K1 G -> \Type{%endard%} and mutually inverse functions {%ard%}encode (x : K1 G) : code x -> base = x{%endard%}
and {%ard%}decode (x : K1 G) : base = x -> code x{%endard%} between the universal cover and the path fibration.

As in the case of {%ard%}Sphere1{%endard%}, the fiber of {%ard%}code{%endard%} over {%ard%}base{%endard%} is {%ard%}G{%endard%} and the 
transport along {%ard%}path (loop g){%endard%} defines the homomorphism {%ard%}\lam g' => g' * g : G -> G{%endard%}. In order to ensure
the latter we need to prove that the right multiplication is an equivalence. We can use the class {%ard%}QEquiv{%endard%} of quasi-equivalences
to store the data: the inverse map {%ard%}* (inverse g){%endard%} and the proofs that the maps {%ard%}* g{%endard%} and {%ard%}* (inverse g){%endard%}
are mutually inverse.

{%arend%}
\func rightMulEquiv {G : Group} (g : G) : QEquiv (`* g) \cowith
  | ret => `* (inverse g) 
  | ret_f h => (*-assoc _ _ _) *> pmap (h *) (inverse-right g) *> ide-right h
  | f_sec h => (*-assoc _ _ _) *> pmap (h * ) (inverse-left g) *> ide-right h
{%endarend%}

We can now define {%ard%}code{%endard%} on {%ard%}base{%endard%} and {%ard%}loop g i{%endard%}:

{%arend%}
\func code {G : Group} (x : K1 G) : \Type \lp \oo \elim x
  | base => G
  | loop g j => Equiv-to-= (rightMulEquiv g) @ j 
             -- 'Equiv-to-=' is essentially 'iso'.
  | relation g g' i j => {?}
{%endarend%}

It remains to define a filling of the square with sides {%ard%}Equiv-to-= (rightMulEquiv g){%endard%} (top), {%ard%}Equiv-to-= (rightMulEquiv g'){%endard%} (right),
{%ard%}Equiv-to-= (rightMulEquiv (g * g')){%endard%} (bottom), {%ard%}idp{%endard%} (left). The function {%ard%}Cube2.map{%endard%} allows to construct
such filling out of a proof that {%ard%}code{%endard%} preserves the relation {%ard%}path (loop g) *> path (loop g') = path (loop (g * g')){%endard%}.

{%arend%}
-- Proof that 'code' preserves the relation on loops.
-- path (\lam i => code (loop g i)) *> path (\lam i => code (loop g' i)) = path (\lam i => code (loop (g * g') i))
\func equivPathComposition {G : Group} (g g' : G)
  : (Equiv-to-= (rightMulEquiv g)) *> (Equiv-to-= (rightMulEquiv g')) = (Equiv-to-= (rightMulEquiv (g * g')))
=> {?}

\func code {G : Group} (x : K1 G) : \Type \lp \oo \elim x
  | base => G
  | loop g j => Equiv-to-= (rightMulEquiv g) @ j 
  | relation g g' i j => Cube2.map (Equiv-to-= (rightMulEquiv g)) (Equiv-to-= (rightMulEquiv (g * g'))) idp (Equiv-to-= (rightMulEquiv g'))
                                   (movePath (equivPathComposition g g')) @ j @ i
  \where {
    \func movePath {A : \Type} {a a' a'' : A} {p : a = a'} {q : a' = a''} {r : a = a''} (h : p *> q = r) : p = r *> inv q
      => (inv (pmap (p *>) (*>_inv q)) *> inv (*>-assoc p q (inv q))) *> pmap (`*> inv q) h
  }
{%endarend%}

The rest of the proof, which includes definitions of {%ard%}encode{%endard%} and {%ard%}decode{%endard%}, is technical and essentially repeats the corresponding
parts of the proof for the circle. It can be found in the Arend standard library.
