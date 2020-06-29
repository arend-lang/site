---
title: Definitions
---

Arend supports the following kinds of definitions: [functions](functions), [data](data), [records](records), [classes](classes), [instances](classes#instances), and [coercions](coercion).
Every definition has a name which must be a valid identifier as described in [Lexical structure](../lexical-structure#identifiers).

Definitions can be referred by _defcall_ expressions.
If {%ard%} def {%endard%} is a name of a definition, defcall is an expression of the form:
{%ard%} def e_1 ... e_n {%endard%}, where {%ard%} e_1, ..., e_n {%endard%} are expressions.
Expressions {%ard%} e_1, ..., e_n {%endard%} are called arguments of the defcall.

There are alternative notations in case a defcall has precisely one or two arguments.
In case of two arguments, it is possible to use the infix notation: {%ard%} def e_1 e_2 {%endard%} is equivalent
to {%ard%} e_1 \`def\` e_2 {%endard%}.
In case of one argument, it is possible to use the postfix notation: {%ard%} def e_1 {%endard%} is equivalent to {%ard%} e_1 \`def {%endard%}.

## Precedence

The parsing of complex defcall expressions, containing several infix and postfix notations, is regulated by precedence
of involved definitions: their priority and the type of associativity. Precedence of a definition can be specified
by writing {%ard%} FIX N {%endard%} just before the name of the definition, where {%ard%} FIX {%endard%} is one of keywords
{%ard%} \fixl {%endard%}, {%ard%} \fixr {%endard%} or {%ard%} \fix {%endard%},
which mark the definition as left, right associative or non-associative respectively, and {%ard%} N {%endard%} is the priority, 
which is an integer between 1 and 9. For example, {%ard%} \func \fixl 3 op (a b : Nat) => 0 {%endard%} defines a binary function
named {%ard%} op {%endard%} which is left associative with priority 3. The default precedence is {%ard%} \fixr 10 {%endard%}. 

If {%ard%} op1 {%endard%} and {%ard%} op2 {%endard%} are two definitions and {%ard%} e1, e2, e3 {%endard%} are expressions,
the expression {%ard%} e1 \`op1\` e2 \`op2\` e3 {%endard%} is parsed according to the following rules:

* If priorities of {%ard%} op1 {%endard%} and {%ard%} op2 {%endard%} are different and, say, the priority of {%ard%} op1 {%endard%} is higher, then the expression is parsed as {%ard%} (e1 \`op1\` e2) \`op2\` e3 {%endard%}.
* Assume priorities of {%ard%} op1 {%endard%} and {%ard%} op2 {%endard%} are the same. If they are both left or both right associative, the expression is
  parsed as {%ard%} (e1 \`op1\` e2) \`op2\` e3 {%endard%} or {%ard%} e1 \`op1\` (e2 \`op2\` e3) {%endard%} respectively. If {%ard%} op1 {%endard%} and {%ard%} op2 {%endard%} have
  different types of associativity or are non-associative, then the parsing error is generated.

## Infix operators

A definition can be labeled as an _infix operator_.
This means that its defcalls are parsed as infix notations even without `` ` ` ``.
An infix operator is defined by specifying one of keywords {%ard%} \infixl {%endard%}, {%ard%} \infixr {%endard%}, {%ard%} \infix {%endard%} before the name of operator.
These keywords have the same syntax and semantics as keywords {%ard%} \fixl {%endard%}, {%ard%} \fixr {%endard%}, and {%ard%} \fix {%endard%}, which are described above.

An infix operator can be used in the prefix form as an ordinary definition.
For example, if the function {%ard%} + {%endard%} is defined as {%ard%} \infixl 6 + {%endard%}, then it is allowed to write either {%ard%} + 1 2 {%endard%} or {%ard%} 1 + 2 {%endard%}; 
these expressions are equivalent.

Finally, if {%ard%} f {%endard%} is an infix operator or an operator surrounded with `` ` ` ``, then it is allowed to write {%ard%} e f {%endard%} and
this is equivalent to {%ard%} f e {%endard%}.
For example, the function that adds {%ard%} 1 {%endard%} to its argument can be written either as {%ard%} 1 + {%endard%} or as {%ard%} + 1 {%endard%}.
The result of application of the first function to {%ard%} 2 {%endard%} is {%ard%} 1 + 2 {%endard%}, the result of application of the second one to {%ard%} 2 {%endard%}
is {%ard%} + 1 2 {%endard%}, and as noted before these expressions are equivalent.

As noted above, it is possible to use a left section of an operator, that is {%ard%} x + {%endard%} is equivalent to {%ard%} \lam y => x + y {%endard%}.
It is also possible to use right sections:
if a postfix notation is applied to an argument from the right as in {%ard%} `+ y {%endard%}, then such an expression is equivalent to {%ard%} \lam x => x + y {%endard%}.

## Aliases

An alias is an alternative name for the definition.
It can be specified by putting {%ard%} \alias aliasName {%endard%} after the name of a definition.
The definition itself and its alias can be used interchangeably.
Aliases can have their own precedence which is specified before the alias name.
Aliases can also contain unicode symbols between `U+2200` and `U+22FF`.
