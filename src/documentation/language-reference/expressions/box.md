---
title: Box
toc: false
---

If {%ard%} A {%endard%} is a proposition and {%ard%} a : A {%endard%}, then {%ard%} \box a : A {%endard%} is an element that does not evaluate to anything,
but which is judgmentally equal to any other boxed element. This includes all expressions of the form {%ard%} \box b {%endard%} and also all lemma calls.

If the type of a parameter of a definition is a proposition, this parameter can be marked with {%ard%} \property {%endard%} keyword.
Then the corresponding argument will be automatically surrounded in {%ard%} \box {%endard%} for every call of this definition.
