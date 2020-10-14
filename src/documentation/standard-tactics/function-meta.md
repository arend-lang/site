---
title: \module Function.Meta
---

# `$` and `#`

These metas are analogical to Haskell's `$` operator
(`$` is right-associative and `#` is left-associative), but they also work with implicit arguments.

 [defined meta]: (/documentation/language-reference/definitions/metas)

Also, it's also possible to define `$` as a [defined meta]:

{% arend %}
\meta \infixr 0 $ f a => f a
{% endarend %}

But then it won't work with implicit arguments.
In Haskell, you can apply `$` partially (like `$ a`), and you can do this in Arend via implicit lambdas ( {%ard%} __ $ a {%endard%}).

# `repeat`
