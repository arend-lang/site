---
title: \module Meta
---

# Scope metas

Meta `using`, `usingOnly` and `hiding` controls the scope.

+ `using (e_1, ... e_n) e` adds `e_1`, ... `e_n` to the context before checking `e`.
  `using (e_1, ... e_n)` is sometimes used in other context-manipulating metas,
  that adds `e_1`, ... `e_n` to the context it uses.
+ `usingOnly (e_1, ... e_n) e` replaces the context with `e_1`, ... `e_n` before checking `e`.
  `usingOnly (e_1, ... e_n)` is sometimes used in other context-manipulating metas,
  that replaces the context is uses with `e_1`, ... `e_n`.
+ `hiding (e_1, ... e_n) e` hides local bindings `e_1`, ... `e_n` from the context before checking `e`.
  `hiding (e_1, ... e_n)` is sometimes used in other context-manipulating metas,
  that hides `e_1`, ... `e_n` from the context it uses.
