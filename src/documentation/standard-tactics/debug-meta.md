---
title: \module Debug.Meta
---

This module defines some debugging helper metas.

# `time`

Returns current time in milliseconds, as an integer literal.

Examples:

{% arend %}
\func currentTime : Nat => time
\func currentTimeInt : Int => time
{% endarend %}

# `random`

Returns a random number as an integer literal.
It can take some arguments which specifies the returned random number.

Examples:

{% arend %}
random -- returns a random number.

random n -- returns a random number between 0 and `n`

random (l,u) -- returns a random number between `l` and `u`
{% endarend %}

# `println`

Prints the argument to the console.
In the IDE, it will open a tool window and display the argument.

Examples:

{% arend %}
\import Debug.Meta
\import Meta (run)

-- A defined meta
\meta runTimed m => run {
  -- Record the start time
  \let startTime => time,
  -- Type check the input and print it
  println m,
  -- Calculate the elapsed time and print it
  println (time Nat.- startTime)
}

-- Usage
\func test => runTimed (114 Nat.+ 514)
{% endarend %}
