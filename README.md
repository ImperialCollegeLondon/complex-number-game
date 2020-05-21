# The Complex Number Game

The Complex Number Game. Make an interface for the complex numbers in Lean.

# Installation

This assumes you have [installed Lean and the python package `mathlibtools`](https://leanprover-community.github.io/get_started.html).

All you have to do is type

```
leanproject get ImperialCollegeLondon/complex-number-game
```

into the terminal you used to install `mathlibtools`. This will get the fully compiled Lean project onto your computer.

You can open the project using the terminal with

```
cd complex-number-game
code .
```

(or you can use VS Code and then "Open Folder" -> `complex-number-game`)

# Playing the game

The general idea: we can assume anything about the real numbers, and have to build the complex numbers from the ground up.
Once the project is installed on your computer, see the [instructions](INSTRUCTIONS.md) for how to play it.

# Thanks

* Everyone on the Zulip chat at leanprover-community, for answering my
questions. You are now too many to mention.

* Patrick Massot, and all the other people who have been involved in getting
  the `leanproject` command up and running. If you're using linux, Lean
  projects are now really easy to install.

* Scott Morrison, for explaining that I had missed an opportunity to teach `simp`
  in the natural number game. My excuse: I didn't understand it at the time!
  I hope you like this one better.

