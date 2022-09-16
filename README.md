# The Complex Number Game

The Complex Number Game. Make an interface for the complex numbers in Lean.

# Online play

Whilst installing Lean and this project locally is the recommended way to play the game, if you have an account at Github you can play online with Gitpod (wait a minute or two for everything to download and set up) here: [![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/ImperialCollegeLondon/complex-number-game). When everything's finished downloading, open up the `src` directory on the left and then choose a level to play. Start with `Level_00_basic.lean` (a walkthrough of a proof that the complex numbers are a ring) and then move on to `Level_01_of_real.lean` (the definition of the map from the reals to the complexes). See the [instructions](INSTRUCTIONS.md) for more information.

# Installation

This assumes you have [installed Lean using the instructions at the leanprover-community website](https://leanprover-community.github.io/get_started.html).

All you have to do is type

```
leanproject get ImperialCollegeLondon/complex-number-game
```

into the terminal you used when installing Lean. This will get the fully compiled Lean project onto your computer.

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
  the `leanproject` command up and running. Lean projects are now really easy to install,
  once you have everything set up.

* Scott Morrison, for explaining that I had missed an opportunity to teach `simp`
  in the natural number game. My excuse: I didn't understand it at the time!
  I hope you like this one better.

