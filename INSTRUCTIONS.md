Open the project in VS Code. All the levels are in the `src` directory.

# The tutorial level

Level 0: The tutorial level, is at `src/complex/Level_00_basic.lean`. All solutions are given. Read through this code first, and refer back to it if necessary. 

In the tutorial level we define `0`, `1`, `+`, `-` and `*`, and prove that the complex numbers are a ring.

Note: you can play the tutorial level if you are online, even if you haven't installed Lean, because you can play in the Lean Web Editor. Click [here](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fcomplex-number-game%2Fmaster%2Fsrc%2Fcomplex%2FLevel_00_basic.lean) to interact with the tutorial level. Note that to play the main levels, you will have to install Lean. 

# The main levels

Anyone who has played Majora's Mask knows that all good games have 4 levels.

People who know some basic Lean tactics should be able to have a go at these. Open the relevant project files in VS Code and fill in all the `sorry`s.

* Level 1: the natural map from the reals to the complexes, is at `src/complex/Level_01_of_real.lean`

* Level 2: sqrt(-1), is at `src/complex/Level_02_I.lean`

* Level 3: Complex conjugation, is at `src/complex/Level_03_conj.lean`

* Level 4: the complex norm (squared), is at `src/complex/Level_04_norm_sq.lean`

# Challenges

These are harder, and I give fewer hints.

* Level 5: the complex numbers are a field, is at `src/complex/Level_05_field.lean` . Note that this is not too bad really, and the answers are up on the Xena youtube channel.

* Level 6: the complex numbers are an algebraically closed field, is at `src/complex/alg_closed.lean`

This is hard. Chris Hughes did it, and [put it in mathlib](https://leanprover-community.github.io/mathlib_docs/analysis/complex/polynomial.html#complex.exists_root).
