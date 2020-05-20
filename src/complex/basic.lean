/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, anyone else who wants to join in.
Thanks: Imperial College London, leanprover-community

The complex numbers, modelled as R^2 in the obvious way.
-/
--*TODO* sort out Licence. Make private GH repo.

-- We will assume that the real numbers are a field.
import data.real.basic

/-!
# The complex numbers

We define the complex numbers, and prove that they are a ring.
We then might do other stuff

# main definitions:

zero
one
add
mul

# main theorem

comm_ring ℂ
-/

/-
The complex numbers.
A documented remix of part of mathlib

Our goal is to define the complex numbers, and then "extract some API".
Our first goal is to define addition and multiplication,
and prove that the complex numbers are a commutative ring.
We then do a slightly more computer-sciency worked development of the
natural inclusion from the reals to the complexes. 

There are then a bunch of exercises, which can be solved in term mode
or tactic mode. . 
a lot of stuff we don't need for this one precise result. As an appendix
We leave as exercises
the API extraction for the stuff we skipped, namely the following
complex conjugation and the norm function.
-/
