/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/
import complex.of_real -- solutions to levels 1 to 4

/-! # Level 5 : the complex numbers are a field -/

namespace complex

-- Define the inverse of a complex number

/-- The inverse of a complex number-/
def inv (z : ℂ) : ℂ := sorry

-- Note that you should ensure that the inverse of 0 to be 0.

/-- The complex numbers are a field -/
instance : field ℂ :=
{ inv := inv,
  inv_zero := sorry,
  zero_ne_one := sorry,
  mul_inv_cancel := begin sorry end,
  ..complex.comm_ring }

end complex