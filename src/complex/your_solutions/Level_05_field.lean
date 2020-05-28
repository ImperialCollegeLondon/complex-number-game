/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- Import levels 1 to 4
import complex.Level_04_norm_sq

/-
If you know what "the reals don't have decidable
equality" means then you know why the next line
is there, and if you don't then you probably don't care.
-/

noncomputable theory

/-! # Level 5 : the complex numbers are a field -/

namespace complex

/-

Before we start, it's worth pointing out that a field,
for Lean, is a non-zero commutative ring K equipped
with an inverse map `inv: K → K`, with notation z⁻¹,
satisfying 0⁻¹=0 and if z is non-zero then z*z⁻¹=1.
It's easy to check that this is equivalent to the
usual definition, where 0⁻¹ is simply not defined at all.

-/
/-- The inverse of a complex number-/
def inv (z : ℂ) : ℂ := sorry

-- notation for inverse
instance : has_inv ℂ := ⟨inv⟩

/-- The complex numbers are a field -/
instance : field ℂ :=
{ inv := has_inv.inv,
  inv_zero := begin sorry end,
  zero_ne_one := begin sorry end, 
  mul_inv_cancel := begin sorry end,
  ..complex.comm_ring }

end complex