/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/
import complex.of_real -- solutions to levels 1 to 4

-- If you know what "the reals don't have decidable
-- equality" means then you know why the next line
-- is there, and if you don't then you probably don't care.
noncomputable theory

/-! # Level 5 : the complex numbers are a field -/

namespace complex

/-- The inverse of a complex number-/
def inv (z : ℂ) : ℂ := sorry

instance : has_inv ℂ := ⟨inv⟩

@[simp] lemma inv_re (z : ℂ) : re(z⁻¹) = re(z)/norm_sq(z) := sorry
@[simp] lemma inv_im (z : ℂ) : im(z⁻¹) = -im(z)/norm_sq(z) := sorry

-- click on a `sorry` to see what you have to prove

/-- The complex numbers are a field -/
instance : field ℂ :=
{ inv := inv,
  inv_zero := begin sorry end,
  zero_ne_one := begin sorry end, 
  mul_inv_cancel := begin sorry end,
  ..complex.comm_ring }

end complex