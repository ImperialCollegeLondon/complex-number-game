/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- Import levels 1 to 4
import complex.your_solutions.Level_04_norm_sq

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
def inv (z : ℂ) : ℂ := ⟨re(z)/norm_sq(z), -im(z)/norm_sq(z)⟩

-- notation for inverse
instance : has_inv ℂ := ⟨inv⟩

example : ℂ := 1⁻¹

example : ℂ := 0⁻¹ -- we have no data about this object

@[simp] lemma inv_re (z : ℂ) :
  re(z⁻¹)=re(z)/norm_sq(z) := rfl

@[simp] lemma inv_im (z : ℂ) :
  im(z⁻¹)=-im(z)/norm_sq(z) := rfl



/-- The complex numbers are a field -/
instance : field ℂ :=
{ inv := has_inv.inv,
  inv_zero := begin
    ext;
    simp,
  end,
  zero_ne_one := zero_ne_one, 
  mul_inv_cancel := begin
    intro z,
    intro hz,
    rw ←norm_sq_ne_zero at hz,
    ext; simp [norm_sq] at *;
    { field_simp [hz], -- clears denominators
      ring},
  end,
  ..complex.comm_ring }

-- finale
def div (z w : ℂ) : ℂ := z * w⁻¹

-- notation
instance : has_div ℂ := ⟨complex.div⟩

end complex

