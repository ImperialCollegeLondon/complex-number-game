/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- Import levels 1 to 4
import complex.kb_solutions.Level_04_norm_sq

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

@[simp] lemma inv_re (z : ℂ) :
  re(z⁻¹) = re(z)/norm_sq(z) := rfl

@[simp] lemma inv_im (z : ℂ) :
  im(z⁻¹) = -im(z)/norm_sq(z) := rfl

lemma zero_ne_one : (0 : ℂ) ≠ 1 :=
by intro h; simp [ext_iff, *] at *

/-- The complex numbers are a field -/
instance : field ℂ :=
{ inv := has_inv.inv,
  inv_zero := by ext; simp,
  zero_ne_one := zero_ne_one, 
  mul_inv_cancel := begin
    intros z hz,
    rw [←norm_sq_ne_zero, norm_sq] at hz,
    ext; simp;
    field_simp [norm_sq, hz];
    ring,
  end,
  ..complex.comm_ring }



def div (z w : ℂ) : ℂ := z * w⁻¹

instance : has_div ℂ := ⟨complex.div⟩

example : (1 : ℂ) / 0 = 0 :=
begin
  ext;
  simp,
end


end complex
