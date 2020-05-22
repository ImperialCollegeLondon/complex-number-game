/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/
import complex.kb_solutions.of_real -- solutions to levels 1 to 4

noncomputable theory 

namespace complex

-- Define the inverse of a complex number

/-- The inverse of a complex number-/
noncomputable def inv (z : ℂ) : ℂ :=
⟨re(z)/norm_sq(z), -im(z)/norm_sq(z)⟩

instance : has_inv ℂ := ⟨inv⟩

@[simp] lemma inv_re (z : ℂ) :
  re(z⁻¹) = re(z)/norm_sq(z) := rfl

@[simp] lemma inv_im (z : ℂ) :
  im(z⁻¹) = -im(z)/norm_sq(z) := rfl

/-- The complex numbers are a field -/
instance : field ℂ :=
{ inv := has_inv.inv,
  inv_zero := begin ext; simp end,
  zero_ne_one := begin
    intro h,
    rw ext_iff at h,
    cases h with hr hi,
    change (0 : ℝ) = 1 at hr,
    linarith,
  end,
  mul_inv_cancel := begin
    intros z hz,
    -- why is everything in such a weird state?
    change z ≠ 0 at hz,
    change z * z⁻¹ = 1,
    -- that's better
    rw ←norm_sq_pos at hz,
    have h : z.norm_sq ≠ 0,
      linarith,
    -- finally ready
    ext;
    simp [norm_sq] at *;
    field_simp [h];
    ring
  end,
  ..complex.comm_ring }

end complex