/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- Import levels 1 to 3
import complex.kb_solutions.Level_03_conj

/-! 

# Level 4: Norms

Define `norm_sq : ℂ → ℝ` by defining `norm_sq(z)` to be
`re(z)*re(z)+im(z)*im(z)` and see what you can prove about it.

-/

namespace complex

/-- The real number which is the squared norm of z -/
def norm_sq (z : ℂ) : ℝ := re(z)*re(z)+im(z)*im(z)

local attribute [simp] ext_iff

-- next few proofs are are all mostl simp [norm_sq] so let's locally
-- tell simp about it for this section only

section simp_knows_norm_sq

local attribute [simp] norm_sq
/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := by simp

@[simp] lemma norm_sq_one : norm_sq 1 = 1 := by simp
@[simp] lemma norm_sq_I : norm_sq I = 1 := by simp

/-! ## Behaviour with respect to *, + and - -/

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
by simp; ring

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
by simp; ring

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
by simp

/-! ## Behaviour with respect to `conj` -/

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
by simp

/-! ## Behaviour with respect to real numbers` -/

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
by simp

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
by simp; ring

-- time to end the section; simp no longer knows about norm_sq

end simp_knows_norm_sq

/-! ## Behaviour with respect to real 0, ≤, < and so on -/

-- Warning: you will have to know something about Lean's API for
-- real numbers to solve these ones. If you turn the statements about
-- complex numbers into statements about real numbers, you'll find
-- they're of the form "prove $$x^2+y^2\geq0$$" with `x` and `y` real.

example (y : ℝ) : 0 ≤ y * y := mul_self_nonneg y

namespace realtac

lemma norm_nonneg (x y : ℝ) : 0 ≤ x * x + y * y :=
begin
  nlinarith,
end

lemma norm_eq_zero_iff {x y : ℝ} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 :=
begin
  split,
  { intro h,
    rw add_eq_zero_iff' at h,
    { simp * at *},
    { apply mul_self_nonneg},
    { apply mul_self_nonneg}},
  { rintros ⟨rfl, rfl⟩,
    simp,
  }
end

lemma norm_nonpos_right {x y : ℝ} (h1 : x * x + y * y ≤ 0) : y = 0 :=
begin
  suffices : x = 0 ∧ y = 0,
    simp [this],
  rw ←norm_eq_zero_iff,
  linarith [norm_nonneg x y],
end

lemma norm_nonpos_left (x y : ℝ) (h1 : x * x + y * y ≤ 0) : x = 0 :=
begin
  rw add_comm at h1,
  apply norm_nonpos_right h1,
end

end realtac

-- back to the levels


lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z :=
begin
  cases z with x y,
  simp [norm_sq],
  apply realtac.norm_nonneg,
end

@[simp] lemma norm_sq_eq_zero (z : ℂ) : norm_sq z = 0 ↔ z = 0 :=
begin
  cases z with x y,
  simp [norm_sq],
  exact realtac.norm_eq_zero_iff
end

@[simp] lemma norm_sq_ne_zero {z : ℂ} : norm_sq z ≠ 0 ↔ z ≠ 0 :=
begin
  have h := norm_sq_eq_zero z,
  tauto!
end

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
begin
  rw lt_iff_le_and_ne, 
  rw ne_comm,
  simp [norm_sq_nonneg],
end

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
begin
  simp [norm_sq],
  apply mul_self_nonneg,
end

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
begin
  simp [norm_sq],
  apply mul_self_nonneg
end


end complex
