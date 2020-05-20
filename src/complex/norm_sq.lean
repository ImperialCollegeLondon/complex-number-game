
import complex.conj -- solutions to exercise 2
/-! 

# Exercise 3: Norms

Define `norm_sq(z)` to be `re(z)*re(z)+im(z)*im(z)` and see
what you can prove.

-/

namespace complex

/-- The real number which is the squared norm of z -/
def norm_sq (z : ℂ) : ℝ := sorry

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := sorry
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := sorry
@[simp] lemma norm_sq_I : norm_sq I = 1 := sorry

/-! ## Behaviour with respect to *, + and - -/

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
sorry

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
sorry

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
sorry

/-! ## Behaviour with respect to `conj` -/

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
sorry

/-! ## Behaviour with respect to real 0, ≤, < and so on -/

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z := sorry

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
sorry

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
sorry

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
sorry

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
sorry

end complex
