
import complex.conj -- solutions to exercise 2
/-! 

# Exercise 3: Norms

-/

namespace complex

def norm_sq (z : ℂ) : ℝ := z.re * z.re + z.im * z.im

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := sorry
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := sorry
@[simp] lemma norm_sq_I : norm_sq I = 1 := sorry

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z := sorry

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
sorry

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
sorry

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
sorry

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
sorry

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
sorry

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
sorry

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
sorry

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
sorry

end complex

#exit

-- needs coercions
@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
sorry

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
sorry
