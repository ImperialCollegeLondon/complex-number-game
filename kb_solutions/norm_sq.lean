import complex.kb_solutions.conj -- solutions to exercise 2
/-! 

# Exercise 3: Norms

Define `norm_sq : ℂ → ℝ` by defining `norm_sq(z)` to be `re(z)*re(z)+im(z)*im(z)` and see
what you can prove about it.

-/

namespace complex

/-- The real number which is the squared norm of z -/
def norm_sq (z : ℂ) : ℝ := re(z)*re(z)+im(z)*im(z)

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 :=
by simp [norm_sq]

@[simp] lemma norm_sq_one : norm_sq 1 = 1 :=
by simp [norm_sq]

@[simp] lemma norm_sq_I : norm_sq I = 1 :=
by simp [norm_sq]

/-! ## Behaviour with respect to *, + and - -/

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
begin
  simp [norm_sq],
  ring,
end

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
begin
  simp [norm_sq],
  ring,
end

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
begin
  simp [norm_sq],
end

/-! ## Behaviour with respect to `conj` -/

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
begin
  simp [norm_sq],
end

/-! ## Behaviour with respect to real 0, ≤, < and so on -/

end complex

-- Computer scientists tell me some theory of the reals is complete
-- So why so I have to prove these by hand?

lemma real_tac1 (x y : ℝ) : 0 ≤ x * x + y * y :=
begin
  apply add_nonneg;
  apply mul_self_nonneg,
end

lemma real_tac2 (x y : ℝ) : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 :=
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

lemma real_tac3 {x y : ℝ} (h1 : x * x + y * y ≤ 0) : y = 0 :=
begin
  suffices : x = 0 ∧ y = 0,
    simp [this],
  rw ←real_tac2,
  apply le_antisymm h1,
  apply real_tac1,
end

lemma real_tac4 (x y : ℝ) (h1 : x * x + y * y ≤ 0) : x = 0 :=
begin
  rw add_comm at h1,
  apply real_tac3 h1,
end

lemma real_tac5 (y : ℝ) : 0 ≤ y * y := mul_self_nonneg y

namespace complex
-- Introducing 
lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z :=
begin
  simp [norm_sq],
  -- (x y : ℝ) ⊢ 0 ≤ x * x + y * y
  apply real_tac1,
end

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
begin
  cases z with x y,
  simp [norm_sq],
  apply real_tac2,
end

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
begin
  -- this is a bit thorny
  split,
  { intro h,
    rintro rfl,
    simp [norm_sq] at *,
    linarith,
  },
  { intro h,
    rw ←not_le,
    intro h2, -- I am so bad at Lean
    simp [norm_sq] at *,
    by_cases hre : z.re = 0,
    { apply h hre,
      cases z with x y,  
      dsimp at *, 
      apply real_tac3 h2,
    },
    { 
      apply hre,
      cases z with x y,
      dsimp at *,
      apply real_tac4 x y h2,
    }
  }
end

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
begin
  cases z with x y,
  simp [norm_sq],
  apply real_tac5,
end


lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
begin
  cases z with x y,
  simp [norm_sq],
  apply real_tac5,
end

end complex
