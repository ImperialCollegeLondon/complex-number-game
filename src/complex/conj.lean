-- import solutions to level 1
import complex.I

/-! 

# Level 2: Complex conjugation

-/

namespace complex

def conj (z : ℂ) : ℂ := sorry

@[simp] lemma conj_re (z : ℂ) : re(conj z) = re(z) := sorry
@[simp] lemma conj_im (z : ℂ) : im(conj z) = -im(z) := sorry


@[simp] lemma conj_zero : conj 0 = 0 := sorry
@[simp] lemma conj_one : conj 1 = 1 := sorry
@[simp] lemma conj_I : conj I = -I := sorry

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
sorry

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := sorry

@[simp] lemma conj_neg_I : conj (-I) = I := sorry

@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
sorry

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
sorry

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
sorry

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
sorry

lemma conj_involutive : function.involutive conj := sorry

lemma conj_bijective : function.bijective conj := sorry

/-- the ring homomorphism complex conjugation -/
def Conj : ℂ →+* ℂ :=
{ to_fun := conj,
  map_zero' := begin sorry end,
  map_one' := begin sorry end,
  map_add' := begin sorry end,
  map_mul' := begin sorry end
}

end complex

#exit
-- needs coercions
@[simp] lemma conj_of_real (r : ℝ) : conj r = r := sorry

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
sorry

lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
sorry

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
sorry
