-- import solutions to level 1
import complex.I

/-! 

# Level 2: Complex conjugation

-/

namespace complex

-- First complete the definition using `complex.mk` or `⟨x, y⟩` notation

/-- The complex conjugate of a complex number -/
def conj (z : ℂ) : ℂ := sorry

-- Now prove how it interacts with everything else

/-! ## Real and imaginary parts -/

@[simp] lemma conj_re (z : ℂ) : re(conj z) = re(z) := sorry
@[simp] lemma conj_im (z : ℂ) : im(conj z) = -im(z) := sorry

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma conj_zero : conj 0 = 0 := sorry
@[simp] lemma conj_one : conj 1 = 1 := sorry
@[simp] lemma conj_I : conj I = -I := sorry
@[simp] lemma conj_neg_I : conj (-I) = I := sorry

/-! # Behaviour with respect to +, - and * -/

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
sorry

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := sorry


@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
sorry

/-! # Properties of the `conj` map -/

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
sorry

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
sorry

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
sorry

/-- the ring homomorphism complex conjugation -/
def Conj : ℂ →+* ℂ :=
{ to_fun := conj,
  map_zero' := begin sorry end,
  map_one' := begin sorry end,
  map_add' := begin sorry end,
  map_mul' := begin sorry end
}

-- Some optional lemmas which computer scientists like.
-- If you can work out what they say, you can probably prove them

lemma conj_involutive : function.involutive conj := sorry

lemma conj_bijective : function.bijective conj := sorry

end complex
