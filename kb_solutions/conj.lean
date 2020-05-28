-- import solutions to level 1
import complex.kb_solutions.I

/-! 

# Level 2: Complex conjugation

-/

namespace complex

-- First complete the definition using `complex.mk` or `⟨x, y⟩` notation

/-- The complex conjugate of a complex number -/
def conj (z : ℂ) : ℂ := ⟨re(z), -im(z)⟩

-- Now prove how it interacts with everything else

/-! ## Real and imaginary parts -/

@[simp] lemma conj_re (z : ℂ) : re(conj z) = re(z) := rfl -- short for "begin refl end"
@[simp] lemma conj_im (z : ℂ) : im(conj z) = -im(z) := rfl

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma conj_zero : conj 0 = 0 := by ext; simp -- short for "begin ext; simp end"
@[simp] lemma conj_one : conj 1 = 1 := by ext; simp
@[simp] lemma conj_I : conj I = -I := by ext; simp
@[simp] lemma conj_neg_I : conj (-I) = I := by ext; simp

/-! # Behaviour with respect to +, - and * -/

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
by ext; -- check on real and imag parts 
   simp; -- question becomes to check that a+b=b+a for certain real numbers a and b
   ring -- true because this is obvious in a ring

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z :=
by ext; -- check on real and imag parts 
   refl -- happens to be true by definition


@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
by ext; -- check on real and imag parts 
   simp; -- it's some random statement involving ring theory of the real numbers
   ring -- solve it

/-! # Properties of the `conj` map -/

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
by ext; -- check on real and imag parts 
   simp -- ext had reduced question to -(-x)=x for reals

attribute [simp] ext_iff -- cheeky trick to make the next proof work

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
begin
  simp * at *
end


@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
begin
  simp * at *
end

/-- the ring homomorphism complex conjugation -/
def Conj : ℂ →+* ℂ :=
{ to_fun := conj,
  map_zero' := conj_zero,
  map_one' := conj_one,
  map_add' := conj_add,
  map_mul' := conj_mul,
}

open function

lemma conj_involutive : involutive conj := conj_conj

lemma conj_bijective : bijective conj := conj_involutive.bijective

end complex
