import complex.kb_solutions.norm_sq

/-! # Coercion 

This file sets up the coercion from the reals to the complexes, sending `r` to `⟨r, 0⟩`.
Mathematically it is relatively straightforward.

-/

namespace complex

/-- The canonical map from ℝ to ℂ. -/
def of_real (r : ℝ) : ℂ := ⟨r, 0⟩

/-- The coercion from ℝ to ℂ sending `r` to the complex number `⟨r, 0⟩` -/
instance : has_coe ℝ ℂ := ⟨of_real⟩

@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r := rfl
@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl

@[simp, norm_cast] theorem of_real_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
begin
  split,
  { rintro ⟨⟩,
    refl},
  { cc}
end

/-
We now go through all our basic constants and constructions, namely 0, 1, +, *, I, conj and norm_sq,
and tell the simplifier how they behave with respect to this new function. 
-/

/-! ## zero -/

@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 :=
by ext; refl

@[simp] theorem of_real_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 :=
begin
  split,
  { intro h,
    simpa using h,
  },
  { rintro rfl,
    refl}
end

theorem of_real_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 :=
begin
  simp,
end

/-! ## one -/

@[simp, norm_cast] lemma of_real_one : ((1 : ℝ) : ℂ) = 1 :=
begin
  refl,
end

/-! ## add -/

@[simp, norm_cast] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
begin
  ext;
  simp
end

/-! ## neg -/

@[simp, norm_cast] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
begin
  simp,
end

/-! ## mul -/

@[simp, norm_cast] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
begin
  simp,
end

/-! ## I -/

lemma mk_eq_add_mul_I (a b : ℝ) : complex.mk a b = a + b * I :=
begin
  ext;
  simp
end

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
begin
  ext;
  simp,
end

/-! ## conj -/

@[simp] lemma conj_of_real (r : ℝ) : conj r = r :=
begin
  simp,
end

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
begin
  -- not my finest hour
  split,
  { intro h,
    simp at h,
    use z.re,
    ext,
    { refl},
    simp,
    linarith},
  { cases z with x y,
    rintro ⟨x, hx⟩,
    ext, refl,
    dsimp at *,
    rw ext_iff at hx,
    simp * at *
  }
end

lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
begin
  cases z with x y,
  -- `simp` doesn't quite work, so just prove the goal it leaves independently.
  have h : -y = y ↔ 0 = y,
  { split; intros; linarith},
  -- Makes for more readable and maintainable code.
  simp [h],
end

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
begin
  cases z with x y,
  simp,
  ring,
end

/-! ## norm_sq -/

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
begin
  simp [norm_sq],
end

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
begin
  cases z with x y,
  simp [norm_sq],
  ring,
end

/-! ## Appendix: numerals.

If you're not a computer scientist feel free to skip this bit. 

These last two are to do with the canonical map from numerals into the complexes, e.g. `(23 : ℂ)`.
Lean stores the numeral in binary. See for example

set_option pp.numerals false
#check (37 : ℂ)-- bit1 (bit0 (bit1 (bit0 (bit0 has_one.one)))) : ℂ

`bit0 x` is defined to be `x + x`, and `bit1 x` is defined to be `bit0 x + 1`.

We need these results so that `norm_cast` can prove results such as (↑(37 : ℝ) : ℂ) = 37 : ℂ
(i.e. coercion commutes with numerals)

-/

@[simp, norm_cast] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r :=
begin
  ext;
  simp [bit0]
end

@[simp, norm_cast] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r :=
begin
  ext;
  simp [bit1],
end

end complex
