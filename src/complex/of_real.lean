/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/
import complex.norm_sq -- solutions to levels 1 to 3

/-! # Level 4 : Coercion 

This file sets up the coercion from the reals to the complexes, sending `r` to `⟨r, 0⟩`.
Mathematically it is relatively straightforward.

-/

namespace complex

-- fill in the definition of the map below,
-- sending the real number r to the complex number ⟨r, 0⟩

/-- The canonical map from ℝ to ℂ. -/
def of_real (r : ℝ) : ℂ := sorry

/-
We make this map into a *coercion*, which means that if `(r : ℝ)` is a real
number, then `(r : ℂ)` or `(↑r : ℂ)` will indicate the corresponding
complex number with no imaginary part. This is the notation we shall
use in our `simp` lemmas.
-/

/-- The coercion from ℝ to ℂ sending `r` to the complex number `⟨r, 0⟩` -/
instance : has_coe ℝ ℂ := ⟨of_real⟩

/-
As usual, we need to train the `simp` tactic. But we also need to train
the `norm_cast` tactic. The `norm_cast` tactic enables Lean to prove
results like r^2=2*s for reals `r` and `s`, if it knows that `(r : ℂ)^2 = 2*(s : ℂ)`.
-/

@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r := sorry
@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := sorry

-- The map from the reals to the complexes is injective, something we
-- write in iff form so `simp` can use it; `simp` also works on `iff` goals.

@[simp, norm_cast] theorem of_real_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w := sorry

/-
We now go through all our basic constants and constructions, namely 0, 1, +, *, I, conj and norm_sq,
and tell the simplifier how they behave with respect to this new function. 
-/

/-! ## zero -/

@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := sorry

@[simp] theorem of_real_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 := sorry

theorem of_real_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 := sorry

/-! ## one -/

@[simp, norm_cast] lemma of_real_one : ((1 : ℝ) : ℂ) = 1 := sorry

/-! ## add -/

@[simp, norm_cast] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
begin
  sorry
end

/-! ## neg -/

@[simp, norm_cast] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
begin
  sorry
end

/-! ## mul -/

@[simp, norm_cast] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
begin
  sorry
end

/-! ## I -/

lemma mk_eq_add_mul_I (a b : ℝ) : complex.mk a b = a + b * I := sorry

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z := sorry


/-! ## conj -/

@[simp] lemma conj_of_real (r : ℝ) : conj r = r := sorry

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
sorry

lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
sorry

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
sorry

/-! ## norm_sq -/

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
sorry

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
sorry

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

@[simp, norm_cast] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r := sorry
@[simp, norm_cast] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r := sorry

end complex
