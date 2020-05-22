/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard
Thanks: Imperial College London, leanprover-community
-/
import complex.basic -- tutorial level
/-! 

# Level 1: I 

I find it unbelievable that we have written quite a lot of code about the complex numbers
and we've still never defined i, or j, or I, or $$\sqrt{-1}$$, or whatever it's called. 
Why don't you supply the definition, and make the basic API?

All the proofs below are sorried. You can try them in tactic mode
by replacing `sorry` with `begin end` and then starting to write 
tactics in the `begin end` block.
-/

namespace complex

/-- complex.I is the square root of -1 above the imaginary axis -/
def I : ℂ := sorry

/-

 Easy lemmas, tagged with `simp` so Lean can prove things about `I` by equating
 real and imaginary parts.
 
-/

/-- re(I) = 0 -/
@[simp] lemma I_re : re(I) = 0 :=
begin
  sorry
end

/-- im(I) = 1 -/
@[simp] lemma I_im : im(I) = 1 :=
begin
  sorry
end

/-- I*I = -1 -/
@[simp] lemma I_mul_I : I * I = -1 :=
begin
  sorry
end

/-
  Bonus level. Hint: don't forget ext_iff. It's defined
  in complex.basic and its type is below.
   
  ext_iff : ∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
-/
/-- I is non-zero -/
lemma I_ne_zero : (I : ℂ) ≠ 0 :=
begin
  sorry
end

end complex
