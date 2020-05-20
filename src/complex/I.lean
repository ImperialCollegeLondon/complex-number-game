/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard
Thanks: Imperial College London, leanprover-community

The complex numbers, modelled as R^2 in the obvious way.
-/
import complex.basic -- tutorial level
/-! 

# Exercise 1: I 

I find it unbelievable that we have written quite a lot of code about the complex numbers
and we've still never defined i, or j, or I, or $$\sqrt{-1}$$, or whatever it's called. 
Why don't you supply the definition, and make the basic API?

All the proofs below are sorried. You can try them in tactic mode
by replacing `sorry` with `begin end` and then starting to write 
tactics in the `begin end` block.
-/

/-- complex.I is the square root of -1 above the imaginary axis -/
def I : ℂ := sorry

/-

 Easy lemmas, tagged with `simp` so Lean can prove things about `I` by equating
 real and imaginary parts.
 
  -/
@[simp] lemma I_re : I.re = 0 := sorry
@[simp] lemma I_im : I.im = 1 := sorry

@[simp] lemma I_mul_I : I * I = -1 := sorry





#exit
-- to be moved: need coercions

lemma mk_eq_add_mul_I (a b : ℝ) : complex.mk a b = a + b * I := sorry

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z := sorry

-- I haven't given enough information to solve this
lemma I_ne_zero : (I : ℂ) ≠ 0 := sorry