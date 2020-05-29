/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard
Thanks: Imperial College London, leanprover-community
-/

-- import levels 1 and 2
import complex.Level_02_I

/-! # Level 3: Complex conjugation -/

namespace complex

-- First complete the definition using `complex.mk` or `⟨x, y⟩` notation

/-- The complex conjugate of a complex number -/
def conj (z : ℂ) : ℂ := ⟨re(z), -im(z)⟩

-- Now prove how it interacts with everything else

/-! ## Real and imaginary parts -/

@[simp] lemma conj_re (z : ℂ) : re(conj z) = re(z) := rfl
@[simp] lemma conj_im (z : ℂ) : im(conj z) = -im(z) := rfl

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma conj_zero : conj 0 = 0 := by ext; simp


@[simp] lemma conj_one : conj 1 = 1 := by ext; simp
@[simp] lemma conj_I : conj I = -I := by ext; simp
@[simp] lemma conj_neg_I : conj (-I) = I := by ext; simp

/-! ## Behaviour with respect to +, - and * -/

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
by ext; simp [add_comm]


--by ext; simp -- doesn't work!
-- why does the simplifier not know add_comm?

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := by ext; simp


@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
by ext; simp; ring

/-! ## Behaviour with respect to real numbers -/

@[simp] lemma conj_of_real (r : ℝ) : conj r = r := by ext; simp

lemma im_eq_zero_of_eq_conj {z : ℂ} : conj z = z → im z = 0 :=
begin
  intro h,
  simp [ext_iff] at h,
  linarith
end

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
begin
  split,
  { intro h,
    use re(z),
    have h2 := im_eq_zero_of_eq_conj h,
    ext; simp * at *},
  { rintro ⟨r, hr⟩,
    simp [ext_iff, *] at *
  }
end


lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
begin
  simp [ext_iff],
  split; intros; linarith
end

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
begin
  simp [ext_iff],
  split,
  { show re(z)+re(z)=2*re(z),
    ring,
  },
  left,
  simp [bit0],
end


/-! ## Properties of the `conj` map -/

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
by simp [ext_iff]

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
by simp [ext_iff]

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
by simp [ext_iff]

/-

A ring homomorphism in Lean is the following collection
of data: a map, and the proof that it commutes with
the ring structures in the obvious way. Here we observe
that the work we've done is enough to define the
ring homomorphism complex conjugation.

-/

/-- the ring homomorphism complex conjugation -/
def Conj : ℂ →+* ℂ :=
{ to_fun := conj,
  map_zero' := conj_zero,
  map_one' := conj_one,
  map_add' := conj_add,
  map_mul' := conj_mul
}

-- Two optional lemmas which computer scientists like,
-- giving us easy access to some basic properties
-- of conj

open function

lemma conj_involutive : involutive conj :=
begin
--  unfold involutive,
  intro z,
  simp,
end

lemma conj_bijective : bijective conj :=
begin
  apply involutive.bijective,
  exact conj_involutive
end

end complex
