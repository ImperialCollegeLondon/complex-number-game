/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, anyone else who wants to join in.
Thanks: Imperial College London, leanprover-community

The complex numbers, modelled as R^2 in the obvious way.
-/
--*TODO* sort out Licence. Make private GH repo.

-- We will assume that the real numbers are a field.
import data.real.basic

/-!
# The complex numbers

We define the complex numbers, and prove that they are a ring.
We then might do other stuff

# main definitions:

zero
one
add
mul

# main theorem

comm_ring ℂ
-/

/-
The complex numbers.
A documented remix of part of mathlib

Our goal is to define the complex numbers, and then "extract some API".
Our first goal is to define addition and multiplication,
and prove that the complex numbers are a commutative ring.
We then do a slightly more computer-sciency worked development of the
natural inclusion from the reals to the complexes. 

There are then a bunch of exercises, which can be solved in term mode
or tactic mode. . 
a lot of stuff we don't need for this one precise result. As an appendix
We leave as exercises
the API extraction for the stuff we skipped, namely the following
complex conjugation and the norm function.
-/

/-
The complex numbers.
A documented remix of part of mathlib

Our goal is to define the complex numbers, and then "extract some API".
Our first goal is to define addition and multiplication,
and prove that the complex numbers are a commutative ring.
We then do a slightly more computer-sciency worked development of the
natural inclusion from the reals to the complexes. 

There are then a bunch of exercises, which can be solved in term mode
or tactic mode. . 
a lot of stuff we don't need for this one precise result. As an appendix
We leave as exercises
the API extraction for the stuff we skipped, namely the following
complex conjugation and the norm function.
-/

/-- A complex number is defined to be a structure consisting of two real numbers,
    the real part and the imaginary part of the complex number   . -/
structure complex : Type :=
(re : ℝ) (im : ℝ)

-- Let's use the usual notation for the complex numbers
notation `ℂ` := complex

-- You make the complex number with real part 3 and imaginary part 4 like this:
example : ℂ :=
{ re := 3,
  im := 4 }

-- Or like this:
example : ℂ := complex.mk 3 4

-- or like this:
example : ℂ := ⟨3, 4⟩

-- They all give the same complex number.

-- If you have a complex number, then you can get its real and 
-- imaginary parts with the `complex.re` and `complex.im` functions.

example : ℝ := complex.re(complex.mk 3 4) -- this term is (3 : ℝ)

example : complex.re(complex.mk 3 4) = 3 := rfl -- true by definition.

-- We clearly don't want to be constantly saying `complex.blah` so let's
-- move into the `complex` namespace

namespace complex

-- All our theorems and definitions will now be called complex.something,
-- and we can in general just drop `complex.`

-- For example

example : re(mk 3 4) = 3 := rfl

-- Computer scientists prefer the style `z.re` to `re(z)` for some reason. 

example : (mk 3 4).re = 3 := rfl

example (z : ℂ) : re(z) = z.re := rfl

-- We now prove the basic theorems and make the basic definitions for
-- complex numbers. For example, we will define addition and multiplication on
-- the complex numbers, and prove that it is a commutative ring.

/-! # Mathematical trivialities -/

-- We start with some facts about complex numbers which are so obvious that we do not
-- often explicitly state them. The first is that if z is a complex number, then
-- the complex number with real part re(z) and imaginary part im(z) is equal to z.
-- This is called eta reduction in type theory. Let's work through the
-- simple tactic mode proof.

example : ∀ z : ℂ, complex.mk z.re z.im = z :=
begin
  intro z,
  cases z with x y, 
  -- goal now looks complicated, and contains terms which look
  -- like {re := a, im := b}.re which obviously simplify to a.
  -- The `dsimp` tactic will do some tidying up for us, although
  -- it is not logically necessary. `dsimp` does definitional simplification.
  dsimp,
  -- Now we see the goal can be solved by reflexivity
  refl,
end

-- The proof was "unfold everything, and it's true by definition".
-- This proof does not teach a mathematician anything, so we may as well write
-- it in term mode, because each tactic has a term equivalent.
-- The equation compiler does the `intro` and `cases` steps,
-- and `dsimp` was unnecessary -- the two sides of the equation 
-- were definitionally equal.

-- It's important we give this theorem a name, because we want `simp`
-- to be able to use it. In short, the `simp` tactic tries to solve
-- goals of the form A = B, when `refl` doesn't work (i.e. the goals are
-- not definitionally equal) but when any mathematician would be able
-- to simplify A and B via "obvious" steps such as `0 + x = x` or
-- `⟨z.re, z.im⟩ = z`. These things are sometimes not true by definition,
-- but they should be tagged as being well-known ways to simplify an equality.
-- When building our API for the complex numbers, if we prove a theorem of the
-- form `A = B` where `B` is a bit simpler than `A`, we should probably
-- tag it with the `@[simp]` attribute, so `simp` can use it.

-- Note: `simp` does *not* prove "all simple things". It proves *equalities*.
-- It proves `A = B` when, and only when, it can do it by applying 
-- its "simplification rules", where a simplification rule is simply a proof
-- of a theorem of the form `A = B` and `B` is simpler than `A`.  
@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨x, y⟩ := rfl

-- The second triviality is the assertion that two complex numbers
-- with the same and imaginary parts are equal. Again this is not
-- hard to prove, and mathematicians deem it not worth documenting.

example (z w : ℂ) : z.re = w.re → z.im = w.im → z = w :=
begin
  cases z with zr zi,
  cases w,
  intros, cc,
end

-- This lemma is called extensionality by type theorists.
-- Here is another tactic mode proof. Note that we have moved
-- the z and w to the other side of the colon; this does not
-- change the fully expanded proof term. It shows the power
-- of the `rintros` tactic.

example : ∀ z w : ℂ, z.re = w.re → z.im = w.im → z = w :=
begin
  rintros ⟨zr, zi⟩ ⟨_, _⟩ ⟨rfl⟩ ⟨rfl⟩,
  refl,
end

-- `rintros` does `cases` as many times as you like using this cool `⟨, ⟩` syntax
-- for the case splits. Note that if you do cases on `h : a = b` then, because
-- `=` is notation for `eq`, an inductive type with one constructor `a = a`, 
-- it will just delete `b` and change all `b`s to `a`s. That is one of the
-- things going on in the above proof.

-- Here is the same proof in term mode. Even though it's obvious, we still
-- give it a name, namely `ext`. It's important to prove it, so we can
-- tag it with the `ext` attribute. If we do this, the `ext` tactic can use it.
-- The `ext` tactic applies all theorems of the form "two
-- objects are the same if they are made from the same pieces".

@[ext]
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

-- The theorem `complex.ext` is trivially true to a mathematician.
-- But it is often used: for example it will be used all the time
-- in our proof that the complex numbers are a ring.

-- Note that `ext` is an implication -- if re(z)=re(w) and im(z)=im(w) then z=w.
-- The below variant `ext_iff` is the two-way implication: two complex
-- numbers are equal if and only if they have the same real and imaginary part.
-- Let's first see a tactic mode proof. See how the `ext` tactic is used?
-- After it is applied, we have two goals, both of which are hypotheses.
-- The semicolon means "apply the next tactic to all the goals produced by this one"

example (z w : ℂ) : z = w ↔ z.re = w.re ∧ z.im = w.im :=
begin
  split,
  { intro H,
    simp [H]},
  {
    rintro ⟨hre, him⟩,
    ext; assumption,
  }
end

-- Again this is easy to write in term mode, and no mathematician
-- wants to read the proof anyway.

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
⟨λ H, by simp [H], and.rec ext⟩

/-! # Main course: the complex numbers are a ring. -/

-- Our goal is to prove that the complexes are a ring. Let's
-- define the structure first; the zero, one, addition and multiplication
-- on the complexes. 

/-! ## 0 -/

-- Let's define the zero complex number. Once we have done this we will be
-- able to talk about (0 : ℂ).

/-- notation: `0`, or (0 : ℂ), will mean the complex number with
  real and imaginary part equal to (0 : ℝ). -/
instance : has_zero ℂ := ⟨⟨0, 0⟩⟩

-- Let's prove its basic properties, all of which are true by definition,
-- and then tag them with the appropriate attributes.
@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl

/-! ## 1 -/

-- Now let's do the same thing for 1.

/-- Notation `1` or `(1 : ℂ)`, means `⟨(1 : ℝ), (0 : ℝ)⟩`. -/
instance : has_one ℂ := ⟨⟨1, 0⟩⟩ 

-- name basic properties and tag them appropriately
@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl

/-! ## + -/

-- Now let's define addition

/-- Notation `+` for usual addition of complex numbers-/
instance : has_add ℂ := ⟨λ z w, ⟨z.re + w.re, z.im + w.im⟩⟩

-- and state and tag its basic properties. We want to prove
-- theorems like $$a(b+c)=ab+ac$$ by checking on real and
-- imaginary parts, so we need to teach the simplifier
-- these tricks.

@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl



instance : has_neg ℂ := ⟨λ z, ⟨-z.re, -z.im⟩⟩

@[simp] lemma neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : ℂ) : (-z).im = -z.im := rfl

instance : has_mul ℂ := ⟨λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-! ## Example of what `simp` can now do -/

example (a b c : ℂ) : re(a*(b+c)) = re(a) * (re(b) + re(c)) - im(a) * (im(b) + im(c)) :=
begin
  simp,
end


/-! # Theorem:  The complex numbers are a commutative ring -/

-- Proof: we've defined all the structure, and every axiom can be checked by reducing it
-- to checking real and imaginary parts with `ext`, expanding everything out with `simp`
-- and then using the fact that the real numbers are a ring.
instance : comm_ring ℂ :=
by refine { zero := 0, add := (+), neg := has_neg.neg, one := 1, mul := (*), ..};
   { intros, apply ext_iff.2; split; simp; ring }

-- That is the end of the proof that the complexes form a ring. We built
-- a basic API which was honed towards the general idea that to prove
-- certain statements about the complex numbers, for example distributivity,
-- we could just check on real and imaginary parts. We trained the `simp`
-- lemma to simplify every
