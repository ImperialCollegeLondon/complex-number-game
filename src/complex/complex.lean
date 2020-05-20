/-
The complex numbers.
A documented remix of part of mathlib

Our goal is to define the complex numbers, and then "extract some API".
Our first goal is to define addition and multiplication,
and prove that the complex numbers are a commutative ring.
We then do a slightly more computer-sciency worked development of the
natural inclusion from the reals to the complexes. 

There are then a bunch of API-building exercises, which can be solved in term mode
or tactic mode. The first is `I`, the second is complex conjugation,
and the third is the "squared norm" function. 

There is then a speculative last exercise on harder properties
of the complexes.
-/

-- We will assume that the real numbers are a field.
import data.real.basic

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

/-! ## The first triviality -/

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

@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨x, y⟩ := rfl

/-! ### Digression on `simp` -/

-- It's important we give this theorem a name (and we called it `eta`
-- because that's what computer scientists call lemmas of this form).
-- The reason it's important is that we want `simp`
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

/-! ## The second triviality -/

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

