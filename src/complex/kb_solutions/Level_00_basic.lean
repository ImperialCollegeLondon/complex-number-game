/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- Import everything about the real numbers
import data.real.basic

/-!
# The complex numbers

We define the complex numbers, and prove that they are a ring.

We also "extract some basic API" (e.g. we prove that
two complex numbers are equal iff they have the same
real and imaginary parts)

This file has no `sorry`s in. All of the other levels:

`Level_01_of_real.lean`
`Level_02_I.lean`
`Level_03_conj.lean`
`Level_04_norm_sq.lean`
`Level_05_field.lean`
`Level_06_alg_closed.lean`

have sorrys, indicating puzzles to be solved.

# Main Definitions

`zero` : the complex number 0
`one` : the complex number 1
`add` -- addition of two complex numbers
`neg` -- negation of a complex number
`mul` -- multiplication of two complex numbers

# Main Theorem

`comm_ring` : The complex numbers are a commutative ring.

-/

/-- A complex number is defined to be a structure consisting of two real
  numbers, the real part and the imaginary part of the complex numberd. -/
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

example : complex.mk 3 4 = ⟨3, 4⟩ := begin refl end  -- "true by definition"

-- All of our definitions, like `zero` and `one`, will all
-- live in the `complex` namespace.

namespace complex

-- If you have a complex number, then you can get its real and 
-- imaginary parts with the `re` and `im` functions.

example : ℝ := re(mk 3 4) -- this term is (3 : ℝ)

example : re(mk 3 4) = 3 := begin refl end

-- Computer scientists prefer the style `z.re` to `re(z)` for some reason. 

example : (mk 3 4).re = 3 := begin refl end

example (z : ℂ) : re(z) = z.re := begin refl end

-- Before we start making the basic 
-- We now prove the basic theorems and make the basic definitions for
-- complex numbers. For example, we will define addition and multiplication on
-- the complex numbers, and prove that it is a commutative ring.
-- TODO fix

/-! # Defining the ring structure on ℂ -/

-- Our main goal is to prove that the complexes are a ring. Let's
-- define the structure first; the zero, one, addition and multiplication
-- on the complexes. 

/-! ## zero (0) -/

/-- The complex number with real part 0 and imaginary part 0 -/
def zero : ℂ := sorry

-- Now we set up notation so that `0 : ℂ` will mean `zero`. 

/-- notation `0` for `zero` -/
instance : has_zero ℂ := ⟨zero⟩

-- Let's prove the two basic properties, both of which are true by definition,
-- and then tag them with the appropriate attributes.
@[simp] lemma zero_re : re(0 : ℂ) = 0 := sorry
@[simp] lemma zero_im : im(0 : ℂ) = 0 := sorry

/-! ## one (1) -/

-- Now let's do the same thing for 1.

/-- The complex number with real part 1 and imaginary part 0 -/
def one : ℂ := sorry

/-- Notation `1` for `one` -/
instance : has_one ℂ := ⟨one⟩ 

-- name the basic properties and tag them with `simp`
@[simp] lemma one_re : re(1 : ℂ) = 1 := sorry
@[simp] lemma one_im : im(1 : ℂ) = 0 := sorry

/-! ## add (+) -/

-- Now let's define addition

/-- addition `z+w` of complex numbers -/
def add (z w : ℂ) : ℂ := sorry

/-- Notation `+` for addition -/
instance : has_add ℂ := ⟨add⟩

-- basic properties
@[simp] lemma add_re (z w : ℂ) : re(z + w) = re(z) + re(w) := sorry
@[simp] lemma add_im (z w : ℂ) : im(z + w) = im(z) + im(w) := sorry

/-! ## neg (-) -/

-- negation

/-- The negation `-z` of a complex number `z` -/
def neg (z : ℂ) : ℂ := sorry

/-- Notation `-` for negation -/
instance : has_neg ℂ := ⟨neg⟩

-- how neg interacts with re and im
@[simp] lemma neg_re (z : ℂ) : re(-z) = -re(z) := sorry
@[simp] lemma neg_im (z : ℂ) : im(-z) = -im(z) := sorry

/-! ## mul (*) -/

-- multiplication

/-- Multiplication `z*w` of two complex numbers -/
def mul (z w : ℂ) : ℂ := sorry

/-- Notation `*` for multiplication -/
instance : has_mul ℂ := ⟨mul⟩

-- how `mul` reacts with `re` and `im`
@[simp] lemma mul_re (z w : ℂ) : re(z * w) = re(z) * re(w) - im(z) * im(w) :=
sorry

@[simp] lemma mul_im (z w : ℂ) : im(z * w) = re(z) * im(w) + im(z) * re(w) :=
sorry

/-! ## Example of what `simp` can now do

example (a b c : ℂ) :
  re(a*(b+c)) = re(a) * (re(b) + re(c)) - im(a) * (im(b) + im(c)) :=
begin
  simp,
end

-/


/-! # `ext` : A mathematical triviality -/

/- 
Two complex numbers with the same and imaginary parts are equal. This is an
"extensionality lemma", i.e. a lemma of the form "if two things are made from
the same pieces, they are equal". This is not hard to prove, but we want to
give the result a name so we can tag it with the `ext` attribute, meaning that
the `ext` tactic will know it. To add to the confusion, let's call the
theorem `ext` :-)
-/

/-- If two complex numbers z and w have equal real and imaginary parts,
    they are equal -/
@[ext] theorem ext {z w : ℂ}
  (hre : re(z) = re(w)) (him : im(z) = im(w)) : z = w :=
begin
  sorry
end

/-! # Theorem:  The complex numbers are a commutative ring

Proof: we've defined all the structure, and every axiom can be checked by
reducing it to checking real and imaginary parts with `ext`, expanding
everything out with `simp`, and then using the fact that the real numbers are
a commutative ring (which we already know)

-/

/-- The complex numbers are a commutative ring -/
instance : comm_ring ℂ :=
begin
  -- first the data
  refine_struct {
      zero := (0 : ℂ), add := (+), neg := has_neg.neg, one := 1, mul := (*),
  ..},
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
end


/-

That is the end of the proof that the complexes form a ring. We built
a basic API which was honed towards the general idea that to prove
certain statements about the complex numbers, for example distributivity,
we could just check on real and imaginary parts. We trained the
simplifier to expand out things like re(z*w) in terms
of re(z), im(z), re(w), im(w).

-/

/-!

# Optional (for mathematicians) : more basic infrastructure, and term mode

-/

/-! 
## `ext` revisited

Recall extensionality:

theorem ext {z w : ℂ}
  (hre : re(z) = re(w)) (him : im(z) = im(w)) : z = w := ...

Here is another tactic mode proof of extensionality. Note that we have moved
the hypotheses to the other side of the colon; this does not
change the theorem. This proof shows the power
of the `rintros` tactic.
-/

theorem ext' : ∀ z w : ℂ, z.re = w.re → z.im = w.im → z = w :=
begin
  rintros ⟨zr, zi⟩ ⟨_, _⟩ ⟨rfl⟩ ⟨rfl⟩,
  refl,
end


/-!

Explanation: `rintros` does `cases` as many times as you like using this cool
`⟨ ⟩` syntax for the case splits. Note that if you say that a proof of `a = b`
is `rfl` then Lean will define a to be b, or b to be a, and not even introduce
new notation for it.

-/

-- Here is the same proof in term mode.

theorem ext'' : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

/-!
## `eta`
-/

/-
We prove the mathematically obvious statement that the
complex number whose real part is re(z) and whose imaginary
part is im(z) is of course equal to z.
-/

/-- ⟨z.re, z.im⟩ is equal to z -/
@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z :=
begin
  intro z,
  cases z with x y, 
  /-
    goal now looks complicated, and contains terms which look
    like {re := a, im := b}.re which obviously simplify to a.
    The `dsimp` tactic will do some tidying up for us, although
    it is not logically necessary. `dsimp` does definitional simplification.
  -/
  dsimp,
  -- Now we see the goal can be solved by reflexivity
  refl,
end

/-
The proof was "unfold everything, and it's true by definition".
This proof does not teach a mathematician anything, so we may as well write
it in term mode. Many tactics have term mode equivalent.
The equation compiler does the `intro` and `cases` steps,
and `dsimp` was unnecessary -- the two sides of the equation 
were definitionally equal.
-/

theorem eta' : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨x, y⟩ := rfl

/-!
## ext_iff
-/

/-
Note that `ext` is an implication -- if re(z)=re(w) and im(z)=im(w) then z=w.
The below variant `ext_iff` is the two-way implication: two complex
numbers are equal if and only if they have the same real and imaginary part.
Let's first see a tactic mode proof. See how the `ext` tactic is used?
After it is applied, we have two goals, both of which are hypotheses.
The semicolon means "apply the next tactic to all the goals
produced by this one"
-/

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
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

theorem ext_iff' {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
⟨λ H, by simp [H], and.rec ext⟩

end complex

/-!

# some last comments on the `simp` tactic

Some equalities, even if obvious, had to be given names, because we want `simp`
to be able to use them. In short, the `simp` tactic tries to solve
goals of the form A = B, when `refl` doesn't work (i.e. the goals are
not definitionally equal) but when any mathematician would be able
to simplify A and B via "obvious" steps such as `0 + x = x` or
`⟨z.re, z.im⟩ = z`. These things are sometimes not true by definition,
but they should be tagged as being well-known ways to simplify an equality.
When building our API for the complex numbers, if we prove a theorem of the
form `A = B` where `B` is a bit simpler than `A`, we should probably
tag it with the `@[simp]` attribute, so `simp` can use it.

Note: `simp` does *not* prove "all simple things". It proves *equalities*.
It proves `A = B` when, and only when, it can do it by applying 
its "simplification rules", where a simplification rule is simply a proof
of a theorem of the form `A = B` and `B` is simpler than `A`.  
-/
