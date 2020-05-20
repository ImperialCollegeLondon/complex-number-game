-- let's assume the real numbers ℝ exist, and are a field
import data.real.basic

/-!
# The complex numbers

We define the complex numbers, and prove that they are a ring.
We then might do other stuff

-/

/-- The complex numbers ℂ, defined as pairs ⟨x, y⟩ of real numbers. -/
structure complex :=
(re : ℝ)
(im : ℝ)

notation `ℂ` := complex

-- that's the end of the definition

variables (z : ℂ)
variables (x y : ℝ)

-- example (x : ℝ) : x = 0 :=
-- begin
--   sorry
-- end

-- example (z : ℂ) : z = 0 :=
-- begin
--   sorry
-- end
/-
failed to synthesize type class instance for
z : ℂ
⊢ has_zero ℂ
-/

-- new complex number stuff goes in here
namespace complex

def zero : ℂ := sorry

-- secret computer science function which makes notation `0` work
instance : has_zero ℂ := ⟨zero⟩

example (z : ℂ) : z = 0 :=
begin
  sorry
end

-- note that I have no errors.

-- how do we actually make a complex number anyway?

-- Let's leave the complex namespace for a bit
end complex

#print prefix complex
-- let's freeze it
-- That's what the computer scientists want to see.
namespace complex

/-!
I give you: 

# The mathematician's part of the complex namespace

In the complex namespace, mathematicians and
computer scientists co-exist.

They write tactics and we write mathematics.

WARNING: Currently mostly full of
computer science junk which we will
*IGNORE*

WARNING: IF YOU ARE DOING THIS ON THE WEB EDITOR
IT WILL GET SLOW

MAKE STREAM COMPLEX NUMBER GAME IN #MATHS 
ADVERTISE TWITCH TALK LAUNCHING THE COMPLEX NUMBER GAME
MAKE TINYURL SHOTCUT TO WEB EDITOR

* TODO 
PUSH TO IC GITHUB THE COMPLEX NUMBER GAME

CLONE, ASK KEVIN BUZZARD FOR PUSH ACCESS TO NON-MASTER BRANCH. 

TO MATHEMATICIANS: MAKE IT YOURSELF

IF YOU THINK IT'S TOO EASY, THEN MAKE RIEMANN SURFACES BECAUSE WE NEED THEM

CREATE WEB EDITOR LINK
POST LINK ON ZULIP AND TWITTER

WITHIN THE CRAP WE FIND FOUR INTERESTING FUNCTIONS

/-! re : takes a complex number to its real part-/
re : ℂ → ℝ

/-! im : takes a complex number to its imaginary part-/
im : ℂ → ℝ

/-! mk : takes two real numbers x and y, and spits out a complex number
thought of as $x+iy$ by humans and as the ordered pair $(x,y)$ by computers-/
mk : ℝ → (ℝ → ℂ)

ALL THE REST ARE WHAT THE ALGORITHM PEOPLE NEED TO MAKE TACTICS WORK.
THEY WERE ALL WRITTEN BY A COMPUTER PROGRAM. 

The *system* added as an *axiom*, the principle of mathematical recursion
for the complex numbers: 
rec : Π {C : ℂ → Sort l}, (Π (re im : ℝ), C {re := re, im := im}) → Π (n : ℂ), C n
The computer scientists use this axiom to make *algorithms*.
The algorithms turn into *tactics*
and we mathematicians can use the tactics to make the complex
numbers behave the way a mathematician wants them to behave.

Some of the algorithms make notation. 

HAVE SOME CUT AND PASTE STUFF IN SOME TWITCH.LEAN DOC FILE WHICH GETS
*DELETED* AFTER 

push I.lean and whatever else as puzzles in complex.

Can you prove they're a field?

Can you prove they're an algebraically closed field?

Chris Hughes did this when he was a 2nd year undergraduate mathematician at
Imperial College London

To do it, it had to make the theory of polynomials in one variable over a ring.

And he made the theory of polynomials for me.

Thank you Chris Hughes!

Note that Chris is actually a computer scientist at heart, because
his code is incomprehensible to mathematicians

Mathlib is like Bourbaki. It is there for people who don't want to worry about
why the complex numbers is algebraically closed and just need it, like they
might need Banach spaces the next day and perfectoid spaces the day after
and Riemann surfaces the day after and just need them all to work like
normal. If you want to do normal maths in Lean, import mathlib. 

This is what happens if you don't import data.complex.basic
This file is a mathematician's remix of data.complex.basic

Maybe make a blog post: data.complex: a mathematician's remix.

For computer science version see * TODO link to mathlib docs *

post link to mathlib doc for definition of data.complex

* TODO * check there's a well-documented mathlib 
-/

def z : ℂ := mk 3 4

def z1 : ℂ := ⟨3, 4⟩

--noncomputable theory -- the reals are noncomputable
--example : ℂ := ⟨3.7,-1⟩

-- TODO : push to github *just* before talk, but without "basic"
-- with games all up and running
-- levels I and 

-- Make the hints an md file

-- TODO TODAY: Make repo, tell William and say if this could happen on CoCalc 
-- instead of on GitHub then I would be happy to make that happen.

-- The Complex Number Game -- live on Twitch on Thursday 

-- TODO: basic.lean needs a copyright. Ask Johan and Patrick?
#exit