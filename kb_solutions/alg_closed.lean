/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard
Thanks: Imperial College London, leanprover-community
-/

import data.polynomial -- polynomials in one variable over rings
import complex.field -- solutions to levels 1 to 5
/-! 

# Level 6: The complex numbers are algebraically closed

-/

namespace complex

open polynomial

lemma exists_root {f : polynomial ℂ} (hf : 0 < degree f) : ∃ z : ℂ, is_root f z :=
begin
  sorry
end

end complex

/-
Chris Hughes, an undergraduate mathematician at Imperial College London, proved
this result in Lean and PR'ed it to Lean's maths library. 

Here is the link to the docs
https://leanprover-community.github.io/mathlib_docs/analysis/complex/polynomial.html

and here is the code
https://github.com/leanprover-community/mathlib/blob/3710744/src/analysis/complex/polynomial.lean#L34
-/
