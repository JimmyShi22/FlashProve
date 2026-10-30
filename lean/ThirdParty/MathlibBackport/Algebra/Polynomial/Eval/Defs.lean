/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/Algebra/Polynomial/Eval/Defs.lean, commit 5ed2965256430c3649e86755f9576b54eca72435
(v4.34.0), lines 222-225. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Polynomial
variable {R S : Type*} [Semiring R] [CommSemiring S]

@[simp]
theorem eval₂RingHom_comp_C (f : R →+* S) (x : S) : (eval₂RingHom f x).comp C = f := by
  ext
  simp

end Polynomial
