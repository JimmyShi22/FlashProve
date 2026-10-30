/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/Algebra/Polynomial/HasseDeriv.lean, commit 5ed2965256430c3649e86755f9576b54eca72435
(v4.34.0), lines 127-131. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import Mathlib.Algebra.Polynomial.HasseDeriv

open Polynomial
namespace Polynomial
variable {R : Type*} [Semiring R]

@[simp]
theorem hasseDeriv_map {S : Type*} [Semiring S] (f : R →+* S) (k : ℕ) (p : R[X]) :
    hasseDeriv k (p.map f) = (hasseDeriv k p).map f := by
  ext
  simp [hasseDeriv_coeff]

end Polynomial
