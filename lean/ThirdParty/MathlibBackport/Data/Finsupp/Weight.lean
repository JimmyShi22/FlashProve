/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/Data/Finsupp/Weight.lean, commit 5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0), lines
100-101. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import Mathlib.Data.Finsupp.Weight

namespace Finsupp
variable {σ M R : Type*} [Semiring R] (w : σ → M) [AddCommMonoid M] [Module R M]

theorem weight_eq_sum [Fintype σ] (f : σ →₀ R) : weight w f = ∑ i, f i • w i := by
  rw [weight_apply, f.sum_fintype (fun i c ↦ c • w i) fun _ ↦ zero_smul _ _]

end Finsupp
