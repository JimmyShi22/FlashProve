-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/BindingManyExit.lean: for a relation `R` of ZKCP/Defs.lean, the pair of relations `toPair R`
(ZKCP/SpecialDefs.lean) has the language of `R`, at every index and at `none` (`L_toPair`).
-/
import Compile.BindingMany
import Rom.ExitBind
import ZKCP.Special
import ZKCP.Optional

noncomputable section

namespace Compile.ManyExit

open Iop Rom Prob
open scoped ENNReal

/-! ## The language of `toPair R` -/

section Literal
open ZKCP.Special (toPair toGen)
variable {lam : ℕ} {I X Wn PP IVK ISK Pf : Type}

theorem L_toPair (R : ZKCP.IndexedRelation I X Wn PP) (o : Option I) : (toPair R).L o = R.L o := by
  cases o <;> rfl

end Literal

end Compile.ManyExit
