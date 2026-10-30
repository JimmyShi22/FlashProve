-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/SpecXBase.lean: a description in order has its base in order.

Main theorem: `specX_base`.
-/
import OnBytes.Params.EntryRounds
import OnBytes.Tie.EntryFile

set_option autoImplicit false

namespace OnBytes.Tie

/-- If S is in order, so is `S.base`. -/
theorem specX_base (S : Fmt.SpecX) (hS : S.ok = true) : S.base.ok = true := by
  unfold Fmt.SpecX.ok at hS
  simp only [Bool.and_eq_true] at hS
  exact hS.1.1

end OnBytes.Tie

#print axioms OnBytes.Tie.specX_base
