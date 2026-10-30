-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/SealPort.lean: rounds in which no value of the verifier's message is bad, against the
rounds "SEAL" and "SPLIT" that the planner adds.

Statements with their proofs.
Main names:
  `covered_zero`: a round without a bad value is covered by every planned round, under every scope.
  `runs_seal'`, `runs_split'`: the planner's routines `planSeal` and `planSplit` add one round each.
  `seal_values`, `seal_covered`: the message of "SEAL" has one value; no bad value of one is
    covered.
  `split_fits`, `split_covered`: "SPLIT" has no verifier's message; no bad value of one fits it and
    is covered.
Limits: nothing on a block of the proof library: that a block has no bad value is not shown here.
`covered_zero` says little: an error that a plan holds is not negative. The bytes of "SPLIT", 24,
are not compared.

-/
import OnBytes.Tie.Pv.PortKit
import OnBytes.Params.PlanListsChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv
open OnBytes OnBytes.Params

/-- A round without a bad value is covered by every planned round. -/
theorem covered_zero (s : Setting) (c : Scope) (n : ℕ) (y : RoundSpec) : Covered s c (0, n) y := by
  unfold Covered
  rw [Nat.cast_zero, zero_div]
  exact_mod_cast Binary.val_nonneg _

theorem runs_seal' (s : Setting) (c : Scope) : Runs s c 0 0 0 planSeal () [sealRound] 0 0 0 :=
  runs_seal

theorem runs_split' (s : Setting) (c : Scope) :
    Runs s c 0 0 0 planSplit () [.silent "SPLIT" (24 * 1) 0] 0 0 0 := runs_split

theorem seal_values (q : ℕ) : valuesOf q sealRound = 1 := by
  simp [valuesOf, sealRound]

theorem seal_covered (s : Setting) (c : Scope) : Covered s c (0, 1) sealRound :=
  covered_zero s c 1 sealRound

theorem split_fits (q : ℕ) : Fits q (0, 1) (.silent "SPLIT" (24 * 1) 0) := ⟨rfl, rfl⟩

theorem split_covered (s : Setting) (c : Scope) :
    Covered s c (0, 1) (.silent "SPLIT" (24 * 1) 0) := covered_zero s c 1 _

end Cb.Pv

#print axioms Cb.Pv.covered_zero
#print axioms Cb.Pv.seal_values
#print axioms Cb.Pv.split_fits
