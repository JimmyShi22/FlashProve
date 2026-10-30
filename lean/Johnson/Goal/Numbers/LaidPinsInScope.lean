-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/LaidPinsInScope.lean: IN THE GOALS' SCOPE, WHERE THE PROOF FILE's VALUE IS
LAID, BOTH PINS OF THE VERSION OF THE ENTRY TESTS WITH THIRTEEN ROWS
ACCEPT. A law file; it stands above Ladder/; outside the files whose checksums are frozen.

  laidPOf_pins_scope   in scope the key is the full size's (`key_in_scope_pure`): so `madeRow Z` and
                       `cutRow F Z` accept at the maker's own F and Z, and the lookups' three tests

Nothing on soundness.

-/
import Johnson.Desc.Laid.ProofFullPins
import Johnson.Goal.Numbers.KeyInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD.Full
open OnBytes.Maker
open VerifiableInference

variable {o : ProofFile.SecondHashFunctionArgument} {D : WholeD} {r : RunPF}

/-- **In the goals' scope, where the value is laid, both pins' tests accept.** -/
theorem laidPOf_pins_scope {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true)
    (h : proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    ∃ F Z, ProofFile.onlineDescription o W.pol W.lay W.KL = .ok F ∧
      ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z ∧
      PlanWritten.madeRow Z = true ∧ PlanWritten.cutRow F Z = true ∧
      Desc.K3Asks.digEntry Z = true ∧ Desc.K3Asks.readsEntry Z = true ∧
      Desc.K3Asks.headEntry Z = true := by
  obtain ⟨F, Z, hF, hZ, a, b, c, hp⟩ := laidPOf_pins h
  have hk : Desc.Door.atFullKey Z = true :=
    decide_eq_true (PlanWritten.key_in_scope_pure hW hZ)
  exact ⟨F, Z, hF, hZ, (hp hk).1, (hp hk).2, a, b, c⟩

end LPFD.Full

#print axioms LPFD.Full.laidPOf_pins_scope
