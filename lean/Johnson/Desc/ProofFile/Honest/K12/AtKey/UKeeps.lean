-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/UKeeps.lean: what `keepsKey` (UKeepsText.lean), the value for the letter `keeps` of the
key file's shared thread, says at the members 0, 9, 10 and 11.

  `keepsKey_zero`, `keepsKey_nine`, `keepsKey_ten`, `keepsKey_eleven`, `keepsKey_same`

Limits.
- Five lemmas by unfolding.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UKeepsText
import Johnson.Desc.ProofFile.Honest.K12.AtFile.FiveAtNine
import E2E.HalvesAreJobs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest.K12.AtFile (keepsU)
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.K1 (SmpStay)
open _root_.Desc.K14 (St)
open AtPublicFiles.HalvesAreJobs (pU)

theorem keepsKey_zero (s s' : St) : keepsKey 0 s s' ↔ s' = s :=
  ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun h9 => by omega, fun h10 => by omega, fun h11 => by omega⟩⟩

theorem keepsKey_nine (s s' : St) : keepsKey 9 s s' ↔ keepsU pU s s' :=
  ⟨fun h => h.2.1 rfl, fun h => ⟨fun h0 => by omega, fun _ => h, fun h10 => by omega, fun h11 => by omega⟩⟩

theorem keepsKey_ten (s s' : St) : keepsKey 10 s s' ↔ Grows s.st s'.st ∧ SmpStay s.st s'.st :=
  ⟨fun h => h.2.2.1 rfl, fun h => ⟨fun h0 => by omega, fun h9 => by omega, fun _ => h, fun h11 => by omega⟩⟩

theorem keepsKey_eleven (s s' : St) : keepsKey 11 s s' ↔ s' = s :=
  ⟨fun h => h.2.2.2 rfl, fun h => ⟨fun h0 => by omega, fun h9 => by omega, fun h10 => by omega, fun _ => h⟩⟩

/-- At the members 0 and 11 it holds of a state and itself. -/
theorem keepsKey_same : ∀ b ∈ [0, 11], ∀ s, keepsKey b s s := by
  intro b hb s
  have h : b = 0 ∨ b = 11 := by simpa using hb
  exact ⟨fun _ => rfl, fun h9 => by omega, fun h10 => by omega, fun _ => rfl⟩

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.keepsKey_zero
#print axioms ProofFile.Honest.K12.AtKey.keepsKey_nine
#print axioms ProofFile.Honest.K12.AtKey.keepsKey_ten
#print axioms ProofFile.Honest.K12.AtKey.keepsKey_eleven
#print axioms ProofFile.Honest.K12.AtKey.keepsKey_same
