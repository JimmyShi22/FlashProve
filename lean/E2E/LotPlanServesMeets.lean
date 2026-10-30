-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotPlanServesMeets.lean: A TEST OF LotPlanServes' FIRST PREMISE, beside it, no part of it: offlineDescription returns
wherever the five returns are there, so wherever the test protocolDataWellFormed accepts.

Main names.
  description_of_made5: the converse of made5_of (E2E/LotPlanServesValue.lean).
  offlineDescriptionNamed: the proposition OfflineDescriptionNamed (E2E/TheHonestProverStatements.lean) at all public files, by
    key_sourced (E2E/KeyPublic.lean).

What it is worth. With the side library's theLive_zFull and theLive_zGap and VerifierAndGoals.inScope_full, inScope_gap (not called
here), the first two premises of LotPlanServes are met together at these two sets of written files. It says nothing on
the third premise, that ready returns.

Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotPlanServesValue
import E2E.TheHonestProverStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.LotPlanGround
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription OfflineDescriptionNamed)

/-- **Where the five return, offlineDescription returns what they return.** -/
theorem description_of_made5 {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (h : Made5 Z X N P) : offlineDescription Z = .ok ⟨X, N, P⟩ := by
  obtain ⟨X₀, m, h0, hm, r1, r2, r3⟩ := h
  unfold offlineDescription
  rw [h0]
  show (do
    let made ← VerifiableInference.Desc.Key.madeAt X₀ Z.lay VerifiableInference.Desc.Key.fixedDigest
    let source ← VerifiableInference.Desc.Key.sourceOf made
    let numbers ← VerifiableInference.Desc.Key.rangesNumbers made
    let later ← VerifiableInference.Desc.Key.laterPlaces made
    pure (⟨source, numbers, later⟩ : OfflineDescription) : Except String OfflineDescription) = _
  rw [hm]
  show (do
    let source ← VerifiableInference.Desc.Key.sourceOf m
    let numbers ← VerifiableInference.Desc.Key.rangesNumbers m
    let later ← VerifiableInference.Desc.Key.laterPlaces m
    pure (⟨source, numbers, later⟩ : OfflineDescription) : Except String OfflineDescription) = _
  rw [r1, r2, r3]
  rfl

/-- **The offline description is the one that the verifier's seat makes**, wherever the test on the public files says yes. -/
theorem offlineDescriptionNamed (files : VerifierAndGoals.PublicFiles) : OfflineDescriptionNamed files := by
  intro live
  obtain ⟨X, N, P, hs⟩ := AtPublicFiles.AtFiles.key_sourced files live
  exact ⟨⟨X, N, P⟩, description_of_made5 hs.source, hs⟩

end AtPublicFiles.LotPlanGround

#print axioms AtPublicFiles.LotPlanGround.description_of_made5
#print axioms AtPublicFiles.LotPlanGround.offlineDescriptionNamed
