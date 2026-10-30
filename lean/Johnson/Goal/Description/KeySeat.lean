-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/KeySeat.lean: the key file's seat's equation.
`kseat_name`: where `protocolDataWellFormed` says yes, the data and the decision behind the slot's gate are the own
data and the own run of a key file's description `Key.descriptionFromSource X N P`; that description is what
`Key.descAt` returns at what `publicOfO` reads of the three public files, at the layout file and at
the constant `Key.fixedDigest`; its tests on the plan, `wantedOk`, `owedOk` and every test of
`Key.lawsAsk` say yes. By `theLive_made` (Live.lean) and
`VerifiableInference.Desc.Key.laidFixed_is` (Johnson/Desc/Key/SlotIs.lean).
Limits. An equation between names: nothing on soundness. `protocolDataWellFormed` says yes at the written copies by
theorem (AtFullSide/Top/), as bytes by evaluation alone. What was run at the seat is not said here.

-/
import Johnson.Goal.Description.Live
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open VerifiableInference.Desc.Key

/-- **The value behind the key file's gate is the description's own.** -/
theorem kseat_name (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ X₀ m X N P,
      VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ ∧
      madeAt X₀ Z.lay fixedDigest = .ok m ∧
      descAt X₀ Z.lay fixedDigest = .ok (descriptionFromSource X N P) ∧ (descriptionFromSource X N P).planOk = true ∧
      (descriptionFromSource X N P).wantedOk = true ∧ (descriptionFromSource X N P).owedOk = true ∧
      (∀ t ∈ lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) ∧
      (descriptionFromSource X N P).data "key file" = .ok (theKeyData (asDescriptionFiles Z)) ∧
      theKeyRun (asDescriptionFiles Z) = ((descriptionFromSource X N P).pull keyInstanceOfOutOfDomainSample).run := by
  obtain ⟨K, _, _, hK, _, _⟩ := theLive_made (asDescriptionFiles Z) live
  obtain ⟨D, r⟩ := K
  have hK' : (VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay)).bind
      (fun X => keyDataAndDecisionAtFixedDigest X Z.lay) = .ok (D, r) := hK
  cases hX : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) with
  | error e => rw [hX] at hK'; cases hK'
  | ok X₀ =>
    rw [hX] at hK'
    obtain ⟨m, X, N, P, hm, _, _, _, h0, h1, h2, h3, h4, h5, h6⟩ := laidFixed_is X₀ Z.lay D r hK'
    refine ⟨X₀, m, X, N, P, rfl, hm, h0, h1, h2, h3, ?_, ?_, ?_⟩
    · rw [theKeyData_ok hK]; exact h4
    · rw [theKeyData_ok hK]; exact h5
    · rw [theKeyRun_ok hK]; exact h6

end FlashProve
