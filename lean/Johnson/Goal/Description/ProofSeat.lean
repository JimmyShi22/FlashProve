-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/ProofSeat.lean: the proof file's seat's equation.
`pseat_name`: where `protocolDataWellFormed` says yes, the data and the decision behind the slot's gate are the
own data and the own run of the description that `ProofFile.onlineDescription` makes of the three public files at
the format's second hash function; that description's tests on the plan say yes, and so does every
test of `LPFD.lawsAsk`. By `theLive_made` (Live.lean) and `LPFD.Full.laidPOf_ok`
(Johnson/Desc/Laid/ProofFullLaw.lean).
Limits. An equation between names: nothing on soundness. `protocolDataWellFormed` says yes at the written copies by
theorem (AtFullSide/Top/), as bytes by evaluation alone. What was run at the seat is not said here.

-/
import Johnson.Goal.Description.Live
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals

/-- **The value behind the proof file's gate is the description's own.** -/
theorem pseat_name (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ F, ProofFile.onlineDescription OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok F ∧ F.planOk = true ∧
      F.data "proof file" = .ok (theProofData (asDescriptionFiles Z)) ∧
      (∀ t ∈ LPFD.lawsAsk OnBytes.secondHashFunction Z.pol Z.lay Z.KL F (theProofData (asDescriptionFiles Z)),
        t.2 = true) ∧
      theProofRun (asDescriptionFiles Z) = (F.pull LPFD.Full.instanceAsPlainRecord).run := by
  obtain ⟨_, P, _, _, hP, _⟩ := theLive_made (asDescriptionFiles Z) live
  obtain ⟨D, r⟩ := P
  obtain ⟨F, h1, h2, h3, h4, h5⟩ :=
    LPFD.Full.laidPOf_ok (o := OnBytes.secondHashFunction) (pol := Z.pol) (lay := Z.lay) (KL := Z.KL) hP
  refine ⟨F, h1, h2, ?_, ?_, ?_⟩
  · rw [theProofData_ok hP]; exact h3
  · rw [theProofData_ok hP]; exact h4
  · rw [theProofRun_ok hP]; exact h5

end FlashProve
