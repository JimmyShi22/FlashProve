-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/PublicFactsAtTheHead.lean: CONDITIONAL: on the head at a return of the maker.
THE FULL SIZE ALONE.

What is here. Two facts on public data that the five statements at the members 9 and 10 of the shared
chain's thread take as premises (hb and hO of five_border_nine and five_border_ten,
AtFullSide/K12/InstanceLater.lean), paid under the head at the return, whatever the filling.

  eight_blocks_at_the_head   the linear claim's text makes its eight sub-protocols at the plan's own
                             parameters qAt A.Z h.places
  omega_place_at_the_head    the plan has a place for the proximity test on G_omega: in both
                             spellings that the two statements ask, and the tie of the two

By what. Calls alone: plan2_at_head (Honest/K14/PlanAtHead.lean) with Plan2.eight
(Honest/K14/Debts2.lean); omega_head and omega_of_four (Honest/K12/Sim/FirstPubOwnAtHead.lean).

Not shown here. That the head is met (at VerifierAndGoals.storedPublicFiles: `baseReturn_atStoredFiles`,
AtFullSide/HonestTrace/EntersAtStoredFiles.lean, has a return with a head). Nothing on a run, a
prover or a thread. Nothing on soundness, on completeness,
on hiding or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K14.PlanAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.LaterThreads
open ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.K12.AtProof (fourOf)
open VerifiableInference.Desc (Block K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St blocks)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- CONDITIONAL on h. **THE LINEAR CLAIM's TEXT MAKES ITS EIGHT SUB-PROTOCOLS AT THE PLAN's OWN
PARAMETERS.** -/
theorem eight_blocks_at_the_head (h : HeadAtReturn files A) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit,
      blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  obtain ⟨_, _, plan⟩ := K14.plan2_at_head h.head
  obtain ⟨eight⟩ := plan.eight
  exact ⟨_, _, _, _, _, _, _, _, eight.made⟩

/-- CONDITIONAL on h. **THE PLAN HAS A PLACE FOR THE PROXIMITY TEST ON G_omega**, in both spellings. -/
theorem omega_place_at_the_head (h : HeadAtReturn files A) :
    ∃ (numbers : H2U.PlaceNums) (place : P12), h.places.O = some numbers ∧
      (fourOf h.places).O = some place ∧ place = H2K.JointK.pGomega numbers := by
  obtain ⟨place, four⟩ := K12.Light.omega_head h.head.toAtMg
  obtain ⟨numbers, plain, tie⟩ := K12.Light.omega_of_four four
  exact ⟨numbers, place, plain, four, tie⟩

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.eight_blocks_at_the_head
#print axioms AtFullSide.LaterThreads.omega_place_at_the_head
