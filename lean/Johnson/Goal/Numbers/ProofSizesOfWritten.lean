-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/ProofSizesOfWritten.lean: seven fields of the written value of the sizes of a
proof's chains (`proofSizedFull`, Johnson/Desc/Ok/PlanWritten/SizedLit.lean) are the written values
that the law of the kind "the code switch" is stated at. Seven closed facts, by Lean's kernel; and
what follows for a record that is that written value. No definition.

Why. A test at the proof file's door holds the sizes that the planner makes against
`proofSizedFull`, whole (`sizedPinnedAt`, Johnson/Desc/Ok/PlanWritten/SizedTest.lean; its law
`sized_of_pinnedAt` gives `made.sized.proof = proofSizedFull`). The rows of the law at the 25
written records (Johnson/G/SwitchRowsAtScope.lean: `rows_of_eight`) ask equations on fields of the
sizes, with right sides from other files of written values. This file joins the two sets of written
values.

Main statements.
  `set_full`, `ownFirst_full`, `link_full`, `requestLink_full`, `requestCode_full`,
  `requestMask_full`, `requestAnswers_full`: the seven closed facts.
  `seven_of_sized`: the seven at a record z with `z = proofSizedFull`.

Limits. Two further equations that the rows ask, on `codes` and on `last.stages`, stand in
SizedTestLaws.lean (`codes_written`) and LastOfPinned.lean (`last_of_pinnedAt`). That the planner's
sizes are the written value at any files is not said here. Nothing on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.K12.Law.Sizes.TurnsLFull
import Johnson.Desc.K12.Law.Sizes.GroupsFull
import Johnson.G.SwitchPricesLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals.Sizes
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)
open H2K.Sizes H2K.Member Johnson.G

theorem set_full : proofSizedFull.set = setLit := by decide +kernel

theorem ownFirst_full :
    proofSizedFull.batch.own.first =
      { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
        slots := 1, rule := .johnson, m := 159 } := by decide +kernel

theorem link_full : proofSizedFull.link = ⟨gLink, 219⟩ := by decide +kernel

theorem requestLink_full : proofSizedFull.request.link = linksFull := by decide +kernel

theorem requestCode_full : proofSizedFull.request.code = 0 := by decide +kernel

theorem requestMask_full : proofSizedFull.request.maskCode = 0 := by decide +kernel

theorem requestAnswers_full : proofSizedFull.request.answers = 1 := by decide +kernel

/-- **The seven at a record that is the written value.** -/
theorem seven_of_sized {z : ProofSized} (h : z = proofSizedFull) :
    z.set = setLit ∧
      z.batch.own.first =
        { main := ⟨22, 262144, 3571, true⟩, mask := ⟨13, 256, 55, true⟩, k := 5, h := 1,
          slots := 1, rule := .johnson, m := 159 } ∧
      z.link = ⟨gLink, 219⟩ ∧ z.request.link = linksFull ∧ z.request.code = 0 ∧
      z.request.maskCode = 0 ∧ z.request.answers = 1 := by
  subst h
  exact ⟨set_full, ownFirst_full, link_full, requestLink_full, requestCode_full,
    requestMask_full, requestAnswers_full⟩

end VerifierAndGoals.Sizes

#print axioms VerifierAndGoals.Sizes.set_full
#print axioms VerifierAndGoals.Sizes.ownFirst_full
#print axioms VerifierAndGoals.Sizes.link_full
#print axioms VerifierAndGoals.Sizes.requestLink_full
#print axioms VerifierAndGoals.Sizes.requestCode_full
#print axioms VerifierAndGoals.Sizes.requestMask_full
#print axioms VerifierAndGoals.Sizes.requestAnswers_full
#print axioms VerifierAndGoals.Sizes.seven_of_sized
