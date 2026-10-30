-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/KeepsYes.lean: the proofs of `K11KeepsYesAtGives`, `K11KeepsYesAtIs`,
`K11KeepsYesAtElse` and `HeadMergeKeepsYesAtOfStep`
(Johnson/Desc/K11/Returns/KeepsYesStatement.lean), to the letter. Lemmas; none of the library's
goals.

How. The first three: by the definitions. The payer: the step's yes holds a yes of the seated
block's decision (`stepYes_decide`, Johnson/Top/H0/Walk/ReachInv.lean); that gives `K11Keeps`
(`headMergeKeeps`, Keeps.lean of this folder); and the seated block's decision is the kind's own
behind a guard on the mark (`headMergeSeated`, Seat.lean of this folder; `IM.guardMark_yes`,
Johnson/IMR/SeatForm.lean): as `headMergeKeeps`'s own proof goes.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.KeepsYesStatement
import Johnson.Desc.K11.Returns.Keeps
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open Johnson.Desc.First.Walk.Tied (stepYes_decide)

/-- **It gives the weaker wrapper.** -/
theorem k11KeepsYesAtGives : K11KeepsYesAtGives := fun _ _ _ _ h => ⟨h.1, h.2.1⟩

/-- **At its own place it is the stronger clause.** -/
theorem k11KeepsYesAtIs : K11KeepsYesAtIs := fun _ _ _ => ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- **At every other place it holds of no two states.** -/
theorem k11KeepsYesAtElse : K11KeepsYesAtElse := fun _ _ _ _ hp h => hp h.1

/-- **A yes of the member's step gives it at the kind's address.** -/
theorem headMergeKeepsYesAtOfStep : HeadMergeKeepsYesAtOfStep := by
  intro ft P name pl s s' h
  obtain ⟨rs, gs, e⟩ := stepYes_decide h
  have hK := headMergeKeeps P name pl s s' rs gs e
  rw [headMergeSeated P name pl] at e
  obtain ⟨h1, _⟩ := (IM.guardMark_yes (headClaimMergeKind P) s s' rs gs).1 e
  exact ⟨rfl, hK, rs, h1⟩

end Johnson.Desc.First.ForkMerge.Returns

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Returns.k11KeepsYesAtGives
#print axioms Johnson.Desc.First.ForkMerge.Returns.k11KeepsYesAtIs
#print axioms Johnson.Desc.First.ForkMerge.Returns.k11KeepsYesAtElse
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeKeepsYesAtOfStep
