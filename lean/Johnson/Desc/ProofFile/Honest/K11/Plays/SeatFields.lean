-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SeatFields.lean: the proofs of `StepsOfHalfCoins` and
`MergedWoAtHead` (Honest/K11/Plays/SeatFieldsStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The first: `stepsOfHalf` (Accepted.lean of this folder) has the steps at the very coins that
`lendRow` returns: `headMergeCoins` reads these off that return. The second: by unfolding: the
thread's "means" is `Item.holds` (Johnson/Desc/First/Borders.lean) at the honest letters over the
frame's meaning at the input (Honest/Thread/First.lean, FirstAt.lean); the honest letters turn five
fields, neither forms nor wo.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatFieldsStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Accepted

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11

/-- **The field steps, with its coins laid.** -/
theorem stepsOfHalfCoins : StepsOfHalfCoins := by
  intro Bk W₀ Rc Xi Tr X Pb T P claims weights name pl c₀ hhalf k w st hst
  obtain ⟨q, c, hl, rfl⟩ :=
    stepsOfHalf Bk W₀ Rc Xi Tr X Pb T P claims weights name pl hhalf k w st hst
  refine ⟨T.φ.sees w, q, ?_⟩
  unfold headMergeCoins
  rw [hl]

/-- **The fields merged and wo, at the head's thread.** -/
theorem mergedWo_at_head : MergedWoAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact ⟨fun _ _ _ _ hm => hm, fun _ _ _ _ hm => hm⟩

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.stepsOfHalfCoins
#print axioms ProofFile.Honest.K11.mergedWo_at_head
