-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/OpenAt346.lean: the proofs of `WeightsOpenAt346` and
`WeightsOpenAtHead` (Honest/K11/Plays/OpenAt346Statement.lean), to the letter. Lemmas; none of the
library's goals.

How. The first: BY EVALUATION IN LEAN's KERNEL (`decide +kernel`, under the option maxRecDepth
1000000) on the written lists, as the frame's authors show, of another function on the same two
lists, which public items are open where. The second: the thread's open set at a border is that
term, by unfolding.

Limits. Those of the statements. The evaluation has been checked by Lean's own kernel alone. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.OpenAt346Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11

set_option maxRecDepth 1000000 in
/-- **The item "weights" of the head's segment is open at 346 and shut at 347.** -/
theorem weightsOpen_at_346 : WeightsOpenAt346 := by
  unfold WeightsOpenAt346
  decide +kernel

/-- **So the head's thread has it open at 346.** -/
theorem weightsOpen_at_head : WeightsOpenAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact weightsOpen_at_346.1

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.weightsOpen_at_346
#print axioms ProofFile.Honest.K11.weightsOpen_at_head
