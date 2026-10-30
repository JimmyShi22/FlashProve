-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/PlaysAtHead.lean: the proof of `PlaysAtHead`
(Honest/K11/Plays/PlaysAtHeadStatement.lean), to the letter. A lemma; none of the library's goals.

How: calls. `headMergePlaysHalf` (Accepted.lean of this folder), general in the thread, at this
thread: its flat list is cF.blocksInOrder, whose number 346 is the kind's block at its seat
(`headMergeAtFull`, Johnson/Desc/K11/Exchange/AtFull.lean); its halves are the prover's of the first
chain. The second half: the frame's `playsS_of` (Honest/Thread/PaysS.lean).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.PlaysAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Accepted
import Johnson.Desc.K11.Exchange.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open ProofFile.Honest.FirstThread (lettersHead)

/-- **The frame's debt Plays at the merge's member, at the head's thread, where the prover's half
there is the kind's.** -/
theorem plays_at_head : PlaysAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs claims
    weights hmade hhalf
  obtain ⟨Bs', _, name, hmade', _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hmade'.symm.trans hmade)
  have hp : Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346 :=
    headMergePlaysHalf Bk W₀ Rc ProofFile.Inst Tr X _
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346
      (_root_.K11.parOf Zp Bs'.G₀) claims weights name IM.k11Place hfl hhalf
  exact ⟨hp, fun Said => playsS_of _ Said hp⟩

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.plays_at_head
