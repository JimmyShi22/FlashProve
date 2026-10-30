-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ReadyWhole.lean: the proof of `MergeReadyAtHead`
(Honest/K11/Plays/ReadyWholeStatement.lean), to the letter. A lemma; none of the library's goals.

How: calls. `readyOfCount_at_head` (ReadyOfCount.lean of this folder) at `countRaw`
(Johnson/Desc/K11/Front/Count.lean), at what the pair reaches (the frame's `thrS_reach_below`,
Honest/Thread/ReachAtHead.lean; the library's `reach_raw`).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyWholeStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyOfCount
import Johnson.Desc.K11.Front.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open Johnson.Desc.First.Walk.Tied (reach_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open Johnson.Desc.First.ForkMerge.Front (countRaw)
open ProofFile.Honest.FirstThread (thrS_reach_below)

/-- **"The state is ready", whole.** -/
theorem mergeReady_at_head : MergeReadyAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    hmade hT
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hr := reach_raw (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
  exact readyOfCount_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd
    Rd Kp w k s m E Bs hmade hT fun a ha =>
      countRaw Z D r Zp Np cF x Bs m.st.input.x.pub s a h hmade hr ha

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.mergeReady_at_head
