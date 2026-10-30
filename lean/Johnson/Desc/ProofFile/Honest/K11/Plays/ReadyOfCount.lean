-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ReadyOfCount.lean: the proof of `ReadyOfCountAtHead`
(Honest/K11/Plays/ReadyOfCountStatement.lean), to the letter. A lemma; none of the library's goals.

How: calls. `readyOfThree_at_head` (ReadyAtHead.lean of this folder); of its three clauses the first
by `claimFitsRaw` (Johnson/Desc/K11/Front/ClaimFits.lean) and the second by `filledRaw`
(Johnson/Desc/K11/Front/Filled.lean), both at what the pair reaches (the frame's `thrS_reach_below`,
Honest/Thread/ReachAtHead.lean; the library's `reach_raw`); the third is the premise.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyOfCountStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyAtHead
import Johnson.Desc.K11.Front.ClaimFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open Johnson.Desc.First.Walk.Tied (reach_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open Johnson.Desc.First.ForkMerge.Front (claimFitsRaw filledRaw)
open ProofFile.Honest.FirstThread (thrS_reach_below)

/-- **"The state is ready" from the count of slots alone.** -/
theorem readyOfCount_at_head : ReadyOfCountAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    hmade hT hc
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hr := reach_raw (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
  exact readyOfThree_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd
    Rd Kp w k s m E Bs hmade hT fun a claim hx ha hcl hax =>
      ⟨claimFitsRaw Z D r Zp Np cF x Bs m.st.input.x.pub s a claim h hmade hr ha hcl,
        filledRaw Z D r Zp Np cF x m.st.input.x.pub s a hx h hr ha hax, hc a ha⟩

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.readyOfCount_at_head
