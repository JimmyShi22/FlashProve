-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ReadyAtHead.lean: the proofs of `SevenReadyAtHead` and
`ReadyOfThreeAtHead` (Honest/K11/Plays/ReadyAtHeadStatement.lean), to the letter. Lemmas; none of
the library's goals.

How: calls. The first: `halfReady_at_head` (FrontAtHead.lean of this folder) · that a claim is laid:
`claimLaidRaw` (Johnson/Desc/K11/Front/ClaimLaid.lean) at what the pair reaches (the frame's
`thrS_reach_below`, Honest/Thread/ReachAtHead.lean; the library's `reach_raw`) · that nothing waits:
`noneWaitsOfShape` (the same file) at the first Bool of the thread's own public form. The second:
the first; the end value's slot is the next free number and 2 lk + 2 more: below the number of slots
by the count; not filled by "free above".

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontAtHead
import Johnson.Desc.K11.Front.ClaimLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.First (Here)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open Johnson.Desc.First.ForkMerge.Front (claimLaidRaw noneWaitsOfShape)
open Johnson.Desc.First.ForkMerge.Returns (mergeEndSlot)
open ProofFile.Honest.FirstThread (thrS_reach_below lettersHead noStrs)

/-- **Seven clauses, and two facts beside.** -/
theorem sevenReady_at_head : SevenReadyAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    hmade hT
  obtain ⟨hf, a, hx, ha, o1, hax, o2, o3, o4⟩ := halfReady_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr
    X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs hmade hT
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  obtain ⟨a', _, _, _, claim, ha', _, _, _, _, hcl, _⟩ := claimLaidRaw Z D r Zp Np cF x Bs
    m.st.input.x.pub s h hmade
    (reach_raw (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT))
  obtain rfl : a' = a := Here.head.inj (ha'.symm.trans ha)
  have hThr := hT.1
  unfold Thr at hThr
  obtain ⟨-, -, ⟨-, hP⟩, -, -, -, -⟩ := hThr
  have hP' : VerifiableInference.Desc.First.onAt (P5J.At.N Zp cF)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.At.links P5J.At.ps[346]?
      _ _ (m.st.input.x.pub, s) noStrs := hP
  have hsh : VerifiableInference.Desc.First.shapeAt P5J.At.links P5J.At.ps[346]? s = true := by
    rcases hP'.2 with hm | ⟨hB, _⟩
    · exact absurd hf hm
    · simp only [Bool.and_eq_true] at hB
      exact hB.1.1.1.1.1
  exact ⟨hf, a', claim, hx, ha, o1, noneWaitsOfShape s hsh, hcl, hax, o2, o3, o4⟩

/-- **"The state is ready" from the three clauses that are left.** -/
theorem readyOfThree_at_head : ReadyOfThreeAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    hmade hT h3
  obtain ⟨hf, a, claim, hx, ha, o1, hw, hcl, hax, o2, o3, o4⟩ := sevenReady_at_head Z D r Zp Np cF x
    h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs hmade hT
  obtain ⟨t1, t2, t3⟩ := h3 a claim hx ha hcl hax
  refine ⟨hf, a, claim, hx, ha, o1, hw, hcl, hax, t1, o2, t2, ?_, ?_, t3⟩
  · unfold mergeEndSlot
    rw [o3]
    omega
  · apply o4
    unfold mergeEndSlot
    omega

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.sevenReady_at_head
#print axioms ProofFile.Honest.K11.readyOfThree_at_head
