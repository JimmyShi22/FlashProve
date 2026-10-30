-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedAtHead.lean: the proof of `AcceptedSAtHead`
(Honest/K11/Plays/AcceptedAtHeadStatement.lean), to the letter. A lemma; none of the library's
goals.

How: calls. `headMergeAcceptedS` (AcceptedS.lean of this folder), general in the thread, at this
thread: its flat list is cF.blocksInOrder, whose number 346 is the kind's block at its seat
(`headMergeAtFull`, Johnson/Desc/K11/Exchange/AtFull.lean); its halves are the prover's of the first
chain; its premise "the state is ready wherever the pair holds" is `mergeReady_at_head`
(ReadyWhole.lean of this folder).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.ReadyWhole
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open ProofFile.Honest.FirstThread (lettersHead)

/-- **The frame's debt AcceptedS at the merge's member, at the head's thread, where the prover's
half there is the kind's.** -/
theorem acceptedS_at_head : AcceptedSAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs claims
    weights hmade hhalf fall
  obtain ⟨Bs', _, name, hmade', _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hmade'.symm.trans hmade)
  exact headMergeAcceptedS Bk W₀ Rc ProofFile.Inst Tr X _
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
    (_root_.K11.parOf Zp Bs'.G₀) claims weights name IM.k11Place hfl hhalf
    (fun k s m E hT => mergeReady_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX
      item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs' hmade hT) fall

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.acceptedS_at_head
