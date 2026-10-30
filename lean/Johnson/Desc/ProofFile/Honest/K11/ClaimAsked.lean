-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimAsked.lean: the proofs of `AskedSmallOfReply` and
`HeadClaimAsked` (Honest/K11/ClaimAskedStatement.lean), to the letter. Lemmas; none of the library's
goals.

How. The asked reply is a word of 32 bits laid as an element: read back by its first word it is that
number (`S.c0_ofNat`, Johnson/Desc/First/ReplyAsked.lean): so `S.replyTok?` answers it, and
`S.covered` is `S.coveredAt` at it, whose first test is "below V". The second: `WaK6` at the reached
state (`P4.waK6_rchAt`, Johnson/P4R/WaK6AtRchAt.lean) holds that `S.covered` answers; then
`headClaimReached` (ClaimAtHead.lean of this folder).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimAskedStatement
import Johnson.Desc.ProofFile.Honest.K11.ClaimAtHead
import Johnson.Desc.First.ReplyAsked

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (pW)
open OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- **The asked token is below the vocabulary's size.** -/
theorem askedSmallOfReply : AskedSmallOfReply := by
  intro x s T V cov hr hc
  have hn : ((Verify.words32 x.y).getD 0 0).toNat < pW.toNat :=
    Nat.lt_of_lt_of_le (UInt32.toNat_lt _) (by decide)
  have ht : s.replyTok? = some ((Verify.words32 x.y).getD 0 0).toNat := by
    unfold S.replyTok?
    rw [hr]
    show (if ofNat (ofNat ((Verify.words32 x.y).getD 0 0).toNat).c0.toNat ==
        ofNat ((Verify.words32 x.y).getD 0 0).toNat then
      some (ofNat ((Verify.words32 x.y).getD 0 0).toNat).c0.toNat else none) = _
    rw [S.c0_ofNat _ hn, if_pos (beq_self_eq_true _)]
  unfold S.covered at hc
  rw [ht] at hc
  unfold S.coveredAt at hc
  dsimp only at hc
  split at hc
  · cases hc
  · rename_i h1
    simpa using h1

/-- **At border 346, where the heard reply is the asked one.** -/
theorem headClaimAsked : HeadClaimAsked := by
  intro H Z D r Zp Np cF xP Bs Str y x heard s o claim h hB hr hf hrep ho hoc hties
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨_, _, _, _, cov, _, _, _, _, _, hcov, _, _⟩ :=
    P4.waK6_rchAt h.scope h.reads O h.laid.planOk ((x.pub, s), y) hr hf
  exact headClaimReached H Z D r Zp Np cF xP Bs' Str y x heard s o claim h hB hr hf ho hoc
    (askedSmallOfReply x s _ _ cov hrep hcov) hties

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.askedSmallOfReply
#print axioms ProofFile.Honest.K11.headClaimAsked
