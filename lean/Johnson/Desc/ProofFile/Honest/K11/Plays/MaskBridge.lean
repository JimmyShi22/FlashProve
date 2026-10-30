-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MaskBridge.lean: the proofs of `ScriptMsgIff`, `MaskTieOfOn`
and `ReaderAtBehind` (Honest/K11/Plays/MaskBridgeStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The first: by the structure's two projections and its constructor. The second: the member
number 346 is the kind's block at its seat (`headMergeAtFull`); the step holds that the chain's
steps at that block returned: so the book's lending to the half's parts returned (`stepsOfHalf`,
Accepted.lean of this folder), and the kind's coins are what it returned, not the spare letter; the
play leaves the prover's input (`play_mid`); the ledger's next free slot in front is 3531
(`nextAtRaw` at what the pair reaches); then the premise at the stand behind the step. The third: in
front of the step: the library's `MaskAt` (`maskAt_head_plain`, FrontAtHead.lean of this folder),
the open part (`frontS_at_head`), the member first at its seat (`xAt` is that search), its number
(`P5J.AtMg.mask_num`): the frame's authors' `readerAt_of_maskAt`; behind the step: the six facts
read the part's layout, statement and book of trees alone, which the merge's yes leaves (the
library's `seg_at_merge`; the yes by `keepsYes_of_stepped`, FormsRide.lean of this folder).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskBridgeStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Accepted
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontSAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.FormsRide
import Johnson.Desc.ProofFile.Honest.Law.Rule.ReaderPays
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.K11.Exchange.AtFull
import Johnson.Desc.K11.Front.LiveBehind
import Johnson.HB.LLHARD.MaskSeatWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.First.MergeLaw (seg_at_merge)
open VerifiableInference.Desc.Sound (seatOf numOf)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open Johnson.Desc.First.ForkMerge.Front (nextAtRaw)
open ProofFile.Honest.FirstThread (lettersHead thrS_reach_below)

/-- **The structure is its two fields.** -/
theorem scriptMsgIff : ScriptMsgIff :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun M => ⟨M.maskTie, M.indexTie⟩, fun M => ⟨M.1, M.2⟩⟩

/-- **The kind's premise on the mask row's message, from the frame's authors' form.** -/
theorem maskTieOfOn : MaskTieOfOn := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    claims weights c₀ hB hhalf hOn blk k s m E ds y cols s' a a9 hT hS hblk ha ha9 ds' i hi
  obtain ⟨Bs', _, name, hB', _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  obtain rfl : blk = IM.seatedAs ProofFile.sameReply
      (Johnson.Desc.First.ForkMerge.headClaimMergeKind (_root_.K11.parOf Zp Bs'.G₀)) name IM.k11Place :=
    Option.some.inj (hblk.symm.trans hfl)
  have hb : 346 ≤ cF.blocksInOrder.length := by
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hr := reach_raw (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
  have hnext : a.F.next = 3531 :=
    (nextAtRaw Z D r Zp Np cF x Bs' m.st.input.x.pub s a h hB hr ha).1
  obtain ⟨⟨l, hl, hy⟩, _⟩ := hS.1
  obtain ⟨q, c, hlend, _⟩ := stepsOfHalf Bk W₀ Rc ProofFile.Inst Tr X _
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (_root_.K11.parOf Zp Bs'.G₀)
    claims weights name IM.k11Place hhalf k m.st.input l hl
  have hin : y.2.st.input = m.st.input := (play_mid l ds [] m y hy).1
  have h0 := hOn k s' y.2 E ⟨_, s, m, E, ds, y, cols, hT, hS, hblk, rfl⟩ a9 ((q, (), ()), c, ())
    ha9 hlend ds' i hi
  unfold headMergeCoins
  rw [hlend, hnext, ← hin]
  exact h0

/-- **The reader's six facts at the stands behind the member's step.** -/
theorem readerAtBehind : ReaderAtBehind := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    free hB hp k s' m' En hAt a9 ha9
  obtain ⟨blk, s, m, E, ds, y, cols, hT, hS, hblk, _⟩ := hAt
  obtain ⟨Bs', _, name, hB', _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  obtain ⟨_, rs, hyes⟩ := keepsYes_of_stepped Bk _ _ X _
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346
    (_root_.K11.parOf Zp Bs'.G₀) name IM.k11Place hfl blk k s m E ds y cols s' hblk hS
  obtain ⟨xM, hxM⟩ := maskMemberAtHead Z D r Zp Np cF x h
  have hM := maskAt_head_plain Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀
    Vd Rd Kp w k s m E xM hxM hT
  obtain ⟨_, _, _, b9, _, _, _, hb9, _, _, _⟩ :=
    frontS_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      k s m E Bs' hB hT
  have hseat : seatOf xM = (73, 2) := by
    have := List.find?_some hxM
    simpa using this
  have hx : h.𝔇.ms.find? (fun z => decide (seatOf z = seatOf xM)) = some xM := by
    rw [hseat]
    exact hxM
  have hn : numOf h.𝔇.arr xM = P5J.At.num Zp 24 0 := by
    have e : numOf h.𝔇.arr xM = h.𝔇.arr (seatOf xM).1 (seatOf xM).2 := rfl
    rw [e, hseat]
    exact h.toAtMg.mask_num
  have hfront : ReaderAt h.𝔇.cs h.𝔇.arr h.𝔇.ms (h.𝔇.N.group 24) b9 (P5J.At.num Zp 24 0) free :=
    readerAt_of_maskAt hM hb9 hx hn (hp xM hxM)
  obtain ⟨_, _, pb, _, _, hpb, _, _, eL, est, ebk⟩ :=
    seg_at_merge (_root_.K11.parOf Zp Bs'.G₀) hyes b9 hb9
  obtain rfl : pb = a9 := Option.some.inj (hpb.symm.trans ha9)
  unfold ReaderAt at hfront ⊢
  rw [eL, est, ebk]
  exact hfront

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.scriptMsgIff
#print axioms ProofFile.Honest.K11.maskTieOfOn
#print axioms ProofFile.Honest.K11.readerAtBehind
