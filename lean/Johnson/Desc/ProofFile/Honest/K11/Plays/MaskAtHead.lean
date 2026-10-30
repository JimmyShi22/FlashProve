-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MaskAtHead.lean: the proofs of `MaskMemberAtHead` and
`MaskAtAtHead` (Honest/K11/Plays/MaskAtHeadStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. Calls alone. The member: `K11.members_atAll` (Johnson/K11R/AtAll.lean), `k11AtRB_at_head`
(Johnson/Desc/Sound/MgAt/K11MembersAtHead.lean) and `AtMg.mask_place`
(Johnson/HB/LLHARD/MaskSeatWritten.lean), joined as the library joins them
(Johnson/K11R/CondOfPend.lean). The thread gives the description's own "reached" at border 346
(`thrS_rchAt`, Honest/Thread/ReachAtHead.lean); two of its own clauses say that the state bears no
mark and that the table's condition holds at the border, at the thread's own meaning, which reads no
oracle's string (`Letters.thread`, Honest/Thread/First.lean; `onAt_honest_strs`,
Honest/Thread/NoStrs.lean; taken off as in `thr_pub`, Honest/Thread/FormLaw.lean). The law:
`maskAtB_seated` (Johnson/K11R/MaskSeat.lean), general in the meaning, called as `K11.mask_paid`
(Johnson/K11R/MaskPaid.lean) calls it. Its six premises on numbers: by the terms by which
`K11.k11Pub_of_eight` (Johnson/K11R/CondOfEight.lean) lays them. Its three along "reached": fields
of `P5J.foldFacts_at_head'` (Johnson/P5J/FoldJ3Whole.lean), as `K11.eight_at346`
(Johnson/K11R/EightAt346.lean) draws them. From the test with code to the sentence: `maskAt_of_test`
(Johnson/Top/H0/MergeLaw/MaskRow.lean). That 346 is a border of the chain: member number 346 is
there (`headMergeAtFull`, Johnson/Desc/K11/Exchange/AtFull.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskAtHeadStatement
import Johnson.Desc.ProofFile.Honest.Thread.NoStrs
import Johnson.Desc.K11.Exchange.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.Sound (onQ seatOf)
open VerifiableInference.Desc.Sound.MgAt (mergeAt)
open VerifiableInference.Desc.First.MergeLaw (maskAt_of_test maskAtB_seated total_addsAt firstCount
  momentCount)
open VerifiableInference.Desc.K13.Law (LFull laid_in_scope)
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open P5J (F0T)
open ProofFile.Honest.FirstThread (thrS_rchAt lettersHead onAt_honest_strs)

/-- **The member is there.** -/
theorem maskMemberAtHead : MaskMemberAtHead := by
  intro Z D r Zp Np cF x h
  obtain ⟨pM, xM, _, e1, e2, _, _⟩ := _root_.K11.members_atAll Zp cF Z.lay
    (VerifiableInference.Desc.Sound.k11AtRB_at_head h.toAtMg)
  obtain rfl : (73, 2) = pM := Option.some.inj (h.toAtMg.mask_place.symm.trans e1)
  exact ⟨xM, e2⟩

set_option maxRecDepth 100000 in
/-- **`MaskAt` in front of the merge's member.** -/
theorem maskAt_at_head : MaskAtAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Fr
    y xM hxM hT
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hr : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) 346 ((m.st.input.x.pub, s), y) :=
    thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w y hb hT
  have hThr := hT.1
  unfold Thr at hThr
  obtain ⟨-, -, ⟨hf, hP⟩, -, -, -, -⟩ := hThr
  have hf0 : s.failed.isNone = true := hf
  have hf' : s.failed = none := by
    cases hs : s.failed with
    | none => rfl
    | some e =>
      rw [hs] at hf0
      cases hf0
  have hon : onQ (Fr := Fr) (P5J.At.N Zp cF)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.At.links P5J.At.ps
      (fun t => (m.st.input.x.pub, t)) 346 (s, y) :=
    (onAt_honest_strs _ _ _ _ _ _ _ _ _ _ _).1 hP
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have hl := LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks
  have FF := P5J.foldFacts_at_head' h.toAtMg (Str := Fr.E.Str)
    (fun b a => RchAt (F0T OnBytes.secondHashFunction Zp Np cF) b a) (fun _ _ ha => ha)
    (L := LFull) (laid_in_scope h.scope h.laid.pub hy) (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  have hnum : 181 + (firstCount (P5J.At.shape Zp) 24 + 1) +
      (momentCount Bs.G₀.first.shape 24 1 + momentCount Bs.G₀.first.shape 24 2) =
        h.𝔇.N.msgsAt (some mergeAt) + 0 :=
    LT28.K11Tests.maskNum_at_cut h.scope h.laid.pub hy (congrArg (·.shape) O.first) _
      (_root_.K11.hc_paid h)
  exact maskAt_of_test (maskAtB_seated h.scope h.reads O (ft := 0) (start := ProofFile.startS Zp)
    (fun b a => RchAt (F0T OnBytes.secondHashFunction Zp Np cF) b a) (P5J.At.N Zp cF)
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.At.links P5J.At.ps
    (h.𝔇.N.group 24) (seatOf xM) 0 181 LFull (P5J.At.foldD Zp cF LFull).M mergeAt .head
    (P5J.At.shape Zp) 0 (fun _ ha => rchAt_raw ha)
    (LT28.K11Tests.maskNo_in_scope h.scope h.laid.pub hy)
    (LT28.K11Tests.maskLt_in_scope h.scope h.laid.pub hy)
    (by rw [total_addsAt]; exact hnum) _root_.K11.k11_there (by decide +kernel)
    (LT28.K11Tests.maskSeat_at hxM)
    (LT28.K11Tests.maskOwn_in_scope h.scope h.laid.pub hy hl hxM _ _ _ _ _)
    (LT28.K11Tests.maskBits_in_scope h.scope h.laid.pub hy)
    (fun a ha hm => FF.seatsCarried 346 a ha hm) (fun a ha hm => FF.msgShapes 346 a ha hm)
    (fun a ha hm => FF.liveShape 346 a ha hm) m.st.input.x.pub (s, y) hon hr hf')

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.maskMemberAtHead
#print axioms ProofFile.Honest.K11.maskAt_at_head
