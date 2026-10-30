-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ClaimTrue.lean: the proofs of `WaSeatAtHead`,
`WeightsItemAtHead` and `ClaimTrueAtHead` (Honest/K11/Plays/ClaimTrueStatement.lean), to the letter.
Lemmas; none of the library's goals.

How: joins. The first: the pair gives the library's "reached" at 346 (the frame's `thrS_rchAt`);
there `WaK6` holds (`P4.waK6_rchAt`, Johnson/P4R/WaK6AtRchAt.lean); the mask row's sentence `MaskAt`
and its member (`maskAt_head_plain`, `maskMemberAtHead`, of this folder) give `MaskSeatAt` by the
library's `maskSeat_of_maskAt` (Johnson/Top/H0/MergeLaw/MaskJoins.lean) and its written facts on the
seat (73, 2) (`AtMg.mask_sent`, `AtMg.mask_num`, Johnson/HB/LLHARD/MaskSeatWritten.lean). The
second: the thread's clause on its open items; "means" unfolds to the composed meaning's forms,
whose second half at the run "weights" is the sentence (`mgAll_forms`,
Johnson/Desc/Sound/MgAll.lean). The third: behind the member's step the input is the same and the
challenges heard have grown (the frame's `play_mid`, `play_heard`); another team's `forms_of_wtK6`
(Johnson/Desc/Kinds/Law/WtBack.lean) turns the sentence into the equation, its closed premises paid
by the library (`weights_facts`, Johnson/Desc/Sound/K11Tests/WeightsFactsInScope.lean; `rows_fit`,
`cols_fit`, `AtMg.mask_named`), the slot's bound by `svBelowRaw`, `countRaw`
(Johnson/Desc/K11/Front/) and `nMsg_le_ns`; a claim's value sees the cells inside the layout alone
(`claimVal_inside`, Honest/K11/Inner/Helps.lean, at the unit's facts of `frontS_at_head`).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ClaimTrueStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontSAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskAtHead
import Johnson.Desc.ProofFile.Honest.K11.Inner.Helps
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.K11.Front.LiveBehind
import Johnson.Desc.K11.Exchange.NumsAtFull
import Johnson.Desc.Kinds.Law.WtBack
import Johnson.Desc.Sound.K11Tests.WeightsFactsInScope
import Johnson.Desc.Sound.K11Tests.NumsHeadInScope
import Johnson.P4R.WaK6AtRchAt
import Johnson.HB.LLHARD.MaskSeatWritten
import Johnson.Top.H0.MergeLaw.MaskJoins

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open OnBytes.Road (gl_numerals)
open VerifiableInference.Desc.First (Here)
open VerifiableInference.Desc.First.K11Caller (cellsIn)
open VerifiableInference.Desc.First.MergeLaw (maskSeat_of_maskAt nMsg_le_ns hlay_at)
open VerifiableInference.Desc.Sound (mgAll mgBase mgAll_forms seatOf)
open VerifiableInference.Desc.K13.Law (cellAtNo)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (forms_of_wtK6)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull colBitsAtFull)
open Johnson.Desc.First.ForkMerge.Front (svBelowRaw countRaw)
open ProofFile.Honest.FirstThread (lettersHead thrS_rchAt thrS_reach_below head_valid)

/-- **The library's condition on the state in front of the merge, at the head's thread.** -/
theorem waSeat_at_head : WaSeatAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E
    hT
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := (IM.base_made O.made).2.2.1
  have hr := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w () hb hT
  have hf : s.failed = none := by
    obtain ⟨⟨_, _, hForm, _⟩, _⟩ := hT
    exact Option.isNone_iff_eq_none.1 hForm.1
  have hW := P4.waK6_rchAt h.scope h.reads O h.laid.planOk ((m.st.input.x.pub, s), ()) hr hf
  rw [ProofFile.Law.blankBy_W hG] at hW
  obtain ⟨xM, hxM⟩ := maskMemberAtHead Z D r Zp Np cF x h
  have hM := maskAt_head_plain Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀
    Vd Rd Kp w k s m E xM hxM hT
  have hseat : seatOf xM = (73, 2) := by
    have e := List.find?_some hxM
    simpa using e
  exact ⟨hW, maskSeat_of_maskAt h.𝔇.arr h.𝔇.N hM (by rw [hseat]; exact h.toAtMg.mask_sent)
    (by rw [hseat]; exact h.toAtMg.mask_num)⟩

/-- **The output head's sentence for "weights", out of the open item, at the head's thread.** -/
theorem weightsItem_at_head : WeightsItemAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E
    hopen hT ds
  obtain ⟨⟨_, _, _, hItems, _⟩, _⟩ := hT
  have hI : (mgAll (dataAtHead h Q carryX m.st.input) mgBase).forms 24 4 "weights"
      (m.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      (Q.wit k m.st.input (m.st.heard ++ ds)) := hItems ds _ hopen
  rw [mgAll_forms] at hI
  exact hI.2 rfl

/-- **The claim is true, at the head's thread.** -/
theorem claimTrue_at_head : ClaimTrueAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    weights hB hopen hR hcells blk k s m E ds y cols s' a claim x0 b9 hT hS _ ha hcl hx hb9 ds'
  obtain ⟨⟨⟨l, _, hy⟩, _⟩, _⟩ := hS
  have hin := (play_mid _ _ _ _ _ hy).1
  have hhe := play_heard _ _ _ _ _ hy
  have hV : Vd m.st.input :=
    ((head_valid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m.st.input).1 hT.1.2.2.2.2.2.2).2
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := (IM.base_made hB).2.2.1
  have hlay : (P5J.At.X Zp).layers.wsLay = (_root_.K11.parOf Zp Bs.G₀).lay := hlay_at hG
  obtain ⟨hplan, hTT, ⟨sh, Zs, hl⟩, hlam, hV2, hd5⟩ :=
    LT28.K11Tests.weights_facts h.scope h.reads h.pubOne
  have hr := reach_raw (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
  have hsv : x0.sV < (P5J.At.X Zp).H.ns := by
    have h1 := svBelowRaw Z D r Zp Np cF x m.st.input.x.pub s a x0 h hr ha hx
    have h2 := countRaw Z D r Zp Np cF x Bs m.st.input.x.pub s a h hB hr ha
    have h3 : (_root_.K11.parOf Zp Bs.G₀).nMsg ≤ (P5J.At.X Zp).H.ns := nMsg_le_ns hG
    omega
  have hE := forms_of_wtK6 h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N (P5J.At.X Zp) h.𝔇.layout (P5J.At.num Zp)
    (P5J.At.num Zp 24 0) 0 hplan hTT _ P5J.rows_fit P5J.cols_fit
    ⟨(_root_.K11.parOf Zp Bs.G₀).lay, 0, fun i => i.elim0, fun i => i.elim0⟩ hlay.symm
    (fun u => cellAtNo u.cells) (fun _ _ _ => rfl) h.toAtMg.mask_named Zs hl hlam hV2 hd5
    (m.st.input.x.pub, s)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    (Q.wit k m.st.input (m.st.heard ++ (ds ++ ds')))
    (waSeat_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      k s m E hT)
    (hR m.st.input hV) ha hcl hx hsv b9 hb9
    (weightsItem_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd
      Kp w k s m E hopen hT (ds ++ ds'))
  rw [hlay] at hE
  obtain ⟨a', claim', _, _, ha', hcl', _, _, _, _, un, hun, hshape, hU, hfit⟩ :=
    frontS_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      k s m E Bs hB hT
  obtain rfl : a = a' := Here.head.inj (ha.symm.trans ha')
  obtain rfl : claim = claim' := Option.some.inj (hcl.symm.trans hcl')
  have hm0 : (_root_.K11.parOf Zp Bs.G₀).lay.m0 = OnBytes.Flat.numsFull.rows := by
    obtain ⟨Bs', _, _, hB', _, _, h3, _, _, _⟩ := headMergeAtFull Z D r Zp Np cF x h
    obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
    have e := (colBitsAtFull Z D r Zp Np cF x h Bs' hB
      (LT28.K11Tests.numsB_head_of_public h.scope h.reads h.laid.pub h.pubOne
        (Nat.pow_right_injective (le_refl 2) (h.cols13.trans (by decide +kernel))))).2
    rw [e, h3]
  have hC := claimVal_inside gl_numerals hun hshape hU hfit
    (cellsIn ⟨(_root_.K11.parOf Zp Bs.G₀).lay, 0, fun i => i.elim0, fun i => i.elim0⟩
      (cellAtNo (Q.cells m.st.input)))
    (weightCells OnBytes.Flat.numsFull.rows (weights m.st.input.w₀)) (fun r c hr' hc' => by
      show (if _ : r < (_root_.K11.parOf Zp Bs.G₀).lay.m0 ∧
          c < 2 ^ (_root_.K11.parOf Zp Bs.G₀).lay.lk then cellAtNo (Q.cells m.st.input) r c
        else 0) = (if r < OnBytes.Flat.numsFull.rows then
          OnBytes.Model.Reading.gl.val (eOfF ((weights m.st.input.w₀).entry r c)) else 0)
      rw [dif_pos (And.intro hr' hc'), if_pos (by rw [← hm0]; exact hr')]
      exact hcells m.st.input hV r c hr' hc')
  show _ = _
  rw [hin, hhe, List.append_assoc]
  exact hE.trans hC

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.waSeat_at_head
#print axioms ProofFile.Honest.K11.weightsItem_at_head
#print axioms ProofFile.Honest.K11.claimTrue_at_head
