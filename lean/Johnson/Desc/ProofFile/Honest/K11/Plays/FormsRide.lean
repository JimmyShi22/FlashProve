-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FormsRide.lean: the proofs of `KeepsYesOfStepped`,
`HeadMergeBehindYesS` and `FormsRideAtHead` (Honest/K11/Plays/FormsRideStatement.lean), to the
letter. Lemmas; none of the library's goals.

How. The first: as `keeps_of_stepped` (Riders.lean of this folder): the step holds a yes of the
seated block's decision; that gives `K11Keeps` (`headMergeKeeps`) and, behind the guard on the mark,
the yes of the kind's own decision (as Johnson/Desc/K11/Returns/KeepsYes.lean's payer goes). The
second: as `headMergeBehindS` (BehindS.lean of this folder), at the first. The third:
`formsFwdMgAll` (Johnson/Desc/K11/Across/FormsFwd.lean) at the thread's data: the open segment's
part and the ledger's sizes in front by `frontS_at_head`; that the part's ledger is the head's own
by the library's `seg_at_merge`; the slot of the merge's end value free, and the head's part open,
by the kind's clause; "means" at the item unfolds to the composed meaning's forms.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.FormsRideStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontSAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.Riders
import Johnson.Desc.K11.Across.FormsFwd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (step_iff)
open VerifiableInference.Desc.First (Here)
open VerifiableInference.Desc.First.MergeLaw (seg_at_merge)
open VerifiableInference.Desc.Sound (mgAll mgBase)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.Returns (headMergeKeeps headMergeSeated)
open Johnson.Desc.First.ForkMerge.Across (formsFwdMgAll)
open ProofFile.Honest.FirstThread (lettersHead)

/-- **The stronger clause, behind the member's step.** -/
theorem keepsYes_of_stepped : KeepsYesOfStepped := by
  intro Bk V W X Pb T b P name pl hmem blk k s m E ds y cols s' hblk hS
  have eb : blk = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl := by
    rw [hmem] at hblk
    exact (Option.some.inj hblk).symm
  subst eb
  have e := ((step_iff T.ft _ s s' _ cols _).1 hS.2).2.1
  have hK := headMergeKeeps P name pl s s' _ _ e
  rw [headMergeSeated P name pl] at e
  obtain ⟨h1, _⟩ := (IM.guardMark_yes (headClaimMergeKind P) s s' _ _).1 e
  exact ⟨hK, _, h1⟩

/-- **Behind its yes, from the pair, at the stronger clause.** -/
theorem headMergeBehindYesS : HeadMergeBehindYesS := by
  intro Bk V W X Pb T Said b P name pl hmem hkeeps hform hformP hrides blk hblk k s m E ds y cols s'
    hT _ hS
  have hK := keepsYes_of_stepped Bk V W X Pb T b P name pl hmem blk k s m E ds y cols s' hblk hS
  exact ⟨⟨hform blk k s m E ds y cols s' hT hS hblk hK,
    hformP blk k s m E ds y cols s' hT hS hblk hK⟩,
    hrides blk k s m E ds y cols s' hT hS hblk hK, hkeeps s s' hK⟩

/-- **A form's item rides past the merge's member.** -/
theorem formsRide_at_head : FormsRideAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    kk rr hrr hB hk hruns k s mm E s' ps v hT hK h0
  obtain ⟨⟨⟨a2, _, _, _, ha2, hop, _, _, hnf, _, _⟩, _⟩, rs, hy⟩ := hk s s' hK
  obtain ⟨a, _, _, b9, ha, _, _, hb9, hLR, _, _⟩ :=
    frontS_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      k s mm E Bs hB hT
  obtain rfl : a = a2 := Here.head.inj (ha.symm.trans ha2)
  obtain ⟨a1, _, _, ha1, _, _, eF, _⟩ := seg_at_merge (_root_.K11.parOf Zp Bs.G₀) hy b9 hb9
  obtain rfl : a = a1 := Here.head.inj (ha.symm.trans ha1)
  have hS : OnBytes.PscRun.Sized b9.F := by
    rw [eF]
    exact hLR.1
  have hfree : b9.F.gotF.getD (b9.F.next + 2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 2) false =
      false := by
    rw [eF]
    exact Bool.eq_false_iff.2 hnf
  have hfork : s.fork? = some b9.F := by
    rw [eF]
    simp [VerifiableInference.Desc.First.S.fork?, ha, hop]
  have h1 : (mgAll (dataAtHead h Q carryX mm.st.input) mgBase).forms 24 kk rr
      (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) v := h0
  have h2 := formsFwdMgAll _ _ _ _ _ _ _ (dataAtHead h Q carryX mm.st.input) mgBase 24 kk rr hrr
    (_root_.K11.parOf Zp Bs.G₀) mm.st.input.x.pub s s' ⟨rs, hy⟩ b9 hb9 hS hfree
    (fun p hp => ⟨(hruns k s mm E s' hT hK p hp).1,
      fun R hR => (hruns k s mm E s' hT hK p hp).2 b9.F R hfork hR⟩)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h1
  exact h2

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.keepsYes_of_stepped
#print axioms ProofFile.Honest.K11.headMergeBehindYesS
#print axioms ProofFile.Honest.K11.formsRide_at_head
