-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/FoldAt.lean: at a state in front of the closing of segment l (K10) that the first
chain's own blocks reach from its own start, under the library's head (`P5J.AtMgA`, at the older hash), at a state without a
mark of failure: the three tests in front of the fold say yes. They are the fields shape, maskfits and spendAsMask of
`CloseBase` (Johnson/Desc/K10/Honest/Base.lean).

  `mask_no_reached`   the frame's fresh mask is the plan's number of that message, at all 25 links
  `mask_message`      the fresh mask's message is there: no main row, one mask row under the shape's mask code, no answer
  `fold_shape`        the test on the fold's shape
  `fold_mask`         the test on the fresh mask
  `fold_spend`        the test on its being spent

Limits. The last two take as a premise that the fresh mask's message is neither sampled nor spent. The two main tests also
take as premises what `BaseData` names and, for the shape, that the group has the shape's main code and that the layout's k
and h are the frame's group's. The full size and the older hash alone. Whether the head can be had at any files is not shown
here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AtReach
import Johnson.Desc.ProofFile.Honest.K10.Pay.FoldClosed
import Johnson.Desc.ProofFile.Honest.K10.Pay.FoldParts
import Johnson.Desc.ProofFile.Honest.K10.Xch.Height
import Johnson.P5J.MaskAtMgAll
import Johnson.IMR.FlagsNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (told_at_written toldCut)
open VerifiableInference.Desc.First.Close (maskNo maskPub seatsPlanW mask_public mask_at_cut hc_at_laid written_codes)
open VerifiableInference.Desc.First.K2Hands (MList MW_eq)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.K12.Door (msgsOfChain msgShape_at)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)
open Johnson.G (codesFull2)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA TS)
open ProofFile.Honest.K10.YesFree (BaseData)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **In front of a closing the frame's fresh mask is the plan's number of that message.** At what the chain's own blocks
reach; the library's three sentences stand at a stronger sense of "reached" and go down to the plain fold at once. -/
theorem mask_no_reached (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) :
    (recOf s).frame.mask = some (maskNo seatsPlanW P5T.psFull l) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hc := hc_at_laid h.scope h.laid
  have key : ∃ L : OnBytes.Model.LinkCtx, s.link? = some L ∧
      L.check.frame.mask = some (maskNo seatsPlanW P5T.psFull l) := by
    rcases Nat.eq_zero_or_pos l with rfl | h1
    · have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 12 (z, s) := hr
      obtain ⟨-, rs, cols, f⟩ := hr'.fold
      obtain ⟨L, hL, -, em⟩ := Meaning.K2.mask_zero_named h.scope h.reads O (n := 9) (Nat.le_refl 9) f
      have em' : L.check.frame.mask =
          some (maskPub (P5T.N0Full.withTold IM.placesW (Meaning.Carry.toldOf cF.blocksInOrder)) Zp.first.shape 0) := by
        unfold maskPub
        rw [if_pos rfl]
        exact em
      rw [h.shape_full] at em'
      exact ⟨L, hL, em'.trans (congrArg some (mask_at_cut hc P5T.N0Full 0 (by omega)))⟩
    · rcases Nat.lt_or_ge l 24 with h24 | h24
      · have e : 14 * l + IM.nAt l + 5 = 14 * l + 3 + 9 := by
          have : IM.nAt l = 7 := if_neg (by omega)
          omega
        rw [e] at hr
        obtain ⟨-, rs, cols, f⟩ := hr.fold
        obtain ⟨L, hL, -, em⟩ :=
          mask_public h.scope h.reads O h.laid.planOk P5T.N0Full h1 h24 (n := 9) (Nat.le_refl 9) f
        rw [h.shape_full] at em
        exact ⟨L, hL, em.trans (congrArg some (mask_at_cut hc P5T.N0Full l (by omega)))⟩
      · obtain rfl : l = 24 := by omega
        have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 350 (z, s) := hr
        obtain ⟨-, rs, cols, f⟩ := hr'.fold
        obtain ⟨t₀, R₀, C₀, L, f₀, hL, -, em⟩ :=
          Meaning.K2.mask_head_named h.scope h.reads O (n := 10) (Nat.le_refl 10) f
        have hlen := Meaning.K2.flat_358 h.scope O
        have s0 := Meaning.K2.size_at_table h.scope h.reads O h.laid.planOk P5T.N0Full (k := 339) (by omega) f₀
        have em' : L.check.frame.mask =
            some (maskPub (P5T.N0Full.withTold IM.placesW (Meaning.Carry.toldOf cF.blocksInOrder)) Zp.first.shape 24) := by
          unfold maskPub
          rw [if_neg (by omega : ¬ (24 : Nat) = 0), if_pos rfl, ← s0]
          exact em
        rw [h.shape_full] at em'
        exact ⟨L, hL, em'.trans (congrArg some (mask_at_cut hc P5T.N0Full 24 (by omega)))⟩
  obtain ⟨L, hL, em⟩ := key
  show s.live.frame.mask = _
  unfold VerifiableInference.Desc.First.S.live
  rw [hL]
  exact em

/-- **In front of a closing the fresh mask's message is there, with no main row, one mask row under the shape's mask code
and no answer.** -/
theorem mask_message (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) {mk : Nat}
    (hm : (recOf s).frame.mask = some mk) :
    ∃ y : OnBytes.Oracle, (recOf s).st.oracles[mk]? = some y ∧ y.shape.mainRows = 0 ∧ y.shape.maskRows = 1 ∧
      y.shape.maskCode = (recOf s).frame.shape.maskCode ∧ y.shape.answers = 0 := by
  obtain rfl : mk = maskNo seatsPlanW P5T.psFull l :=
    Option.some.inj (hm.symm.trans (mask_no_reached h.toAtMg hl hr))
  obtain ⟨-, -, hsh, -, hM⟩ := facts_reached h hr hf
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hc := hc_at_laid h.toAtMg.scope h.toAtMg.laid
  obtain ⟨hk, rs, cols, f⟩ := hr.fold
  have s0 := Meaning.K2.size_at_table h.toAtMg.scope h.toAtMg.reads O h.toAtMg.laid.planOk P5T.N0Full hk f
  have et : Meaning.Carry.toldOf cF.blocksInOrder = toldCut := (told_at_written hc).2
  rw [et] at s0
  have hlt : maskNo seatsPlanW P5T.psFull l < s.st.oracles.size := by
    have s1 : s.st.oracles.size = _ := s0
    rw [s1]
    exact mask_below_at hl
  have e3 : msgsOfChain Zp.made.proof.1 = MList := by
    rw [sends_in_scope h.toAtMg.scope h.toAtMg.laid.pub (P5J.pins_of_laid h.toAtMg.scope h.toAtMg.laid).1]
    exact MW_eq
  have hs := msgShape_at (st := s.st) hM _ hlt
  rw [e3] at hs
  obtain ⟨o, ho, a1, a2, a3, a4⟩ := mask_written_at hl
  rw [ho] at hs
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 hs
  refine ⟨y, hy, ?_, ?_, ?_, ?_⟩
  · rw [ey]; exact a1
  · rw [ey]; exact a2
  · show y.shape.maskCode = s.live.frame.shape.maskCode
    rw [ey, hsh, h.toAtMg.shapeAt_full]
    exact a3
  · rw [ey]; exact a4

/-- Where a state is reached without a mark of failure, the frame's group at its link is a group of the written shape. -/
theorem group_written (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) (hf : s.failed = none) {Gq : OnBytes.ReqGroup}
    (hq : (recOf s).frame.groups[(recOf s).frame.link]? = some Gq) :
    Gq ∈ (OnBytes.reqGroups shapeFull).toList := by
  obtain ⟨-, -, hsh, hg, -⟩ := facts_reached h hr hf
  have hq' : s.live.frame.groups[s.live.frame.link]? = some Gq := hq
  rw [hg, hsh, h.toAtMg.shapeAt_full] at hq'
  exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hq')

theorem some_getD {a : Array OnBytes.Code} {i : Nat} (hi : i < a.size) : a[i]? = some (a.getD i default) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

/-- **In front of a closing the test on the fold's shape says yes.** -/
theorem fold_shape (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) {B : BaseData}
    (hq : (recOf s).frame.groups[(recOf s).frame.link]? = some B.Gq)
    (hG : (recOf s).st.groups[(recOf s).frame.group]? = some B.G)
    (hcode : B.G.code = (recOf s).frame.shape.code)
    (hkh : (Own.layoutOf (recOf s).st B.G).k = B.Gq.k ∧ (Own.layoutOf (recOf s).st B.G).h = B.Gq.h) :
    Own.foldShapeFits (B.S1 (recOf s)) (B.F (recOf s)) = true := by
  obtain ⟨hI, hc, hsh, -, -⟩ := facts_reached h hr hf
  have H := shapes_reached h hl hr hf B.G hG
  have hOk : OnBytes.Means.GroupOk (recOf s).st B.G := hI.groups _ _ hG
  have hmask : B.G.maskCode = (recOf s).frame.shape.maskCode := by
    have z0 := maskCode_of_shapes (List.all_eq_true.1 written_codes.1 l (List.mem_range.2 hl)) hOk H
    show _ = s.live.frame.shape.maskCode
    rw [z0, hsh, h.toAtMg.shapeAt_full]
    rfl
  have hmem := group_written h hr hf hq
  have k1 := groups_k_pos _ hmem
  have k8 := groups_k_le _ hmem
  have h0 := groups_h_zero _ hmem
  obtain ⟨c1, c2, c3, c4⟩ := codes_written
  have ecs : (recOf s).st.codes = codesFull2 := hc.trans h.toAtMg.codes_full
  have es : (recOf s).frame.shape = shapeFull := hsh.trans h.toAtMg.shapeAt_full
  refine shape_of_parts hG hOk hcode hmask hkh (codesFull2.base.getD shapeFull.code default)
    (codesFull2.mask.getD shapeFull.maskCode default) ?_ ?_ k1 (by omega) c3 (by omega)
    (main_of_shapes H (List.all_eq_true.1 unkept_written l (List.mem_range.2 hl)))
  · rw [ecs, es]
    exact some_getD c1
  · rw [ecs, es]
    exact some_getD c2

/-- The fresh mask's two tests together. -/
theorem fold_mask_spend (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) {B : BaseData}
    (hq : (recOf s).frame.groups[(recOf s).frame.link]? = some B.Gq)
    (hm : (recOf s).frame.mask = some B.m)
    (hG : (recOf s).st.groups[(recOf s).frame.group]? = some B.G)
    (hfresh : ∀ y, (recOf s).st.oracles[B.m]? = some y → y.sampled = false ∧ y.spentAsMask = false) :
    Own.foldMaskFits (B.S1 (recOf s)) (B.F (recOf s)) B.m = true ∧
      Ground.ok (Ground.spendAsMaskL (B.S1 (recOf s)) B.m) = true := by
  obtain ⟨y, hy, m0, m1, m2, m3⟩ := mask_message h hl hr hf hm
  have hS := (OnBytes.Means.tidy4B_iff.1 ((foldFacts_reach h).tidy _ (z, s) hr hf)).members
  have h0 := groups_h_zero _ (group_written h hr hf hq)
  exact mask_of_parts hG hS hy m0 (by rw [h0, m1]; rfl) m2 m3 hfresh

/-- **In front of a closing the test on the fresh mask says yes, where its message is neither sampled nor spent.** -/
theorem fold_mask (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) {B : BaseData}
    (hq : (recOf s).frame.groups[(recOf s).frame.link]? = some B.Gq)
    (hm : (recOf s).frame.mask = some B.m)
    (hG : (recOf s).st.groups[(recOf s).frame.group]? = some B.G)
    (hfresh : ∀ y, (recOf s).st.oracles[B.m]? = some y → y.sampled = false ∧ y.spentAsMask = false) :
    Own.foldMaskFits (B.S1 (recOf s)) (B.F (recOf s)) B.m = true :=
  (fold_mask_spend h hl hr hf hq hm hG hfresh).1

/-- **In front of a closing the test on the spending of the fresh mask says yes, where its message is neither sampled nor
spent.** -/
theorem fold_spend (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) {B : BaseData}
    (hq : (recOf s).frame.groups[(recOf s).frame.link]? = some B.Gq)
    (hm : (recOf s).frame.mask = some B.m)
    (hG : (recOf s).st.groups[(recOf s).frame.group]? = some B.G)
    (hfresh : ∀ y, (recOf s).st.oracles[B.m]? = some y → y.sampled = false ∧ y.spentAsMask = false) :
    Ground.ok (Ground.spendAsMaskL (B.S1 (recOf s)) B.m) = true :=
  (fold_mask_spend h hl hr hf hq hm hG hfresh).2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.mask_no_reached
#print axioms ProofFile.Honest.K10.mask_message
#print axioms ProofFile.Honest.K10.group_written
#print axioms ProofFile.Honest.K10.some_getD
#print axioms ProofFile.Honest.K10.fold_shape
#print axioms ProofFile.Honest.K10.fold_mask_spend
#print axioms ProofFile.Honest.K10.fold_mask
#print axioms ProofFile.Honest.K10.fold_spend
