-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/FrameFacts.lean: the closing of a segment (K10): what the record in front of the
closing says of the live frame, at a state that the first chain's own blocks reach. These are eleven of the twenty fields
of `CloseBase` (Johnson/Desc/K10/Honest/Base.lean), each stated without any acceptance of the closing.

With R := `K9.recOf s`, at the border 14 l + `IM.nAt l` + 5, l < 25, at a reached state without a mark of failure:
  `frame_next`      R.frame.next is `laterOrClose`
  `frame_link`      the frame's shape has a link at R.frame.link, and the frame's moment is that link's count of moments
  `frame_group`     the frame has a request's group at R.frame.link
  `frame_there`     the statement has a group at the frame's group number
  `frame_mask`      the frame names a mask
  `frame_stretch`   under `Tied`: the plan's k is the request's group's k
  `frame_code`      the statement's group has the main code of the frame's shape
  `frame_power`     the message length of the mask code of the frame's shape is a power of two
  `frame_kh`        the group's layout has the request's group's k and h
  `frame_bits`      the main table has at most 63 index bits
  `frame_owed`      nothing is owed. This one reads the table's promise, so it stands at the thread's invariant (or,
                    as `frame_owed_of_shape`, at the promise's book-keeping test)

Limits. Every statement is an implication from the head `P5J.AtMgA` and from being reached; whether the head can be had at
any files is not shown here. The full size and the older hash alone. The other fields of `CloseBase` are not spoken of.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AtReach
import Johnson.Desc.ProofFile.Honest.K10.Xch.Height
import Johnson.Desc.ProofFile.Honest.K10.Xch.Says
import Johnson.Desc.First.Close.Law.ReqKept
import Johnson.P5T.ShapeFacts
import Johnson.IMR.FrameEntry
import Johnson.IMR.HeadMembers
import Johnson.IMR.MaskNamed
import Johnson.IMR.MaskHeadNamed
import Johnson.IMR.MaskZeroNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S Item onAt pubSets shapeAt mayWait momentAt shiftAt)
open VerifiableInference.Desc.First.Close (Par ShapesAre kbAt noK10 codesZero written_codes layout_full real_full)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.G (linksFullLit codesFull2)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Means (InOrder GroupOk)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## 1 Closed facts at the full size -/

/-- The test on the table of places at the closing of segment l: the place is segment l's, it stands early enough for
the frame's link to be named, the next moment there is 3, and no count of rows may wait there. -/
def frameB (l : Nat) : Bool :=
  (P5J.At.ps[LPFK10.ixK10 l]?).any fun p =>
    p.link == some l && decide (p.piece ≤ 11 + 2 * shiftAt P5J.At.links l) &&
      momentAt (shiftAt P5J.At.links l) p.piece == 3 && !mayWait P5J.At.links p

set_option maxRecDepth 1000000 in
/-- The test accepts at all 25 closings: by Lean's kernel. -/
theorem frameB_all : (List.range 25).all frameB = true := by decide +kernel

/-- The place of the closing of segment l. -/
theorem frame_place {l : Nat} (hl : l < 25) :
    ∃ p, P5J.At.ps[14 * l + IM.nAt l + 5]? = some p ∧ p.link = some l ∧
      p.piece ≤ 11 + 2 * shiftAt P5J.At.links l ∧ momentAt (shiftAt P5J.At.links l) p.piece = 3 ∧
      mayWait P5J.At.links p = false := by
  have e : LPFK10.ixK10 l = 14 * l + IM.nAt l + 5 := YesFree.number_is l
  have t : frameB l = true := List.all_eq_true.1 frameB_all l (List.mem_range.2 hl)
  unfold frameB at t
  rw [e] at t
  cases hp : P5J.At.ps[14 * l + IM.nAt l + 5]? with
  | none =>
    rw [hp] at t
    simp at t
  | some p =>
    rw [hp] at t
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at t
    exact ⟨p, rfl, t.1.1.1, t.1.1.2, t.1.2, t.2⟩

set_option maxRecDepth 1000000 in
/-- The written shape's request has more than 25 groups. -/
theorem frame_groups_size : 25 < (OnBytes.reqGroups shapeFull).size := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written shape's mask code is one of the written codes. -/
theorem frame_mask_size : shapeFull.maskCode < codesFull2.mask.size := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written list of each of the 25 links is among the written lists. -/
theorem frame_lo_mem {l : Nat} (hl : l < 25) : linksFullLit.getD l [] ∈ linksFullLit := by
  have hlen : 25 ≤ linksFullLit.length := by decide +kernel
  have hlt : l < linksFullLit.length := by omega
  have e : linksFullLit.getD l [] = linksFullLit[l] := by
    simp [List.getD_eq_getElem?_getD, hlt]
  rw [e]
  exact List.getElem_mem hlt

/-! ## 2 At a reached state -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- In front of the closing of segment l, link l is open, its frame names group l, and the statement has that group. -/
theorem frame_open (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) :
    ∃ (L : OnBytes.Model.LinkCtx) (G : OnBytes.Group), s.link? = some L ∧ L.link = l ∧
      L.check.frame.group = l ∧ s.st.groups[l]? = some G := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · have e : 14 * l + IM.nAt l + 5 = 14 * l + 3 + 9 := by
      have : IM.nAt l = 7 := if_neg (by omega)
      omega
    rw [e] at hr
    obtain ⟨-, rs, cols, f⟩ := hr.fold
    obtain ⟨L, G, -, hL, e2, e3, hG, -⟩ :=
      _root_.Meaning.K2.members_at h.toAtMg.scope h.toAtMg.reads O h24 (Nat.le_refl 9) f
    exact ⟨L, G, hL, e2, e3, hG⟩
  · obtain rfl : l = 24 := by omega
    have e : 14 * 24 + IM.nAt 24 + 5 = 340 + 10 := rfl
    rw [e] at hr
    obtain ⟨-, rs, cols, f⟩ := hr.fold
    obtain ⟨L, G, -, hL, e2, e3, hG, -⟩ :=
      _root_.Meaning.K2.members_head h.toAtMg.scope h.toAtMg.reads O (Nat.le_refl 10) f
    exact ⟨L, G, hL, e2, e3, hG⟩

/-- In front of the closing of segment l, the open link's frame stands at link l, group l, moment 3, and what comes next
is "later or close". -/
theorem frame_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    ∃ L : OnBytes.Model.LinkCtx, s.link? = some L ∧ L.check.frame.group = l ∧ L.check.frame.link = l ∧
      L.check.frame.next = .laterOrClose ∧ L.check.frame.moment = 3 := by
  obtain ⟨L, G, hL, -, e3, -⟩ := frame_open h hl hr
  obtain ⟨p, hp, hk, hpc, hm, -⟩ := frame_place hl
  obtain ⟨n1, -, -, n2⟩ := (foldFacts_reach h).frameIs _ (z, s) p l L hr hf hp hk hL
  obtain ⟨n3, n4⟩ := n2 hpc
  exact ⟨L, hL, e3, n3, n4, n1.trans hm⟩

/-- The same of the record. -/
theorem frame_rec (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    (recOf s).frame.group = l ∧ (recOf s).frame.link = l ∧ (recOf s).frame.next = .laterOrClose ∧
      (recOf s).frame.moment = 3 := by
  obtain ⟨L, hL, e1, e2, e3, e4⟩ := frame_at h hl hr hf
  rw [frame_of_open hL]
  exact ⟨e1, e2, e3, e4⟩

/-- A link that `Tied` names is one of the 25. -/
theorem frame_lt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} {p : K9.Where} {Qc : Par}
    {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l p Qc blk) : l < 25 := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  exact link_lt h (List.getElem?_eq_some_iff.1 hblk).1

/-- The lot's place at a link that `Tied` names has that link's number. -/
theorem frame_plink (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} {p : K9.Where} {Qc : Par}
    {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l p Qc blk) : p.link = l := by
  have hl := frame_lt h Td
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  obtain ⟨_, p', _, hp', _, _, hlk, _⟩ :=
    IM.k9_alone O l (IM.subAt l) (IM.subs_scope h.toAtMg.scope h.toAtMg.reads O l hl)
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans Td.1)
  exact hlk

/-- The record's frame's groups are those of the written shape. -/
theorem frame_groups_eq (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) (hf : s.failed = none) :
    (recOf s).frame.groups = OnBytes.reqGroups shapeFull := by
  obtain ⟨-, -, hsh, hg, -⟩ := facts_reached h hr hf
  show s.live.frame.groups = _
  rw [hg, hsh, h.toAtMg.shapeAt_full]

/-- **What comes next in front of the closing is "later or close".** -/
theorem frame_next (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    (recOf s).frame.next = .laterOrClose :=
  (frame_rec h hl hr hf).2.2.1

/-- **The frame's shape has a link at the frame's link, and the frame's moment is that link's count of moments.** -/
theorem frame_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    ∃ L, (recOf s).frame.shape.link[(recOf s).frame.link]? = some L ∧
      (recOf s).frame.moment = OnBytes.reqMoments L := by
  obtain ⟨-, e1, -, e3⟩ := frame_rec h hl hr hf
  obtain ⟨-, -, hsh, -, -⟩ := facts_reached h hr hf
  have hs : (recOf s).frame.shape = shapeFull := hsh.trans h.toAtMg.shapeAt_full
  have hlen : shapeFull.link.length = 25 := congrArg Prod.fst P5T.shape_ok
  have hall : (shapeFull.link.all fun L => OnBytes.reqMoments L == 3) = true :=
    congrArg (fun y => y.2.1) P5T.shape_counts
  have hlt : l < shapeFull.link.length := by omega
  rw [hs, e1, e3]
  refine ⟨shapeFull.link[l], List.getElem?_eq_getElem hlt, ?_⟩
  have t : (OnBytes.reqMoments shapeFull.link[l] == 3) = true :=
    List.all_eq_true.1 hall _ (List.getElem_mem hlt)
  exact (beq_iff_eq.1 t).symm

/-- **The frame has a request's group at the frame's link.** -/
theorem frame_group (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    ∃ Gq, (recOf s).frame.groups[(recOf s).frame.link]? = some Gq := by
  have hlt : l < (OnBytes.reqGroups shapeFull).size := by
    have := frame_groups_size
    omega
  rw [frame_groups_eq h hr hf, (frame_rec h hl hr hf).2.1]
  exact ⟨_, Array.getElem?_eq_getElem hlt⟩

/-- **The statement has a group at the frame's group number.** -/
theorem frame_there (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) :
    ∃ G, (recOf s).st.groups[(recOf s).frame.group]? = some G := by
  obtain ⟨L, G, hL, -, e3, hG⟩ := frame_open h hl hr
  refine ⟨G, ?_⟩
  rw [frame_of_open hL, e3]
  exact hG

/-- **The frame names a mask.** -/
theorem frame_mask (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) :
    ∃ mk, (recOf s).frame.mask = some mk := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  rcases Nat.eq_zero_or_pos l with rfl | h1
  · have e : 14 * 0 + IM.nAt 0 + 5 = 3 + 9 := rfl
    rw [e] at hr
    obtain ⟨-, rs, cols, f⟩ := hr.fold
    obtain ⟨L, hL, -, hm⟩ :=
      _root_.Meaning.K2.mask_zero_named h.toAtMg.scope h.toAtMg.reads O (Nat.le_refl 9) f
    rw [frame_of_open hL]
    exact ⟨_, hm⟩
  · rcases Nat.lt_or_ge l 24 with h24 | h24
    · have e : 14 * l + IM.nAt l + 5 = 14 * l + 3 + 9 := by
        have : IM.nAt l = 7 := if_neg (by omega)
        omega
      rw [e] at hr
      obtain ⟨-, rs, cols, f⟩ := hr.fold
      obtain ⟨_, _, _, L, _, hL, _, hm⟩ :=
        _root_.Meaning.K2.mask_named h.toAtMg.scope h.toAtMg.reads O h1 h24 (Nat.le_refl 9) f
      rw [frame_of_open hL]
      exact ⟨_, hm⟩
    · obtain rfl : l = 24 := by omega
      have e : 14 * 24 + IM.nAt 24 + 5 = 340 + 10 := rfl
      rw [e] at hr
      obtain ⟨-, rs, cols, f⟩ := hr.fold
      obtain ⟨_, _, _, L, _, hL, _, hm⟩ :=
        _root_.Meaning.K2.mask_head_named h.toAtMg.scope h.toAtMg.reads O (Nat.le_refl 10) f
      rw [frame_of_open hL]
      exact ⟨_, hm⟩

/-- **The plan's k is the k of the request's group at the frame's link.** -/
theorem frame_stretch (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} {p : K9.Where} {Qc : Par}
    {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l p Qc blk) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    ∀ Gq, (recOf s).frame.groups[(recOf s).frame.link]? = some Gq → Qc.k = Gq.k := by
  intro Gq hq
  have hl := frame_lt h Td
  rw [frame_groups_eq h hr hf, (frame_rec h hl hr hf).2.1] at hq
  obtain ⟨Gr, hG, ek, -⟩ := k10Par_group Td.2.1
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.toAtMg.laid.pub
  rw [first_frame_groups hZ, h.toAtMg.shape_full, frame_plink h Td] at hG
  rw [ek, Option.some.inj (hG.symm.trans hq)]

/-- Where the test `codesZero` accepts a written list, a group in order that holds that list's members has the main code
0. The twin of `maskCode_of_shapes` (Xch/Mask.lean). -/
theorem code_of_shapes {T : OnBytes.Statement} {G : OnBytes.Group} {lo : List (OnBytes.OracleShape × Nat)}
    {kb : Fin lo.length → Bool} {no : Fin lo.length → Nat}
    (hz : codesZero lo = true) (hOk : GroupOk T G) (H : ShapesAre T G lo kb no) : G.code = 0 := by
  unfold codesZero at hz
  obtain ⟨h1, -⟩ := Bool.and_eq_true _ _ ▸ hz
  obtain ⟨i, hi, ci⟩ := List.any_eq_true.1 h1
  have ci' : (lo.get i).1.code = 0 := by simpa using ci
  have mi : (lo.get i).1.mainRows ≠ 0 := by
    unfold VerifiableInference.Desc.First.Close.membersOf at hi
    simpa using hi
  have ini : no i ∈ G.members.toList := by rw [H.members]; exact List.mem_map_of_mem hi
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 (H.shape i hi)
  have h3 := hOk.mainCode (no i) ini y hy
  rw [ey] at h3
  exact (h3.resolve_left mi).symm.trans ci'

/-- **The statement's group has the main code of the frame's shape.** -/
theorem frame_code (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    ∀ G, (recOf s).st.groups[(recOf s).frame.group]? = some G → G.code = (recOf s).frame.shape.code := by
  intro G hG
  obtain ⟨hI, -, hsh, -, -⟩ := facts_reached h hr hf
  have z0 : G.code = 0 :=
    code_of_shapes (List.all_eq_true.1 written_codes.1 l (List.mem_range.2 hl)) (hI.groups _ G hG)
      (shapes_reached h hl hr hf G hG)
  show G.code = s.live.frame.shape.code
  rw [z0, hsh, h.toAtMg.shapeAt_full]
  rfl

/-- **The message length of the mask code of the frame's shape is a power of two.** -/
theorem frame_power (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) (hf : s.failed = none) :
    ((recOf s).st.codes.mask.getD (recOf s).frame.shape.maskCode default).ell =
      2 ^ OnBytes.ceilLog2 ((recOf s).st.codes.mask.getD (recOf s).frame.shape.maskCode default).ell := by
  obtain ⟨-, hc, hsh, -, -⟩ := facts_reached h hr hf
  have hC : s.st.codes.lengthsOk = true := by
    rw [hc]
    exact h.three.1
  have hj : s.live.frame.shape.maskCode < s.st.codes.mask.size := by
    rw [hc, hsh, h.toAtMg.codes_full, h.toAtMg.shapeAt_full]
    exact frame_mask_size
  exact YesFree.mask_pow hC hj

/-- **The group's layout has the k and the h of the request's group at the frame's link.** -/
theorem frame_kh (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    ∀ G Gq, (recOf s).st.groups[(recOf s).frame.group]? = some G →
      (recOf s).frame.groups[(recOf s).frame.link]? = some Gq →
      (Own.layoutOf (recOf s).st G).k = Gq.k ∧ (Own.layoutOf (recOf s).st G).h = Gq.h := by
  intro G Gq hG hq
  obtain ⟨L, h1, -, h2, h3, -, -⟩ := layout_full (frame_lo_mem hl) hG (shapes_reached h hl hr hf G hG)
  have eL : Own.layoutOf (recOf s).st G = L := Option.some.inj ((Own.layout_of_group hG).symm.trans h1)
  rw [frame_groups_eq h hr hf, (frame_rec h hl hr hf).2.1] at hq
  have hh : Gq.h = 0 := groups_h_zero Gq (Array.mem_toList_iff.2 (Array.mem_of_getElem? hq))
  have hk : L.k = Gq.k := by
    rw [h3, (real_full l hl).2.1, Array.getD_eq_getD_getElem?, hq]
    rfl
  rw [eL]
  exact ⟨hk, h2.trans hh.symm⟩

/-- **The group's main table has at most 63 index bits.** -/
theorem frame_bits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) :
    ∀ G, (recOf s).st.groups[(recOf s).frame.group]? = some G →
      (Own.layoutOf (recOf s).st G).k + (Own.layoutOf (recOf s).st G).logEll ≤ 63 := by
  intro G hG
  obtain ⟨Gq, hq⟩ := frame_group h hl hr hf
  have kh := (frame_kh h hl hr hf G Gq hG hq).1
  have hcode := frame_code h hl hr hf G hG
  obtain ⟨-, hc, hsh, -, -⟩ := facts_reached h hr hf
  rw [frame_groups_eq h hr hf, (frame_rec h hl hr hf).2.1] at hq
  have hk : Gq.k ≤ 8 := groups_k_le Gq (Array.mem_toList_iff.2 (Array.mem_of_getElem? hq))
  have hle : (Own.layoutOf (recOf s).st G).logEll ≤ 55 := by
    show ((recOf s).st.codes.base.getD G.code default).logEll ≤ 55
    rw [hcode]
    show (s.st.codes.base.getD s.live.frame.shape.code default).logEll ≤ 55
    rw [hc, hsh, h.toAtMg.codes_full, h.toAtMg.shapeAt_full]
    exact logEll_full
  omega

end

/-! ## 3 Nothing is owed -/

/-- The table's promise at a border, at a state without a mark of failure, gives the book-keeping test. -/
theorem frame_shape_of_onAt {Pz W : Type} {N : VerifiableInference.Desc.First.Numbers}
    {Mg : VerifiableInference.Desc.First.Meaning Pz W} {links : List VerifiableInference.Desc.First.ModelPart}
    {p : Option Place} {O : List Item} {Q : List VerifiableInference.Desc.First.Pub} {a : Pz × S} {y : Strs}
    (h : onAt N Mg links p O Q a y) (hf : a.2.failed = none) : shapeAt links p a.2 = true := by
  rcases h.2 with c | c
  · exact absurd hf c
  · have e := c.1
    simp only [Bool.and_eq_true] at e
    exact e.1.1.1.1.1

/-- Where the book-keeping test holds at a place at which no count may wait, nothing is owed. -/
theorem frame_owed_of_shape {links : List VerifiableInference.Desc.First.ModelPart} {p : Place} {s : S}
    (hs : shapeAt links (some p) s = true) (hw : mayWait links p = false) : (recOf s).owed = none := by
  unfold shapeAt at hs
  simp only [Bool.and_eq_true, Bool.or_eq_true, hw, Bool.false_eq_true, or_false] at hs
  have hn := hs.1.2
  unfold VerifiableInference.Desc.First.S.noneWaits at hn
  show K9.owedOf s = none
  unfold K9.owedOf
  cases e : s.rowsOwed with
  | none => rfl
  | some q =>
    rw [e] at hn
    have : q = 0 := by simpa using hn
    subst this
    rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
variable (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head; the option is explained in the head of Xch/BaseAt.lean.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **Wherever the invariant holds at the border before the closing of segment l, nothing is owed.** -/
theorem frame_owed {l : Nat} (hl : l < 25) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) : (recOf s).owed = none := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hP, -, -, -, -⟩ := hT'
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 hP.1
  have hF : (𝕋).formP (14 * l + IM.nAt l + 5) (m.st.input.x.pub, s) := hP.2
  have hon : onAt (P5J.At.N Zp cF) (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.At.links
      P5J.At.ps[14 * l + IM.nAt l + 5]? (P5J.oAt (14 * l + IM.nAt l + 5))
      (((pubSets (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more P5J.At.links
        P5J.At.ps)[14 * l + IM.nAt l + 5]?).getD []) (m.st.input.x.pub, s) noStrs := hF
  have hs := frame_shape_of_onAt hon hf
  obtain ⟨p, hp, -, -, -, hw⟩ := frame_place hl
  rw [hp] at hs
  exact frame_owed_of_shape hs hw

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.frameB_all
#print axioms ProofFile.Honest.K10.frame_place
#print axioms ProofFile.Honest.K10.frame_groups_size
#print axioms ProofFile.Honest.K10.frame_mask_size
#print axioms ProofFile.Honest.K10.frame_lo_mem
#print axioms ProofFile.Honest.K10.frame_open
#print axioms ProofFile.Honest.K10.frame_at
#print axioms ProofFile.Honest.K10.frame_rec
#print axioms ProofFile.Honest.K10.frame_lt
#print axioms ProofFile.Honest.K10.frame_plink
#print axioms ProofFile.Honest.K10.frame_groups_eq
#print axioms ProofFile.Honest.K10.frame_next
#print axioms ProofFile.Honest.K10.frame_link
#print axioms ProofFile.Honest.K10.frame_group
#print axioms ProofFile.Honest.K10.frame_there
#print axioms ProofFile.Honest.K10.frame_mask
#print axioms ProofFile.Honest.K10.frame_shape_of_onAt
#print axioms ProofFile.Honest.K10.frame_owed_of_shape
#print axioms ProofFile.Honest.K10.frame_stretch
#print axioms ProofFile.Honest.K10.code_of_shapes
#print axioms ProofFile.Honest.K10.frame_code
#print axioms ProofFile.Honest.K10.frame_power
#print axioms ProofFile.Honest.K10.frame_kh
#print axioms ProofFile.Honest.K10.frame_bits
#print axioms ProofFile.Honest.K10.frame_owed
