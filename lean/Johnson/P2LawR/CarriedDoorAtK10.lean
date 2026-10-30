-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/CarriedDoorAtK10.lean: TWO NAMED PREMISES OF THE LAW ON K10's CARRIED
  ROWS AT THE CONSTANT (hCar_paid, Johnson/Desc/First/Link/Law/HCarPaid.lean): hDoor AND hGf, AT
  EVERY LINK l < 25, FROM THE ONE HEAD (P5J.AtMgA) AT o := OnBytes.secondHashFunction AND WHAT STANDS IN
  XK h l: the table's promise at ixK10 l, "reached" there, no mark. XK's three conjuncts are
  written out as three premises (XK: Johnson/P5J/K10PieceOfAsks.lean, which this file does not
  import). A joining.
  The test groupK10B asks that the l-th
  group IS THERE ("any", not "all").

THE NAMES.
recAll_wrK: RecAll passes through a yes of closeFrame, at any entries and rounds,
  and K10's writing (closing_rec's own proof, at wrK). RecAll: Johnson/Goal/Meaning/RecAll.lean.
step_wrK: "statement and book in step" passes likewise (closeFrame_size, putRec_core).
door_of_close: AT LETTERS: RecAll · in step · noticesOkB · the state stands inside an open link · a
  yes of closeFrame ⊢ both halves of hDoor at wrK s f' S'.
hDoor_at: **hDoor, to the letter behind XK's three conjuncts.**
link_of_stand: a state that stands inside an open link has a link's part.
placeK10B, place_k10_all, place_k10: a closed fact on the written list of places IM.placesW, by
  Lean's kernel: at ixK10 l stands a place of link l at a piece up to which FoldFacts.frameIs
  gives the frame's link.
groupK10B, group_k10_all, group_k10: a closed fact at the written shape, by Lean's kernel: at each l
  < 25 the shape's list of groups HAS an l-th group, and it has the k and h of the written table's
  row l (gsAt l).
link_in_front: in front of K10's place of link l the live frame's link is l
  (frameIs_paid, Johnson/IMR/FramePaid.lean).
hGf_at: **hGf, to the letter behind XK's three conjuncts.**

Limits. The promise is a premise. NO MEMBER. hDoor's first half is free where the way in does not
  answer: it does not say that a front is there. hGf is an implication: where the state's frame had
  no group at its link it would say nothing. THAT placeK10B | groupK10B CAN SAY FALSE IS SHOWN BY NO
  LINE HERE: negative lines are left to other files. The full size alone. At OnBytes.secondHashFunction alone.
  It leans on the door's issue 2. A raised limit stands in this file (maxRecDepth 100000). Nothing
  on soundness.
-/
import Johnson.P2LawR.SwitchDoorStand
import Johnson.P2LawR.SwitchNoticesWritten
import Johnson.Goal.Meaning.RecK10
import Johnson.Goal.Meaning.SizeSeated
import Johnson.Goal.Meaning.CoreSeated
import Johnson.IMR.FramePaid
import Johnson.IMR.AtReach
import Johnson.IMR.RootsWhole
import Johnson.IMR.PlanOkFlat
import Johnson.LPFE1R.RowPubAt
import Johnson.ToldDescR.SmpWalkOpen
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.P2Notices
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Params (ReqShape)
open OnBytes.Maker (WholeD)
open Meaning.K2 (RecAll FramePub recAll_putLive closeFrame_all closeFrame_size putRec_core)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart standOf)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.First.K2Hands (shW written_in_scope)
open VerifiableInference.Desc.First.Close (closeFrame rdK rdBK wrK)
open VerifiableInference.Desc.LinkJoin (gsAt)
open _root_.Tw.K2 (switchNotices)
open _root_.Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open LPFK10 (ixK10)
open P5J

/-- **RecAll passes through a yes of closeFrame and K10's writing.** -/
theorem recAll_wrK {cs : Codes} {sh : ReqShape} {s : First.S} {f' : ReqFrame} {S' : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} (R : RecAll cs sh s)
    (hc : closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2 es rs = .ok (f', S')) :
    RecAll cs sh (wrK s f' S') := by
  obtain ⟨a1, a2, -, -, a5, a6, a7, a8, a9⟩ := closeFrame_all hc
  have hf : FramePub sh f' := ⟨a1.trans R.live.shape, a2.trans R.live.groups, a9.trans a8.symm,
    Or.inr ⟨a6.trans (congrArg (·.code) R.live.shape),
      a7.trans (congrArg (·.maskCode) R.live.shape), a8⟩⟩
  have R1 := recAll_putLive (c := { s.live with frame := f' }) R hf
  exact ⟨a5.trans R.codes, R1.frames, R.ok⟩

/-- "Statement and book in step" passes likewise. -/
theorem step_wrK {s : First.S} {f' : ReqFrame} {S' : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} (hs : s.st.oracles.size = s.book.place.size)
    (hc : closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2 es rs = .ok (f', S')) :
    (wrK s f' S').st.oracles.size = (wrK s f' S').book.place.size := by
  have e1 : (wrK s f' S').book = s.book := (putRec_core s _).1
  have e2 : S'.oracles.size = s.st.oracles.size := closeFrame_size hc
  rw [e1]
  exact e2.trans hs

/-- **Both halves of hDoor, at letters.** -/
theorem door_of_close {cs : Codes} {sh : ReqShape} {Z : ProofFile.Pub} {m : ℕ} {s : First.S}
    {f' : ReqFrame} {S' : Statement} {es : List Fmt.Entry} {rs : List Fmt.RoundView} {sub : ModelPart}
    (R : RecAll cs sh s) (hs : s.st.oracles.size = s.book.place.size)
    (K : noticesOkB cs sh = true) (hst : standOf s = .link sub)
    (hc : closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2 es rs = .ok (f', S')) :
    (∀ t, doorZ Z m (wrK s f' S') = some t → (ProofFile.pAtK2 Z m).stands = .head →
      ∀ b, (wrK s f' S').here ≠ .head b) ∧
    ∀ t fx, doorZ Z m (wrK s f' S') = some t → First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx →
      ∃ Bk, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree fx.st t.book t.roots
        (switchNotices fx.T fx.others) = some Bk := by
  have hst' : standOf (wrK s f' S') = .link sub := (First.putRec_standOf _ _).trans hst
  exact ⟨fun t hd => hH_of_stand hst' hd,
    book_at_door_stand (recAll_wrK R hc) (step_wrK hs hc) K hst'⟩

/-- A state that stands inside an open link has a link's part. -/
theorem link_of_stand {s : First.S} {sub : ModelPart} (h : standOf s = .link sub) :
    ∃ L, s.link? = some L := by
  cases e : s.here with
  | between => simp [standOf, e] at h
  | lay a => exact ⟨a.L, by simp [First.S.link?, e]⟩
  | att a => exact ⟨a.L, by simp [First.S.link?, e]⟩
  | head a =>
    cases ho : a.opened with
    | false => simp [standOf, First.S.inLink, First.S.fork?, e, ho] at h
    | true => exact ⟨a.L, by simp [First.S.link?, e, ho]⟩
  | fin a => simp [standOf, e] at h
  | mem a => simp [standOf, e] at h

/-- The test on the written list of places IM.placesW (Johnson/IMR/WrittenList.lean). -/
def placeK10B : Bool :=
  (List.range 25).all fun l =>
    (IM.placesW[ixK10 l]?).any fun p =>
      p.link == some l && decide (p.piece ≤ 11 + 2 * Meaning.K2.shiftW l)

/-- **It accepts**: by Lean's kernel. -/
theorem place_k10_all : placeK10B = true := by decide +kernel

theorem place_k10 {l : ℕ} (hl : l < 25) : ∃ p, IM.placesW[ixK10 l]? = some p ∧
    p.link = some l ∧ p.piece ≤ 11 + 2 * Meaning.K2.shiftW l := by
  have k := List.all_eq_true.1 place_k10_all l (List.mem_range.2 hl)
  obtain ⟨p, hp, hq⟩ := (Option.any_eq_true _ _).1 k
  obtain ⟨q1, q2⟩ := Bool.and_eq_true_iff.1 hq
  exact ⟨p, hp, eq_of_beq q1, of_decide_eq_true q2⟩

/-- The test at the written shape. -/
def groupK10B : Bool :=
  (List.range 25).all fun l =>
    ((reqGroups shW)[l]?).any fun G => G.k == (gsAt l).k && G.h == (gsAt l).h

/-- **It accepts**: by Lean's kernel. -/
theorem group_k10_all : groupK10B = true := by decide +kernel

theorem group_k10 {l : ℕ} (hl : l < 25) {G : ReqGroup} (h : (reqGroups shW)[l]? = some G) :
    G.k = (gsAt l).k ∧ G.h = (gsAt l).h := by
  have k := List.all_eq_true.1 group_k10_all l (List.mem_range.2 hl)
  rw [h] at k
  obtain ⟨q1, q2⟩ := Bool.and_eq_true_iff.1 (show (G.k == (gsAt l).k && G.h == (gsAt l).h) = true
    from k)
  exact ⟨eq_of_beq q1, eq_of_beq q2⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- What "reached" and the head give at a state without a mark, at a border k ≤ 353. -/
theorem rec_step_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : ℕ} {a : (ProofFile.InstPub × TS) ×
                  (Frame.E (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)).Str}
    (hr : h.toAtMg.rch k a) (hm : ¬ a.1.2.failed ≠ none) (hk : k ≤ 353) :
    RecAll Zp.first.codes Zp.first.shape a.1.2 ∧
      a.1.2.st.oracles.size = a.1.2.book.place.size := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hu : a.1.2.failed = none := not_not.1 hm
  have e : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (a.1.1, a.1.2) := hr.1
  have e' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (a.1.1, a.1.2) := reach_raw e
  exact ⟨Meaning.K2.recAll_all h.scope h.reads O (ToldDesc.open_planOk O h.laid.planOk) e' hu,
    (Meaning.K2.bookHas_reached O e'
      (by rw [Meaning.Carry.front_len h.scope h.reads O]; exact hk)).symm⟩

theorem ix_le' {l : ℕ} (hl : l < 25) : ixK10 l ≤ 353 := by
  have k : ∀ l ∈ List.range 25, ixK10 l ≤ 353 := by decide
  exact k l (List.mem_range.2 hl)

/-- **hDoor, BEHIND XK's THREE CONJUNCTS.** -/
theorem hDoor_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {a : (ProofFile.InstPub × TS) ×
      (Frame.E (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)).Str}
    (ha : onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) a)
    (hr : h.toAtMg.rch (ixK10 l) a) (hm : ¬ a.1.2.failed ≠ none) {s' : TS}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView}
    (hc : closeFrame (rdK a.1.2).1 (rdK a.1.2).2.1 (rdK a.1.2).2.2 es rs = .ok (rdBK s'))
    (he : s' = wrK a.1.2 (rdBK s').1 (rdBK s').2) {m : ℕ} :
    (∀ t, doorZ Zp m s' = some t → (ProofFile.pAtK2 Zp m).stands = .head → ∀ b, s'.here ≠ .head b) ∧
    ∀ t fx, doorZ Zp m s' = some t → First.K2.frontAt (ProofFile.pAtK2 Zp m) t = some fx →
      ∃ Bk, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Zp m)).firstTree fx.st t.book t.roots
        (switchNotices fx.T fx.others) = some Bk := by
  have RS := rec_step_at h hr hm (ix_le' hl)
  have K := notices_in_scope h.scope h.laid.pub
    (VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true]))
  have st := stand_in_front (At.N Zp cF) (mgAtAll h) (fun a => a) hl a ha hm
  have key := st.elim fun sub hst =>
    door_of_close (Z := Zp) (m := m) (f' := (rdBK s').1) (S' := (rdBK s').2) RS.1 RS.2 K hst hc
  rw [← he] at key
  exact key

/-- In front of K10's place of link l the live frame's link is l. -/
theorem link_in_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {a : (ProofFile.InstPub × TS) ×
      (Frame.E (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)).Str}
    (ha : onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) a)
    (hr : h.toAtMg.rch (ixK10 l) a) (hm : ¬ a.1.2.failed ≠ none) :
    a.1.2.live.frame.link = l := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hu : a.1.2.failed = none := not_not.1 hm
  have e : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (ixK10 l) (a.1.1, a.1.2) := hr.1
  have e' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (ixK10 l) (a.1.1, a.1.2) := reach_raw e
  obtain ⟨sub, hst⟩ := stand_in_front (At.N Zp cF) (mgAtAll h) (fun a => a) hl a ha hm
  obtain ⟨L, hL⟩ := link_of_stand hst
  obtain ⟨p, hp, hpl, hpc⟩ := place_k10 hl
  have hRch : ∀ k (b : ProofFile.InstPub × TS), Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k b → ∃ rs cols r q,
      foldBlocks 0 (cF.blocksInOrder.take k) (ProofFile.startS Zp b.1) rs cols = .ok (b.2, r, q) := by
    intro k b hb
    obtain ⟨-, rs, cols, f⟩ := hb.fold
    exact ⟨rs, cols, [], [], f⟩
  have F := Meaning.K2.frameIs_paid h.scope h.reads O (IM.blocksOk_of_planOk O h.laid.planOk)
    (At.N Zp cF) #[] (fun k b => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k b) (fun b => b) hRch (ixK10 l)
    (a.1.1, a.1.2) p l L e' hu hp hpl hL
  have e1 : a.1.2.live = L.check := by
    unfold First.S.live
    rw [hL]
  rw [e1]
  exact (F.2.2.2 hpc).1

/-- **hGf, BEHIND XK's THREE CONJUNCTS.** -/
theorem hGf_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {a : (ProofFile.InstPub × TS) ×
      (Frame.E (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)).Str}
    (ha : onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) a)
    (hr : h.toAtMg.rch (ixK10 l) a) (hm : ¬ a.1.2.failed ≠ none) :
    ∀ Gf, (rdK a.1.2).2.1.groups[(rdK a.1.2).2.1.link]? = some Gf →
      Gf.k = (gsAt l).k ∧ Gf.h = (gsAt l).h := by
  intro Gf hG
  have RS := rec_step_at h hr hm (ix_le' hl)
  have e1 : a.1.2.live.frame.groups = reqGroups Zp.first.shape := RS.1.live.groups
  have e2 : a.1.2.live.frame.link = l := link_in_front h hl ha hr hm
  have e3 : Zp.first.shape = shW := (written_in_scope h.scope h.laid.pub
    (VerifiableInference.PlanWritten.pinnedAt_of_row
      (by rw [h.toAtMg.pins.1, Bool.or_true]))).2.1
  have hG0 : a.1.2.live.frame.groups[a.1.2.live.frame.link]? = some Gf := hG
  rw [e1, e2, e3] at hG0
  exact group_k10 hl hG0

end VerifiableInference.Desc.P2Notices

#print axioms VerifiableInference.Desc.P2Notices.recAll_wrK
#print axioms VerifiableInference.Desc.P2Notices.step_wrK
#print axioms VerifiableInference.Desc.P2Notices.door_of_close
#print axioms VerifiableInference.Desc.P2Notices.link_of_stand
#print axioms VerifiableInference.Desc.P2Notices.place_k10_all
#print axioms VerifiableInference.Desc.P2Notices.place_k10
#print axioms VerifiableInference.Desc.P2Notices.group_k10_all
#print axioms VerifiableInference.Desc.P2Notices.group_k10
#print axioms VerifiableInference.Desc.P2Notices.rec_step_at
#print axioms VerifiableInference.Desc.P2Notices.ix_le'
#print axioms VerifiableInference.Desc.P2Notices.hDoor_at
#print axioms VerifiableInference.Desc.P2Notices.link_in_front
#print axioms VerifiableInference.Desc.P2Notices.hGf_at
