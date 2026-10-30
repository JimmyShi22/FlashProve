-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/FreshNumbered.lean: UNDER THE HEAD's PREMISE, AT THE FRONT THAT A
CODE SWITCH's BLOCK TAKES OFF A REACHED STATE, AT ALL THREE SORTS OF THE KIND's PLACES: THE CLOSING
THAT LIES BEHIND THE CARRIED ROWS, SAID ONCE; AND OFF IT THE CLOSING FOLD's FRESH MASK: ITS NUMBER,
THAT IT IS STATED, ITS MASK ROWS, AND A WITNESS's WORDS AT IT. One definition (a sentence on the
verifier's side); statements with their proofs.

  `ClosedBehind` h l z rows T: there are a state w, reached at link l's closing kind's own
                    sub-protocol (`ixK10 l`) at the public part z, with an open segment Lw, and a
                    return u of the frame's closing at Lw's frame and w's statement, such that rows
                    are u's carried rows and T has grown out of u's statement
  `link_closedBehind` m < 23, a reached at 14 (m + 1) + 2, fx the switch's front off a's state ⊢
                    `ClosedBehind h m a.1.1 fx.f.rows a.1.2.st`
  `head_closedBehind` the like at 339, of link 23
  `fin_closedBehind` the like at 353, of link 24; fx is taken off the state behind the quiet step in
                    front
  `fresh_of_closedBehind` `ClosedBehind h l z rows T` ⊢ `rows.fresh = maskNo (P5J.At.seats Zp)
                    (P5J.At.pseats Zp) l`, it lies below the number of T's messages, and its shape
                    in T has `2 ^ rows.layout.h` mask rows
  `freshWord_of_closedBehind` THE CORE: a reached at a border without a mark, link l's closing
                    behind rows and a's statement, St with a's oracle messages, Bk a's book, b < 2 ^
                    rows.layout.h ⊢ `wordsFirst arr St Bk v rows.fresh .mask (b + j * 2 ^ ceilLog2
                    maskRows) = v.tab St.codes sh (arr (maskTree l) (maskPart l)) (maskTree l)
                    (maskPart l) true b j`, sh the message's own shape in St, maskRows its mask
                    rows: for every witness v and numbering arr
  `link_freshWord_front` that at the switch's front, m < 23
  `head_freshWord_front` at 339
  `fin_freshWord_front` at 353; the book is that of the state behind the quiet step

THE SPLIT IS NOT ENTERED. `Wit.tab` (Johnson/Desc/Sound/MsgSig.lean) reads, where `padB cs s mask
row place` (Johnson/Desc/SeatAt.lean) says yes, the seat's own component of the witness, and
elsewhere the message's. THE FOUR LAWS ON WORDS STOP IN FRONT OF THAT SPLIT: none says what sort of
entry stands at a place. Whoever goes on from here goes by cases on `padB`.

By, the library's: `closeFrame_reads` (Johnson/Desc/First/Link/Law/CloseReads.lean): the carried
rows' fresh mask is the frame's mask · `AtMg.mask_all` (Johnson/P5J/MaskAtMgAll.lean), `ixK10_is`
(Johnson/P5J/K10HXAt.lean): that mask is `maskNo …` · `closeFrame_sizes`
(Johnson/Desc/First/Link/Law/CarriedSizes.lean): the message is there · `layFits_of_close`, field
`fresh` (Returns/ClosedReached.lean): the mask rows · `AtMg.mask_letters_at`
(Johnson/P5J/MaskLettersAtMg.lean): the written plan's place of that number · `closing_behind_laid`
(Returns/SeatsWalk.lean), `closing_behind_cleared` (Returns/HeadSegment.lean), `front_pin_link`,
`front_pin_head` (Johnson/IMR/FrontPin.lean), `front_nums_head` (Johnson/IMR/HeadFront.lean),
`front_nums_fin` (Johnson/IMR/FinCount.lean), `grows_front` (Johnson/IMR/GrowsFlat.lean),
`finishFrontQ_book` (Johnson/Top/H0/Tw/K2C/BookKept.lean). And: `seat_reached`,
`link_member_stated`, `head_member_stated`, `fin_member_stated` (Returns/SeatReached.lean) ·
`wordFirst_at_row` (Johnson/Desc/K2/Honest/Carry/WordAt.lean).

NEAR, NOT CALLED. `link_closed_reached` (Returns/ClosedReached.lean), `head_closed_reached`,
`fin_closed_reached` (Returns/ClosedArms.lean): a closing behind the state, without who its frame
and statement are and where it was reached · `fresh_behind_laid` (Returns/SeatsWalk.lean),
`fresh_behind_cleared` (Returns/HeadSegment.lean): the fresh mask's number as a count of messages ·
`behind_of_close` (Johnson/Desc/First/Link/Law/BehindOfClose.lean): right behind the closing, at the
item's own way in and numbers: the members' shapes and the fresh mask's mask rows ·
`AtMg.mask_at_letters` (Johnson/P5J/MaskLettersAtMg.lean): in front of the closing: the mask, its
place, its tree's shape.

Limits. No run is given at which the head's premise and "reached" hold together: the laws under the
head could hold of nothing. Nothing ties the front's numbers p to the plan's own numbers of the
place, nor the state to the item's way in. Nothing holds the fresh mask's shape against a sender's
notice. j is not held below a code's length. THE THREE WALKS STAND ALSO IN
Returns/MembersNumbered.lean, Returns/SeatReached.lean AND Returns/TrueMembersAtHead.lean: here they
are said once, as `ClosedBehind`; those files do not call it. The full size and the format's second
hash function alone. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.WordAtFront
import Johnson.Desc.First.Link.Law.CarriedSizes
import Johnson.P5J.MaskLettersAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Chain Wit Grows)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (maskNo maskTree maskPart)
open VerifiableInference.Desc.LinkJoin (closeFrame_reads closeFrame_sizes)
open Meaning.K2 (live_open)
open VerifiableInference.Desc.Sound (below allOf EAll MsgT wordsFirst seatBy noFirst)
open VerifiableInference.Desc.K13.Law (LFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw reach_cuts_below)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open LPFK10 (ixK10)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The closing behind carried rows**: link l's closing kind's own sub-protocol was reached at a
state w with an open segment Lw; the frame's closing there returned u; rows are u's carried rows,
and T has grown out of u's statement. z: the public part. -/
def ClosedBehind (_h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat)
    (z : (F0T OnBytes.secondHashFunction Zp Np cF).XiPub) (rows : SingleRows) (T : Statement) : Prop :=
  ∃ (w : S) (Lw : Model.LinkCtx) (owed : Option Nat) (es : List Fmt.Entry) (rs : List Fmt.RoundView)
    (u : ReqFrame × Statement),
    Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (ixK10 l) (z, w) ∧ w.link? = some Lw ∧
      First.Close.closeFrame owed Lw.check.frame w.st es rs = .ok u ∧ rows = u.1.rows ∧
      Grows u.2 T

/-- At a segment's first place (14 (m + 1) + 2, m < 23), at the switch's front. -/
theorem link_closedBehind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : First.K2.P2} (hq : p.stands = .link)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx) :
    ClosedBehind h m a.1.1 fx.f.rows a.1.2.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below (h.toAtMg.rch_is_reach _ a hr)
  obtain ⟨-, -, -, -, -, a6, -⟩ :=
    Meaning.K2.front_pin_link h.scope h.reads O (l := m + 1) (by omega) (by omega) f₀ hq hfx
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts (14 * m + 12) (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, hf, hg⟩ :=
    closing_behind_laid h.scope h.reads O (l := m) (by omega) f₀
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : ixK10 m = 14 * m + 12 := by
    rw [ProofFile.Honest.K10.YesFree.number_is m, if_neg (by omega)]
  exact ⟨w, Lw, _, _, _, u, by rw [e12]; exact hw, hLw, hx, by rw [a6, hf], hg⟩

/-- At the output head's front (339): segment 23's closing. -/
theorem head_closedBehind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : First.K2.P2} (hq : p.stands = .head)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx) :
    ClosedBehind h 23 a.1.1 fx.f.rows a.1.2.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hR := h.toAtMg.rch_is_reach _ a hr
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below hR
  obtain ⟨tm, rm, cm, hm, fm⟩ := cuts 338 (by omega)
  obtain ⟨-, -, a3, -⟩ := Meaning.K2.front_nums_head h.scope h.reads O fm f₀ hq hfx
  have hlen : 338 < cF.blocksInOrder.length := by
    have := (reach_raw hR).fold.1
    omega
  obtain ⟨rs0, gs0, d0⟩ := Meaning.K2.fold_next (List.getElem?_eq_getElem hlen) fm f₀
  have hgr : Grows tm.st a.1.2.st :=
    IM.grows_front h.scope h.reads O (by omega) (List.getElem?_eq_getElem hlen) _ _ _ _ d0
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts 334 (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, hf, hg⟩ :=
    closing_behind_laid h.scope h.reads O (l := 23) (by omega) fm
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : ixK10 23 = 334 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 23, if_neg (by omega)]
  exact ⟨w, Lw, _, _, _, u, by rw [e12]; exact hw, hLw, hx, by rw [a3, hf], hg.trans hgr⟩

/-- At the front behind the last segment (353, behind its quiet step in front): segment 24's. -/
theorem fin_closedBehind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S} (he : First.K2.finishFrontQ a.1.2 = .ok t)
    {p : First.K2.P2} (hq : p.stands = .finish) {fx : _root_.Tw.K2.Front}
    (hfx : First.K2.frontAt p t = some fx) :
    ClosedBehind h 24 a.1.1 fx.f.rows a.1.2.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below (h.toAtMg.rch_is_reach _ a hr)
  obtain ⟨-, -, a3, -⟩ := Meaning.K2.front_nums_fin h.scope h.reads O f₀ he hq hfx
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts 350 (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, hf, hg⟩ :=
    closing_behind_cleared h.scope h.reads O f₀
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : ixK10 24 = 350 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 24, if_pos rfl]
  exact ⟨w, Lw, _, _, _, u, by rw [e12]; exact hw, hLw, hx, by rw [a3, hf], hg⟩

/-- **THE FRESH MASK OF CARRIED ROWS WITH A CLOSING BEHIND THEM**: its number is the plan's own
number of link l's fresh mask's seat; it is stated in T; and it has there 2 ^ h mask rows, h the
carried layout's. y: any strings. -/
theorem fresh_of_closedBehind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    {z : (F0T OnBytes.secondHashFunction Zp Np cF).XiPub} (hty : h.toAtMg.typed z)
    (y : (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    {rows : SingleRows} {T : Statement} (H : ClosedBehind h l z rows T) :
    rows.fresh = maskNo (P5J.At.seats Zp) (P5J.At.pseats Zp) l ∧
      rows.fresh < T.oracles.size ∧
      (T.oracles.getD rows.fresh default).shape.maskRows = 2 ^ rows.layout.h := by
  obtain ⟨w, Lw, owed, es, rs, u, hw, hLw, hx, rfl, hg⟩ := H
  obtain ⟨-, m, -, -, hm, hfr⟩ := closeFrame_reads hx
  obtain ⟨-, -, -, -, -, -, o, ho, -⟩ := closeFrame_sizes hx
  have hk := h.toAtMg.mask_all hl ((z, w), y) (by rw [← P5J.ixK10_is l hl]; exact ⟨hw, hty⟩)
  have hk' : w.live.frame.mask = some (maskNo (P5J.At.seats Zp) (P5J.At.pseats Zp) l) := hk
  rw [live_open hLw, hm] at hk'
  obtain ⟨o', ho', -⟩ := hg.2.2 _ _ ho
  have hlt : u.1.rows.fresh < T.oracles.size := (Array.getElem?_eq_some_iff.1 ho').1
  exact ⟨hfr.trans (Option.some.inj hk'), hlt, (layFits_of_close hx hg).fresh⟩

/-- **THE WORD AT THE FRESH MASK, THE CORE**: a is reached at a border k without a mark; rows have
link l's closing behind them, and a's statement has grown out of that closing's; St has a's oracle
messages, Bk is a's book ⊢ at a mask row b below 2 ^ h, h the carried layout's, and any place j, a
witness's word at the fresh mask, read at St and Bk, is the witness's table at the plan's seat of
link l's fresh mask, at the message's own shape in St. -/
theorem freshWord_of_closedBehind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat}
    (hk : k ≤ 358)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch k a) (hu : a.1.2.failed = none) {l : Nat} (hl : l < 25)
    {rows : SingleRows} (H : ClosedBehind h l a.1.1 rows a.1.2.st) {St : Statement}
    (hSt : St.oracles = a.1.2.st.oracles) {Bk : TreeBook} (hBk : Bk = a.1.2.book)
    {Cells Tok : Type} (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) {b : Nat}
    (hb : b < 2 ^ rows.layout.h) (j : Nat) :
    wordsFirst arr St Bk v rows.fresh .mask
        (b + j * 2 ^ ceilLog2 (St.oracles.getD rows.fresh default).shape.maskRows) =
      v.tab St.codes (St.oracles.getD rows.fresh default).shape
        (arr (maskTree l) (maskPart l)) (maskTree l) (maskPart l) true b j := by
  obtain ⟨e1, e2, e3⟩ := fresh_of_closedBehind h hl hr.2 a.2 H
  have hq : seatBy noFirst Bk rows.fresh = some (maskTree l, maskPart l) := by
    rw [hBk]
    exact seat_reached h hk a hr hu e2 (by rw [e1]; exact (h.toAtMg.mask_letters_at l hl).1)
  have hs : (St.oracles[rows.fresh]?).map (·.shape) =
      some (St.oracles.getD rows.fresh default).shape := by
    rw [hSt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem e2]
    rfl
  exact wordFirst_at_row arr St Bk v hs hq .mask
    (show b < (St.oracles.getD rows.fresh default).shape.maskRows by rw [hSt, e3]; exact hb) j

/-- **At a segment's first place** (14 (m + 1) + 2, m < 23), at the switch's front. -/
theorem link_freshWord_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : First.K2.P2} (hq : p.stands = .link)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx)
    {Cells Tok : Type} (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) {b : Nat}
    (hb : b < 2 ^ fx.f.rows.layout.h) (j : Nat) :
    wordsFirst arr fx.st a.1.2.book v fx.f.rows.fresh .mask
        (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows) =
      v.tab fx.st.codes (fx.st.oracles.getD fx.f.rows.fresh default).shape
        (arr (maskTree m) (maskPart m)) (maskTree m) (maskPart m) true b j := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ :=
    Meaning.K2.front_pin_link h.scope h.reads O (l := m + 1) (by omega) (by omega) f hq hfx
  exact freshWord_of_closedBehind h (by omega) a hr (link_member_stated h h23 a hr).1 (by omega)
    (link_closedBehind h h23 a hr hq hfx) a2 rfl arr v hb j

/-- **At the output head's front** (339): segment 23's fresh mask. -/
theorem head_freshWord_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : First.K2.P2} (hq : p.stands = .head)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p a.1.2 = some fx)
    {Cells Tok : Type} (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) {b : Nat}
    (hb : b < 2 ^ fx.f.rows.layout.h) (j : Nat) :
    wordsFirst arr fx.st a.1.2.book v fx.f.rows.fresh .mask
        (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows) =
      v.tab fx.st.codes (fx.st.oracles.getD fx.f.rows.fresh default).shape
        (arr (maskTree 23) (maskPart 23)) (maskTree 23) (maskPart 23) true b j := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_head h.scope h.reads O f hq hfx
  exact freshWord_of_closedBehind h (by omega) a hr (head_member_stated h a hr).1 (by omega)
    (head_closedBehind h a hr hq hfx) a2 rfl arr v hb j

/-- **At the front behind the last segment** (353, behind its quiet step in front, t): segment 24's
fresh mask; the book is t's. -/
theorem fin_freshWord_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S} (he : First.K2.finishFrontQ a.1.2 = .ok t)
    {p : First.K2.P2} (hq : p.stands = .finish) {fx : _root_.Tw.K2.Front}
    (hfx : First.K2.frontAt p t = some fx)
    {Cells Tok : Type} (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) {b : Nat}
    (hb : b < 2 ^ fx.f.rows.layout.h) (j : Nat) :
    wordsFirst arr fx.st t.book v fx.f.rows.fresh .mask
        (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows) =
      v.tab fx.st.codes (fx.st.oracles.getD fx.f.rows.fresh default).shape
        (arr (maskTree 24) (maskPart 24)) (maskTree 24) (maskPart 24) true b j := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, -, -, a4, -⟩ := Meaning.K2.front_nums_fin h.scope h.reads O f he hq hfx
  exact freshWord_of_closedBehind h (by omega) a hr (fin_member_stated h a hr).1 (by omega)
    (fin_closedBehind h a hr he hq hfx) a4 (First.K2.finishFrontQ_book he).1 arr v hb j

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.ClosedBehind
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_closedBehind
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_closedBehind
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_closedBehind
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fresh_of_closedBehind
#print axioms VerifiableInference.Desc.K2.Honest.Returns.freshWord_of_closedBehind
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_freshWord_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_freshWord_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_freshWord_front
