-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/SeatReached.lean: UNDER THE HEAD's PREMISE, AT A STATE REACHED AT ANY
BORDER OF THE FIRST CHAIN: WHERE THE STATE's BOOK SEATS A MESSAGE, WHICH SHAPE THE MESSAGE HAS, AND
SO WHAT A WITNESS's WORDS ARE AT IT; and that the members of the group that a code switch's carried
rows name are stated at the state in front of the switch, at all three sorts of the kind's places.
Statements with their proofs; no definition.

  `seat_reached` `AtMgA` · k ≤ 358 · a reached at k (`AtMg.rch`) without a mark · o below the number
                    of the statement's messages · the written plan's list has q at o
                    (`LFull.places[o]? = some q`) ⊢ `seatBy noFirst a.1.2.book o = some q`
  `member_in_opened` a member of carried rows is among `singleRowsOracles`
  `listed_reached` l < 25 · i a place of link l's written list · its number `noK10 … l i` is stated
                    at a ⊢ its seat by a's book is `seatK10 … l i`, and its shape in a's statement
                    is the list's
  `listed_word` and so: `wordsFirst arr a.1.2.st a.1.2.book v (noK10 … l i) part (b + j * 2 ^
                    ceilLog2 rows)` is `v.tab` at a's codes, the list's shape and the number arr
                    gives that seat, at (part == .mask), b, j: for every witness v and numbering arr
  `link_member_stated` m < 23, a reached at 14 (m + 1) + 2: no mark, and each member's number of
                    link m's list is stated
  `head_member_stated` the like at 339, of link 23's list
  `fin_member_stated` the like at 353, of link 24's list

How the seat is had. `seat_at_book` (Johnson/Desc/First/Close/Law/NoOfLink.lean) asks four things of
the state: the book stands where the plan says: `IM.book_reached_planOk`
(Johnson/IMR/BookPaidR.lean), at the table's numbers by `N₀_told`, `placesW_at`
(Johnson/P5J/FoldJ3.lean) · the seats are carried, the book is in order: two fields of `FoldFacts`,
from the head (`AtMgA.fold_full`, Johnson/P5J/MaskLettersAtMg.lean) · the first places of the plan's
list name trees that the book has: `counts_at_name` (Johnson/HB/LLHARD/CountsAtName.lean) and
`below_written` (Johnson/HB/LLHARD/ToldCounts.lean): as `AtMgA.below_at` has it. THE TABLE's PROMISE
IS NOT SPENT.

By, beside these: `hB_at_k10` (Johnson/LPFE1R/BelowAtK10.lean), `ld_at_laid`
(Johnson/LPFE1R/SeedPublicFull.lean), `shape_clause_laid` (Johnson/LPFE1R/ShapeAtNoFull.lean): the
shape at `noK10 … i` where the test on the shapes says yes · `wordFirst_at_row`
(Johnson/Desc/K2/Honest/Carry/WordAt.lean) · `membersNumbered_of_closing`, `link_membersNumbered`
(Returns/MembersNumbered.lean) · `stated_of_close` (Returns/MembersReached.lean),
`link_closed_reached` (Returns/ClosedReached.lean), `closing_behind_laid`, `closing_behind_cleared`
· `noMark_reach_below` · `grows_front` (Johnson/IMR/GrowsFlat.lean).

NEAR, NOT CALLED. `AtMgA.seats_at`, `AtMgA.below_at` (Johnson/P5J/K10SeatsAt.lean),
`AtMgA.seats_five`: the seat of `noK10 … i` AT K10's OWN BORDER, under the table's promise ·
`hs_k10` (NoOfLink.lean) · `shapes_reached` (Johnson/P1K2R/HT1Tight.lean): the shapes at a reached
state, at letters · `seed_state` (Johnson/P2LawR/SeedStateAtK10.lean) · `seatFirst_place`
(Johnson/Desc/Sound/SeamAt.lean), `seat_of_place` (Johnson/ToldDescR/HandedTwo.lean): a seat is the
book's place · `seat_by_new` (Johnson/Top/H0/Tw/K2C/WordsAtNew.lean): the NEW messages' seats behind
an accept of the switch · `out_oracles`, `closing_sent`
(Johnson/Desc/First/Close/Law/CarriedSent.lean): at K10's own closing: which messages its carried
rows open, and that the statement behind holds them.

Limits. No run is given at which the head's premise and "reached" hold together: the laws under the
head could hold of nothing. AT THE STATE's OWN STATEMENT AND BOOK: not yet at the front that the
switch's block takes off it, nor behind the quiet step in front of the last switch. Nothing on the
fresh mask's message. `Wit.tab`'s split at a pad's places is not entered. THE TWO LAST PROOFS WALK
AS THOSE OF Returns/MembersNumbered.lean AND OF Returns/TrueMembersAtHead.lean, which this library
may not hold: typed a third time. The full size and the format's second hash function alone. Nothing on any
property.
-/
import Johnson.Desc.K2.Honest.Returns.MembersNumbered
import Johnson.Desc.K2.Honest.Returns.MembersReached
import Johnson.P5J.K10SeatsAt
import Johnson.P5J.FoldJ3
import Johnson.IMR.BookPaidR
import Johnson.LPFE1R.ShapeAtNoFull
import Johnson.IMR.GrowsFlat
import Johnson.Desc.K2.Honest.Carry.WordAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S bookAt)
open VerifiableInference.Desc.First.Close (noK10 seatK10 seat_at_book)
open VerifiableInference.Desc.LinkJoin (loAt hB_at_k10 ld_at_laid shape_clause_laid)
open VerifiableInference.Desc.Sound (below allOf EAll seatBy noFirst)
open VerifiableInference.Desc.K12.Door (placesBelowB)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.K13.Law (countsFull below_written LFull)
open Johnson.Desc.First.Walk.Tied (reach_raw reach_cuts_below)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE SEAT OF A MESSAGE AT A REACHED STATE**: under the head, at a state without a mark that is
reached at a border k: the state's book seats each of the statement's messages where the written
plan's list of places has it. -/
theorem seat_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 358)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch k a) (hu : a.1.2.failed = none) {o : Nat} {q : Nat × Nat}
    (ho : o < a.1.2.st.oracles.size) (hpl : LFull.places[o]? = some q) :
    seatBy noFirst a.1.2.book o = some q := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hbook : bookAt (P5J.At.N Zp cF) P5J.At.ps[k]? a.1.2 = true := by
    have e := IM.book_reached_planOk h.scope h.reads O (P5J.At.N₀ Zp cF) h.laid.planOk a.1.1 k
      a.1.2 (reach_raw (h.toAtMg.rch_is_reach _ a hr))
    rw [P5J.N₀_told, P5J.placesW_at] at e
    exact e
  have hseats := h.fold_full.seatsCarried k a hr hu
  have hord := h.fold_full.bookInOrder k a hr hu
  have hb : placesBelowB LFull a.1.2.book.place.size a.1.2.book.trees.size = true := by
    have hc := P5J.counts_at_name h.toAtMg.scope h.toAtMg.laid (k := k) hk
    have hw := List.all_eq_true.1 below_written _ (List.mem_of_getElem? hc)
    have e := hbook
    unfold bookAt at e
    simp only [Bool.and_eq_true, beq_iff_eq] at e
    rw [e.1.1, e.1.2, e.2]
    exact hw
  exact seat_at_book hbook hseats hord hb o q
    (by rw [← (VerifiableInference.OnPublicFiles.bookAt_sizes hbook).2]; exact ho) hpl

/-- A member of carried rows is among the messages that must be opened to read them. -/
theorem member_in_opened {old : SingleRows} {o : Nat} (h : o ∈ old.layout.members.toList) :
    o ∈ (singleRowsOracles old).toList := by
  unfold singleRowsOracles
  split
  · rw [Array.toList_push]
    exact List.mem_append_left _ h
  · exact h

/-- **A WRITTEN LIST's MESSAGE AT A REACHED STATE AT WHICH ITS NUMBER IS STATED**: its seat by the
state's book, and its shape in the state's statement. -/
theorem listed_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 358)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch k a) (hu : a.1.2.failed = none) {l : Nat} (hl : l < 25)
    (i : Fin (loAt l).length)
    (ho : noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i < a.1.2.st.oracles.size) :
    seatBy noFirst a.1.2.book (noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i) =
        some (seatK10 (loAt l) (P5J.At.pseats Zp) l i) ∧
      (a.1.2.st.oracles[noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i]?).map (·.shape) =
        some ((loAt l).get i).1 := by
  obtain ⟨-, b2, -⟩ := hB_at_k10 h.toAtMg.scope h.toAtMg.laid
    (ld_at_laid h.toAtMg.scope h.toAtMg.laid) (l := l) hl i
  exact ⟨seat_reached h hk a hr hu ho b2,
    shape_clause_laid h.toAtMg.scope h.toAtMg.laid hl (h.fold_full.msgShapes k a hr hu) i ho⟩

/-- **AND SO THE WITNESS's WORDS AT IT**: at the index "row + place * 2 ^ ceilLog2 rows" the reader
of a witness's words gives the witness's table at the number of the plan's seat, at that row and
place. arr: the numbering of the seats. -/
theorem listed_word (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 358)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch k a) (hu : a.1.2.failed = none) {l : Nat} (hl : l < 25)
    (i : Fin (loAt l).length)
    (ho : noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i < a.1.2.st.oracles.size)
    {Cells Tok : Type} (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) (part : OnBytes.Part)
    {b : Nat}
    (hb : b < ((loAt l).get i).1.rows part) (j : Nat) :
    wordsFirst arr a.1.2.st a.1.2.book v (noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i)
        part (b + j * 2 ^ ceilLog2 (((loAt l).get i).1.rows part)) =
      v.tab a.1.2.st.codes ((loAt l).get i).1
        (arr (seatK10 (loAt l) (P5J.At.pseats Zp) l i).1
          (seatK10 (loAt l) (P5J.At.pseats Zp) l i).2)
        (seatK10 (loAt l) (P5J.At.pseats Zp) l i).1 (seatK10 (loAt l) (P5J.At.pseats Zp) l i).2
        (part == .mask) b j := by
  obtain ⟨h1, h2⟩ := listed_reached h hk a hr hu hl i ho
  exact wordFirst_at_row arr _ _ v h2 h1 part hb j

/-- **AT A SEGMENT's FIRST PLACE** (14 (m + 1) + 2, m < 23): the state has no mark, and each member
of the closed group is stated there. -/
theorem link_member_stated (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) :
    a.1.2.failed = none ∧ ∀ i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt m),
      noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i < a.1.2.st.oracles.size := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hR := h.toAtMg.rch_is_reach _ a hr
  refine ⟨IM.noMark_reach_below h.scope h.reads O hR (by omega)
    (fun l' hl' => by unfold IM.nAt; split <;> omega), fun i hi => ?_⟩
  obtain ⟨owed, f, S₀, es, rs, y, hy, hf, hg⟩ := link_closed_reached h.scope h.reads O h23 hR
  have hmem : noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i ∈
      y.1.rows.layout.members.toList := by
    rw [← hf, link_membersNumbered h (by omega) a hr]
    exact List.mem_map_of_mem hi
  exact stated_of_close hy hg _ (member_in_opened hmem)

/-- **AT THE OUTPUT HEAD's PLACE** (339): the like, of segment 23's closed group. -/
theorem head_member_stated (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) :
    a.1.2.failed = none ∧ ∀ i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt 23),
      noK10 (P5J.At.seats Zp) (loAt 23) (P5J.At.pseats Zp) 23 i < a.1.2.st.oracles.size := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hR := h.toAtMg.rch_is_reach _ a hr
  refine ⟨IM.noMark_reach_below h.scope h.reads O hR (by omega)
    (fun l' hl' => by unfold IM.nAt; split <;> omega), fun i hi => ?_⟩
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below hR
  obtain ⟨tm, rm, cm, hm, fm⟩ := cuts 338 (by omega)
  have hlen : 338 < cF.blocksInOrder.length := by
    have := (reach_raw hR).fold.1
    omega
  obtain ⟨rs0, gs0, d0⟩ := Meaning.K2.fold_next (List.getElem?_eq_getElem hlen) fm f₀
  have hgr : VerifiableInference.Desc.Grows tm.st a.1.2.st :=
    IM.grows_front h.scope h.reads O (by omega) (List.getElem?_eq_getElem hlen) _ _ _ _ d0
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts 334 (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, -, hg⟩ :=
    closing_behind_laid h.scope h.reads O (l := 23) (by omega) fm
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : LPFK10.ixK10 23 = 334 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 23, if_neg (by omega)]
  have hmem : noK10 (P5J.At.seats Zp) (loAt 23) (P5J.At.pseats Zp) 23 i ∈
      u.1.rows.layout.members.toList := by
    rw [membersNumbered_of_closing h (l := 23) (by omega) hr.2 a.2 (by rw [e12]; exact hw) hLw hx]
    exact List.mem_map_of_mem hi
  exact stated_of_close hx (hg.trans hgr) _ (member_in_opened hmem)

/-- **BEHIND THE LAST SEGMENT** (353): the like, of segment 24's closed group. -/
theorem fin_member_stated (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) :
    a.1.2.failed = none ∧ ∀ i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt 24),
      noK10 (P5J.At.seats Zp) (loAt 24) (P5J.At.pseats Zp) 24 i < a.1.2.st.oracles.size := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hR := h.toAtMg.rch_is_reach _ a hr
  refine ⟨IM.noMark_reach_below h.scope h.reads O hR (by omega)
    (fun l' hl' => by unfold IM.nAt; split <;> omega), fun i hi => ?_⟩
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below hR
  obtain ⟨w, rw', cw, hw, fw⟩ := cuts 350 (by omega)
  obtain ⟨w', Rw, Cw, Lw, Q, rs', u, fw', hLw, -, hx, -, hg⟩ :=
    closing_behind_cleared h.scope h.reads O f₀
  obtain rfl : w = w' := congrArg Prod.fst (Except.ok.inj (fw.symm.trans fw'))
  have e12 : LPFK10.ixK10 24 = 350 := by
    rw [ProofFile.Honest.K10.YesFree.number_is 24, if_pos rfl]
  have hmem : noK10 (P5J.At.seats Zp) (loAt 24) (P5J.At.pseats Zp) 24 i ∈
      u.1.rows.layout.members.toList := by
    rw [membersNumbered_of_closing h (l := 24) (by omega) hr.2 a.2 (by rw [e12]; exact hw) hLw hx]
    exact List.mem_map_of_mem hi
  exact stated_of_close hx hg _ (member_in_opened hmem)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.seat_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.member_in_opened
#print axioms VerifiableInference.Desc.K2.Honest.Returns.listed_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.listed_word
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_member_stated
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_member_stated
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_member_stated
