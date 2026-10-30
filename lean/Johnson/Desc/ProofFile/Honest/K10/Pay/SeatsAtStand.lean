-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/SeatsAtStand.lean: the closing of a segment (K10): at a state that the first chain's own
blocks reach in front of a closing, without a mark of failure: where the state's book seats each member of the group
that the closing folds, and which shape that member has, in the plan's own terms.

  `seat_at_reach`       under the head, at a state reached at any border k ≤ 358 without a mark: the state's book seats each of
                      the statement's messages where the written plan's list of places has it
  **`members_at_closing`**   in front of the closing of segment l < 25, G the group that the record's frame names: G's members are
                      the numbers `noK10 … l i` of the written list's members, in order; and for each such i the book seats
                      that number at the plan's seat `seatK10 … l i`, and the message there has the written shape
  `member_at_closing`   the same by the member's position j in the group's list

These are `seat_reached` and `listed_reached` (Johnson/Desc/K2/Honest/Returns/SeatReached.lean) with "reached" in the bare form:
by the chain's own blocks, with no condition on the public part of the instance.

Limits. The head is a premise. That a state is reached is not shown here. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AtReach
import Johnson.Desc.K2.Honest.Returns.SeatReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (bookAt)
open VerifiableInference.Desc.First.Close (ShapesAre kbAt noK10 seatK10 seat_at_book)
open VerifiableInference.Desc.LinkJoin (loAt hB_at_k10 ld_at_laid)
open VerifiableInference.Desc.Sound (seatBy noFirst)
open VerifiableInference.Desc.K12.Door (placesBelowB)
open VerifiableInference.Desc.K13.Law (below_written LFull)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The state's book seats each stated message where the written plan's list of places has it.** -/
theorem seat_at_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 358) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (z, s)) (hf : s.failed = none) {o : Nat} {q : Nat × Nat}
    (ho : o < s.st.oracles.size) (hpl : LFull.places[o]? = some q) : seatBy noFirst s.book o = some q := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hbook : bookAt (P5J.At.N Zp cF) P5J.At.ps[k]? s = true := by
    have e := IM.book_reached_planOk h.scope h.reads O (P5J.At.N₀ Zp cF) h.laid.planOk z k s hr
    rw [P5J.N₀_told, P5J.placesW_at] at e
    exact e
  have FF := foldFacts_reach h
  have hseats := FF.seatsCarried k (z, s) hr hf
  have hord := FF.bookInOrder k (z, s) hr hf
  have hb : placesBelowB LFull s.book.place.size s.book.trees.size = true := by
    have hc := P5J.counts_at_name h.toAtMg.scope h.toAtMg.laid (k := k) hk
    have hw := List.all_eq_true.1 below_written _ (List.mem_of_getElem? hc)
    have e := hbook
    unfold bookAt at e
    simp only [Bool.and_eq_true, beq_iff_eq] at e
    rw [e.1.1, e.1.2, e.2]
    exact hw
  exact seat_at_book hbook hseats hord hb o q
    (by rw [← (VerifiableInference.OnPublicFiles.bookAt_sizes hbook).2]; exact ho) hpl

/-- **In front of a closing: the group's members by number, each one's seat by the state's book, and its shape.** -/
theorem members_at_closing (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub}
    {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none)
    {G : OnBytes.Group} (hG : (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G) :
    G.members.toList = (VerifiableInference.Desc.First.Close.membersOf (loAt l)).map (noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l) ∧
      ∀ i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt l),
        seatBy noFirst s.book (noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i) =
            some (seatK10 (loAt l) (P5J.At.pseats Zp) l i) ∧
          ∃ y, s.st.oracles[noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i]? = some y ∧
            y.shape = ((loAt l).get i).1 := by
  have Sh : ShapesAre s.st G (loAt l) (kbAt VerifiableInference.Desc.ReqLit.shapeFull l (loAt l))
      (noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l) := shapes_reached h hl hr hf G hG
  have hk : 14 * l + IM.nAt l + 5 ≤ 358 := by
    unfold IM.nAt
    split <;> omega
  refine ⟨Sh.members, fun i hi => ?_⟩
  obtain ⟨y, hy, hs⟩ := Option.map_eq_some_iff.1 (Sh.shape i hi)
  have ho : noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i < s.st.oracles.size :=
    (Array.getElem?_eq_some_iff.1 hy).1
  obtain ⟨-, b2, -⟩ := hB_at_k10 h.toAtMg.scope h.toAtMg.laid (ld_at_laid h.toAtMg.scope h.toAtMg.laid) (l := l) hl i
  exact ⟨seat_at_reach h hk hr hf ho b2, y, hy, hs⟩

/-- The same by the member's position in the group's list. -/
theorem member_at_closing (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub}
    {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none)
    {G : OnBytes.Group} (hG : (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G) {j o : Nat}
    (ho : G.members.toList[j]? = some o) :
    ∃ i, (VerifiableInference.Desc.First.Close.membersOf (loAt l))[j]? = some i ∧ o = noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i ∧
      seatBy noFirst s.book o = some (seatK10 (loAt l) (P5J.At.pseats Zp) l i) ∧
      ∃ y, s.st.oracles[o]? = some y ∧ y.shape = ((loAt l).get i).1 := by
  obtain ⟨hm, hall⟩ := members_at_closing h hl hr hf hG
  rw [hm, List.getElem?_map] at ho
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 ho
  obtain ⟨h1, h2⟩ := hall i (List.mem_of_getElem? hi)
  exact ⟨i, hi, rfl, h1, h2⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seat_at_reach
#print axioms ProofFile.Honest.K10.members_at_closing
#print axioms ProofFile.Honest.K10.member_at_closing
