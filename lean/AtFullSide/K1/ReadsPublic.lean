-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsPublic.lean: under the head, the seat of the array "U3" at each of the 25 segments,
at the written values: which message of the reads' sending it is. Public data alone.

  u3AtLinkW, u3AtLinkW_yes   the written test
  seat_at_link               under the head, at each segment, the seat and what the test says of it

Limits. Nothing on a run. Nothing on soundness, completeness or hiding.
-/
import Johnson.HonestTrace.U3Fit.SeatsAtHead
import Johnson.Desc.ProofFile.Honest.K1.LaterOffPad
import Johnson.AtFull.Shape.Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes.HonestTrace (Seat)
open OnBytes.HonestTrace.U3 (u3Seats)
open OnBytes.HonestTrace.U3.Fit (seatsW seats_at_head)
open P5J (AtMgA TS)
open VerifiableInference.Desc

/-- The written test: each of the 25 segments has a seat of "U3" in its reads' sending. -/
def u3AtLinkW : Bool :=
  (List.range 25).all fun l => (seatsW "U3").any fun s =>
    s.seg == l && s.addr.sender == ⟨⟨1, some l, IM.k1Ix l false + 1, .K1⟩, 0⟩ && momentIs s 1 &&
      s.shape.mainDeg == 3 && s.shape.answers != 0

set_option maxRecDepth 1000000 in
theorem u3AtLinkW_yes : u3AtLinkW = true := by decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE SEAT OF "U3" AT A SEGMENT.** -/
theorem seat_at_link (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l < 25) :
    ∃ s ∈ u3Seats Zp G, s.seg = l ∧
      s.addr.sender = ⟨⟨1, some l, IM.k1Ix l false + 1, .K1⟩, 0⟩ ∧ momentIs s 1 = true ∧
      s.shape.mainDeg = 3 ∧ s.shape.answers ≠ 0 := by
  have k := List.all_eq_true.1 u3AtLinkW_yes l (List.mem_range.2 hl)
  obtain ⟨s, hs, hq⟩ := List.any_eq_true.1 k
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hq
  obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩ := hq
  refine ⟨s, ?_, e1, e2, e3, e4, e5⟩
  unfold u3Seats
  rw [seats_at_head h hG]
  exact hs

/-- The written test on the dealing and the moments of the seats of "U3". -/
def apartW : Bool :=
  ((seatsW "BZ").all fun s => s.addr.sender != firstAddr) &&
    (seatsW "U3").all fun s =>
      s.addr.sender != firstAddr && !OnBytes.HonestTrace.mineOf (seatsW "BZ") s.addr && momentIs s 1

set_option maxRecDepth 1000000 in
theorem apartW_yes : apartW = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem lengthsOk_full2 : Johnson.G.codesFull2.lengthsOk = true := by decide +kernel

/-- **THE PUBLIC TEST ON THE DEALING, UNDER THE HEAD.** -/
theorem apart_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : apartOk Zp G = true := by
  have k := apartW_yes
  unfold apartW at k
  rw [Bool.and_eq_true] at k
  unfold apartOk u3Seats
  rw [seats_at_head h hG, seats_at_head h hG, Bool.and_eq_true]
  refine ⟨k.1, List.all_eq_true.2 fun s hs => ?_⟩
  have q := List.all_eq_true.1 k.2 s hs
  simp only [Bool.and_eq_true] at q ⊢
  exact q.1

/-- Every seat of "U3" is of the moment 1; no seat of "BZ" has the address of one. -/
theorem u3_moment (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {s : Seat} (hs : s ∈ u3Seats Zp G) :
    momentIs s 1 = true ∧ OnBytes.HonestTrace.seatAt (OnBytes.HonestTrace.seatsOf Zp G "BZ") s.addr = none := by
  have k := apartW_yes
  unfold apartW at k
  rw [Bool.and_eq_true] at k
  unfold u3Seats at hs
  rw [seats_at_head h hG] at hs
  have q := List.all_eq_true.1 k.2 s hs
  simp only [Bool.and_eq_true] at q
  refine ⟨q.2, ?_⟩
  rw [seats_at_head h hG]
  have e := q.1.2
  unfold OnBytes.HonestTrace.mineOf at e
  simpa using e

/-- **WHAT THE LAW ON THE VECTOR OF READS ASKS OF THE PLAN, AT A SEGMENT.** -/
theorem reads_public (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l < 25)
    (gp : _root_.Desc.Plain.GPar) :
    ∃ (st : Seat) (n : ℕ), st ∈ u3Seats Zp G ∧ st.seg = l ∧
      st.addr = ⟨⟨(K1.parLater G.first gp l (IM.k1Ix l false + 1) 1).place, 0⟩, n⟩ ∧
      n < (K1.parLater G.first gp l (IM.k1Ix l false + 1) 1).sent.size ∧
      Johnson.Prover.Send.shapeAt (K1.parLater G.first gp l (IM.k1Ix l false + 1) 1) n = st.shape ∧
      (Johnson.Prover.Send.shapeAt (K1.parLater G.first gp l (IM.k1Ix l false + 1) 1) n).answers ≠ 0 ∧
      ((Johnson.Prover.Send.shapeAt (K1.parLater G.first gp l (IM.k1Ix l false + 1) 1) n).mainDeg == 3) = true ∧
      (∀ t, (OnBytes.HonestTrace.seatAt (OnBytes.HonestTrace.seatsOf Zp G "BZ")
            ⟨⟨(K1.parLater G.first gp l (IM.k1Ix l false + 1) 1).place, 0⟩, n⟩ = some t ∨
          OnBytes.HonestTrace.seatAt (OnBytes.HonestTrace.seatsOf Zp G "U3")
            ⟨⟨(K1.parLater G.first gp l (IM.k1Ix l false + 1) 1).place, 0⟩, n⟩ = some t) →
        momentIs t 1 = true) := by
  obtain ⟨s, hs, e1, e2, e3, e4, e5⟩ := seat_at_link h hG hl
  have hadr : s.addr = ⟨⟨(K1.parLater G.first gp l (IM.k1Ix l false + 1) 1).place, 0⟩, s.addr.msg⟩ := by
    cases ha : s.addr with
    | mk sn m =>
      rw [ha] at e2
      cases e2
      rfl
  have hmem : s ∈ OnBytes.HonestTrace.seatsOf Zp G "U3" := hs
  obtain ⟨sps, seg, hso⟩ := seats_text hmem
  have hseg := seat_seg hso
  rw [hadr] at hseg
  obtain rfl : l = seg := Option.some.inj hseg
  have hsh := seat_shape_later hso gp (IM.k1Ix l false + 1) 1 e3
  have hnot : s.addr.msg < (K1.parLater G.first gp l (IM.k1Ix l false + 1) 1).sent.size := by
    by_contra hn
    have hd : Johnson.Prover.Send.shapeAt (K1.parLater G.first gp l (IM.k1Ix l false + 1) 1) s.addr.msg =
        (default : OnBytes.OracleNotice).shape := by
      unfold Johnson.Prover.Send.shapeAt
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hn)]
      rfl
    rw [hsh] at hd
    exact e5 (by rw [hd]; rfl)
  refine ⟨s, s.addr.msg, hs, e1, hadr, hnot, hsh, ?_, ?_, ?_⟩
  · rw [hsh]
    exact e5
  · rw [hsh, e4]
    rfl
  · intro t ht
    rcases ht with ht | ht
    · rw [← hadr, (u3_moment h hG hs).2] at ht
      cases ht
    · have hm := List.mem_of_find?_eq_some ht
      exact (u3_moment h hG hm).1

/-- The written test on what a seat of "U3" says of the layout, the shape and the message. -/
def seatClausesW : Bool :=
  (seatsW "U3").all fun st =>
    (match OnBytes.reqArray Johnson.G.layoutFull st.seg "U3" with
      | some a => decide (a = st.array)
      | none => false) &&
    ((_root_.Meaning.messageAt VerifiableInference.PlanWritten.proofSizedFull.request st.seg
        st.array.message).any fun M => decide (M.shape = st.shape) && M.shape.answers != 0) &&
    (OnBytes.HonestTrace.pairOf (seatsW "U3") st.addr == some (st.seg, st.array.message)) &&
    st.array.name == "U3" && decide (0 < st.array.sizeI) &&
    OnBytes.laidMatrixOk st.array (OnBytes.ceilLog2 (st.shape.rows OnBytes.Part.main))
      (if st.shape.rows OnBytes.Part.main == 0 then 0
        else (Johnson.G.codesFull2.base.getD st.shape.code default).logEll) &&
    ((((VerifiableInference.PlanWritten.proofSizedFull.request.link[st.seg]?.map
        (·.messages)).getD []).filter fun x => x.moment == 0).length + st.addr.msg ==
      st.array.message)

set_option maxRecDepth 1000000 in
theorem seatClausesW_yes : seatClausesW = true := by decide +kernel

/-- **WHAT A SEAT OF "U3" SAYS, UNDER THE HEAD.** -/
theorem seat_clauses (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {st : Seat} (hs : st ∈ u3Seats Zp G) :
    OnBytes.reqArray G.first.layout st.seg "U3" = some st.array ∧
      (∃ M, _root_.Meaning.messageAt G.first.shape st.seg st.array.message = some M ∧
        M.shape = st.shape ∧ M.shape.answers ≠ 0) ∧
      OnBytes.HonestTrace.pairOf (u3Seats Zp G) st.addr = some (st.seg, st.array.message) ∧
      st.array.name = "U3" ∧ 0 < st.array.sizeI ∧
      OnBytes.laidMatrixOk st.array (OnBytes.ceilLog2 (st.shape.rows OnBytes.Part.main))
        (if st.shape.rows OnBytes.Part.main == 0 then 0
          else (G.first.codes.base.getD st.shape.code default).logEll) = true ∧
      (((G.first.shape.link[st.seg]?.map (·.messages)).getD []).filter
        fun x => x.moment == 0).length + st.addr.msg = st.array.message := by
  obtain ⟨e1, e2, e3⟩ := OnBytes.HonestTrace.U3.Fit.first_at_head h hG
  have hs' : st ∈ seatsW "U3" := by
    have q := hs
    unfold u3Seats at q
    rwa [seats_at_head h hG] at q
  have k := List.all_eq_true.1 seatClausesW_yes st hs'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at k
  obtain ⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩ := k
  rw [e1, e2, e3]
  refine ⟨?_, ?_, ?_, k4, k5, by simpa only [beq_iff_eq] using k6, k7⟩
  · cases hr : OnBytes.reqArray Johnson.G.layoutFull st.seg "U3" with
    | none =>
      rw [hr] at k1
      cases k1
    | some a =>
      rw [hr] at k1
      have e : a = st.array := by simpa using k1
      rw [e]
  · cases hm : _root_.Meaning.messageAt VerifiableInference.PlanWritten.proofSizedFull.request
        st.seg st.array.message with
    | none =>
      rw [hm] at k2
      cases k2
    | some M =>
      rw [hm] at k2
      simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at k2
      exact ⟨M, rfl, k2.1, k2.2⟩
  · unfold u3Seats
    rw [seats_at_head h hG]
    exact k3

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.seat_at_link
#print axioms ProofFile.Honest.K1.apart_at_head
#print axioms ProofFile.Honest.K1.reads_public
#print axioms ProofFile.Honest.K1.seat_clauses
