-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/FitsAtPlan.lean: the field fits of PlanAt and of PlanRest (K1's files': ∀
x ∈ ms, SeatFits G cs x.1.l x.1.seat), RESTATED OVER THE PLAN's SEATS AND OVER WHAT THE FIRST
CHAIN's SUB-PROTOCOLS DECLARE, at the members by the make (P5T.msAtR); and evaluated by Lean's
kernel at the written values. It names no place: one fact serves all 52 places of the kind K1. A law
file; no running text imports it. The road. seatsFit_of_B gives the field from the plain
test seatsFitB; seatsFitB_R turns that test, at the members by the make, into a test
over the plan's seats (seatsFitP: no radius); noFault_iff (Johnson/Desc/SeatAtOracle.lean) shows
that this test reads of the IOP as written in Lean nothing but G.oracleAt at the seats' trees; these
are trees of the first chain, so G.oracleAt there is the first chain's list of declared oracles.
  fitsToldB os cs ps: the test: at every plan's seat with an OOD sample the oracle number (the
      seat's tree) of the list os fits the seat's shape and tenant
  oracleAt_first: below the first chain's number of declared oracles G.oracleAt reads that chain's
      list
  seatsFitP_of_told: the plan's test from fitsToldB, where os is what the first chain declares
  fits_byMake, fits_atR: the field, at msOf (P5T.memberListsR n radM ps) and at P5T.msAtR Z radM
  osC: what the written cut's 358 sub-protocols declare, one list: 83 oracles
  fits_written: fitsToldB osC codesFull2 P5T.psFull = true: at all 167 seats with an OOD sample:
      Lean's kernel; seats_below: these seats' trees are below 83
  fits_full: the field at the written seats, from the one premise
  fits_rejects: the negative tests: the code table emptied · the oracles shifted by one · one word
      more in tree 40: each rejects

ONE PREMISE STAYS, THE SAME ON WHICH THE TESTS ON THE TABLE's NUMBERS HANG: hO : oraclesOf
G.first.blocksInOrder = osC: what the IOP as written in Lean declares is what the written cut says. What is
not claimed. hO at a seat. planSeats Z Z.D.1 = psFull, cs = codesFull2 at a seat. Nothing on
soundness.

-/
import Johnson.Desc.SeatAtOracle
import Johnson.Desc.AtSeats.CandidateAtCut
import Johnson.P5T.MembersByMake
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes
open VerifiableInference.Desc.Sound (Mem SeatFits msOf seatsFit_of_B)
open HashBuild (toldC)

/-- **The test over the plan's seats and the declared oracles.** -/
def fitsToldB (os : List Oracle) (cs : Codes) (ps : List P5T.PSeat) : Bool :=
  (ps.filter (·.smpd)).all fun p => fitsOrc cs p.shape p.seat.2 os[p.seat.1]?

theorem oracleAt_first {Xi : Type} (G : FileDescription Xi) {j : ℕ}
    (hj : j < (oraclesOf G.first.blocksInOrder).length) : G.oracleAt j = (oraclesOf G.first.blocksInOrder)[j]? := by
  unfold FileDescription.oracleAt
  rw [List.append_assoc, List.getElem?_append_left hj]

theorem seatsFitP_of_told {Xi : Type} (G : FileDescription Xi) {os : List Oracle} {cs : Codes}
    {ps : List P5T.PSeat} (hO : oraclesOf G.first.blocksInOrder = os)
    (hb : ∀ p ∈ ps.filter (·.smpd), p.seat.1 < os.length) (h : fitsToldB os cs ps = true) :
    P5T.seatsFitP G cs ps = true := by
  unfold P5T.seatsFitP
  refine List.all_eq_true.2 fun p hp => ?_
  rw [noFault_iff, oracleAt_first G (by rw [hO]; exact hb p hp), hO]
  exact List.all_eq_true.1 h p hp

/-- **The field fits, at the members by the make.** -/
theorem fits_byMake {Xi : Type} (G : FileDescription Xi) {os : List Oracle} {cs : Codes} {n : ℕ}
    (radM : ℕ → ℕ → ℕ) {ps : List P5T.PSeat} (hn : ∀ p ∈ ps, p.smpd = true → p.send < n)
    (hO : oraclesOf G.first.blocksInOrder = os) (hb : ∀ p ∈ ps.filter (·.smpd), p.seat.1 < os.length)
    (h : fitsToldB os cs ps = true) :
    ∀ x ∈ msOf (P5T.memberListsR n radM ps), SeatFits G cs x.1.l x.1.seat :=
  seatsFit_of_B G cs _ (by
    rw [P5T.seatsFitB_R G cs n radM ps hn]
    exact seatsFitP_of_told G hO hb h)

theorem fits_atR {Xi : Type} (G : FileDescription Xi) {os : List Oracle} {cs : Codes} (Z : ProofFile.Pub)
    (radM : ℕ → ℕ → ℕ) (hO : oraclesOf G.first.blocksInOrder = os)
    (hb : ∀ p ∈ (P5T.planSeats Z Z.D.1).filter (·.smpd), p.seat.1 < os.length)
    (h : fitsToldB os cs (P5T.planSeats Z Z.D.1) = true) :
    ∀ x ∈ P5T.msAtR Z radM, SeatFits G cs x.1.l x.1.seat :=
  fits_byMake G radM (fun p hp _ => P5T.planSeats_send_lt Z Z.D.1 p hp) hO hb h

/-! ## At the written values -/

/-- What the written cut's sub-protocols declare, one list. -/
def osC : List Oracle := toldC.flatten

set_option maxRecDepth 1000000 in
/-- **The accept**, at all 167 seats with an OOD sample. -/
theorem fits_written : (decide (osC.length = 83) &&
    decide ((P5T.psFull.filter (·.smpd)).length = 167) &&
    fitsToldB osC Johnson.G.codesFull2 P5T.psFull) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem seats_below : ((P5T.psFull.filter (·.smpd)).all fun p => decide (p.seat.1 < osC.length)) =
    true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Negative tests. -/
theorem fits_rejects : (fitsToldB osC {} P5T.psFull ||
    fitsToldB (osC.drop 1) Johnson.G.codesFull2 P5T.psFull ||
    fitsToldB (osC.modify 40 fun o => { o with words := o.words + 1 }) Johnson.G.codesFull2
      P5T.psFull) = false := by decide +kernel

/-- **The field at the written seats**, from the one premise. -/
theorem fits_full {Xi : Type} (G : FileDescription Xi) (radM : ℕ → ℕ → ℕ) {n : ℕ}
    (hn : ∀ p ∈ P5T.psFull, p.smpd = true → p.send < n) (hO : oraclesOf G.first.blocksInOrder = osC) :
    ∀ x ∈ msOf (P5T.memberListsR n radM P5T.psFull),
      SeatFits G Johnson.G.codesFull2 x.1.l x.1.seat := by
  have h := fits_written
  rw [Bool.and_eq_true] at h
  exact fits_byMake G radM hn hO
    (fun p hp => of_decide_eq_true (List.all_eq_true.1 seats_below p hp)) h.2

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.oracleAt_first
#print axioms VerifiableInference.Desc.seatsFitP_of_told
#print axioms VerifiableInference.Desc.fits_byMake
#print axioms VerifiableInference.Desc.fits_atR
#print axioms VerifiableInference.Desc.fits_written
#print axioms VerifiableInference.Desc.seats_below
#print axioms VerifiableInference.Desc.fits_rejects
#print axioms VerifiableInference.Desc.fits_full
