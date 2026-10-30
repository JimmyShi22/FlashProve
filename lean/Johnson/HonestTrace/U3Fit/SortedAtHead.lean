-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/SortedAtHead.lean

Under the head and the opening, each address that a switch's place gives ("addrs") for an own
message of a segment in front of it falls to one of four: a switch's own sending; the first place of
the kind K1 ("K1.firstAddr"); the digits' message (a seat of "BZ"); the reads' message. At the
fourth the seats of "U3" name just that segment and message, and the layout lays "U3" alone into it.
Definitions and theorems. Public data alone.

Terms. The head: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean. "The opening" is the premise O :
"IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
(secondAt Zp Np)" (Johnson/IMR/SeatOpen.lean); the ground is then "Bs.G₀". Under the head there is
one: the field "opened" of "h.laid" (Johnson/P5J/LaidOpens.lean).

Main definitions:
* "sortedOne", "sortedBy": the test, of closed letters: the switches' own seats' list, the places,
  the segments, the shape, the layout, the seats of "U3" and of "BZ". It walks the places; the
  segments in front of a place; a segment's own messages; the address, where there is one: at one
  place that is the first loop of "ownLaid" (Johnson/Desc/ProofFile/Honest/K2/AtPlan.lean), which
  rejects where there is no address. The second loop of "ownLaid", over the switch's own sending, it
  does not walk.
* "sortedAt": at a public part and a ground. "ownW": the first list at the written places.

Main theorems:
* "sorted_at_head": "sortedAt Zp Bs.G₀ = true".
* "reads_at_head": an address a with "p.addrs y.2 s.2 = some a" that is none of the other three has
  "pairOf (u3Seats Zp Bs.G₀) a = some (y.2, s.2)", and the layout's arrays in that message are
  ["U3"].

Limits. Head and opening are premises: the full size and the format's second hash function alone. Two closed
facts, "sortedW" and "sortedW_can_fail" (four controls), are shown by "decide +kernel", each under
"set_option maxRecDepth 1000000", which raises the elaborator's depth of recursion. That likeness
with "ownLaid" stands by the two texts alone: no lemma of this file ties them. "K1.firstAddr" stands
in the test's text and is not handed in, so no control turns that clause.
Not claimed: that each own message has an address: where "addrs" returns nothing the test asks
nothing. Anything on what is laid into a message: that wants "valsAt". No property of a release, of
a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.SeatsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.OwnData
import Johnson.Desc.ProofFile.Honest.K1.PlaceFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground)
open ProofFile.Honest (Addr MsgAddr)
open ProofFile.Honest.K2 (SwitchPlace SegmentPub switchPlaces segmentsOf switchSeat ownSeats)
open ProofFile.Honest.K2.Law (placesW segsW places_at_head segments_at_head)
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (layoutFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- At one address a of the own message number m of segment l. -/
def sortedOne (own : List (Addr × Nat × Nat)) (shape : ReqShape) (lay : ReqLayout)
    (u3 bz : List Seat) (l m : Nat) (a : MsgAddr) : Bool :=
  (ProofFile.Honest.K2.seatBy shape own a).isSome || a.sender == ProofFile.Honest.K1.firstAddr ||
    mineOf bz a ||
    (pairOf u3 a == some (l, m) &&
      ((lay.link.getD l []).filter fun A => A.message == m).map (·.name) == ["U3"])

/-- **THE TEST.** -/
def sortedBy (own : List (Addr × Nat × Nat)) (places : List SwitchPlace) (segs : List SegmentPub)
    (shape : ReqShape) (lay : ReqLayout) (u3 bz : List Seat) : Bool :=
  places.all fun p =>
    (segs.take p.link).zipIdx.all fun y =>
      (y.1.ownShapes (y.2 == 0)).zipIdx.all fun s =>
        (p.addrs y.2 s.2).all (sortedOne own shape lay u3 bz y.2 s.2)

/-- At a public part and a ground. -/
def sortedAt (Z : Pub) (G : Ground) : Bool :=
  sortedBy (ownSeats Z G) (switchPlaces Z G) (segmentsOf Z G) G.first.shape G.first.layout
    (seatsOf Z G "U3") (seatsOf Z G "BZ")

/-- The switches' own seats' list at the written places. -/
def ownW : List (Addr × Nat × Nat) :=
  placesW.map fun p => (⟨p.place, 0⟩, p.link, 1 + p.sizes.kept.length)

set_option maxRecDepth 1000000 in
/-- The test says yes at the written values. -/
theorem sortedW : sortedBy ownW placesW segsW proofSizedFull.request layoutFull (seatsW "U3")
    (seatsW "BZ") = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls: without the switches' own seats · without the seats of "U3" · without those of "BZ" ·
with the seats of "BZ" laid behind those of "U3" and none handed in for "BZ" (the digits' message is
then found among the first list's, and does not hold "U3" alone): the test says no. -/
theorem sortedW_can_fail :
    (sortedBy [] placesW segsW proofSizedFull.request layoutFull (seatsW "U3") (seatsW "BZ") ||
      sortedBy ownW placesW segsW proofSizedFull.request layoutFull [] (seatsW "BZ") ||
      sortedBy ownW placesW segsW proofSizedFull.request layoutFull (seatsW "U3") [] ||
      sortedBy ownW placesW segsW proofSizedFull.request layoutFull
        (seatsW "U3" ++ seatsW "BZ") []) = false := by decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD AND THE OPENING THE TEST SAYS YES.** -/
theorem sorted_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) : sortedAt Zp Bs.G₀ = true := by
  obtain ⟨-, e2, e3⟩ := first_at_head h O.blank
  unfold sortedAt ownSeats
  rw [places_at_head h.toAtMg O, segments_at_head h.toAtMg O, e2, e3, seats_at_head h O.blank,
    seats_at_head h O.blank]
  exact sortedW

/-- **UNDER THE HEAD AND THE OPENING: AN ADDRESS THAT IS NONE OF THE OTHER THREE IS THE READS'**: the
seats of "U3" name just the segment and the message at which it is asked, and the layout lays "U3"
alone into that message. -/
theorem reads_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    {y : SegmentPub × Nat} (hy : y ∈ ((segmentsOf Zp Bs.G₀).take p.link).zipIdx)
    {s : OnBytes.OracleShape × Nat} (hs : s ∈ (y.1.ownShapes (y.2 == 0)).zipIdx) {a : MsgAddr}
    (ha : p.addrs y.2 s.2 = some a) (n1 : (switchSeat Zp Bs.G₀ a).isSome = false)
    (n2 : (a.sender == ProofFile.Honest.K1.firstAddr) = false)
    (n3 : mineOf (seatsOf Zp Bs.G₀ "BZ") a = false) :
    pairOf (u3Seats Zp Bs.G₀) a = some (y.2, s.2) ∧
      ((Bs.G₀.first.layout.link.getD y.2 []).filter fun A => A.message == s.2).map (·.name) =
        ["U3"] := by
  have k := sorted_at_head h O
  unfold sortedAt sortedBy at k
  have k1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 k p hp) y hy) s hs
  rw [ha] at k1
  change sortedOne (ownSeats Zp Bs.G₀) Bs.G₀.first.shape Bs.G₀.first.layout
    (seatsOf Zp Bs.G₀ "U3") (seatsOf Zp Bs.G₀ "BZ") y.2 s.2 a = true at k1
  unfold sortedOne at k1
  have n1' : (ProofFile.Honest.K2.seatBy Bs.G₀.first.shape (ownSeats Zp Bs.G₀) a).isSome = false := n1
  rw [n1', n2, n3, Bool.false_or, Bool.false_or, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    beq_iff_eq] at k1
  exact k1

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.sortedW
#check @OnBytes.HonestTrace.U3.Fit.sortedW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.sorted_at_head
#check @OnBytes.HonestTrace.U3.Fit.reads_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.sortedW
#print axioms OnBytes.HonestTrace.U3.Fit.sortedW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.sorted_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.reads_at_head
