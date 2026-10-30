-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/CellsWritten.lean: THE KIND K9 (a link's batching): THE TWO TESTS ON PUBLIC DATA THAT
THE SENTENCE cells OF hLeft STILL NAMES (seatsPubB · shapesPubB,
Johnson/Desc/First/Link/Law/CellTests.lean), AT WRITTEN VALUES, AT ALL 25 LINKS, BY LEAN's KERNEL.
Closed terms and closed facts alone: no head, no public file. Each fact with a control that rejects.
In the manner of Johnson/P2LawR/MasksWritten.lean, whose sentW and numsW are called.
  digW m   the link's own oracle messages, all moments, at the written shape, the radii at 0.
  cellSeatsW up m · cellShapesW M m the two tests' texts at the written terms, at the place of link
      m's batching.
  **cellSeats_written · cellShapes_written**   they accept at all 25 links.
  cellSeats_control · cellShapes_control NEGATIVE TESTS: with every seat taken one member higher,
      and with the list of shapes begun one message later, each rejects AT EACH of the 25.
Limits. NOTHING TIES THESE TERMS TO A HEAD HERE: that is Johnson/P2LawR/CellsAtHead.lean's. The full
size alone. The written values rest on their own files' heads. Raised limits: maxRecDepth 1000000
and maxHeartbeats 4000000 at the four closed facts. Nothing on soundness.

-/
import Johnson.P2LawR.MasksWritten
import Johnson.Desc.First.Link.Law.CellTests
import Johnson.Desc.First.Link.Law.K9KindTiedR
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P2Law.K9C
open OnBytes
open VerifiableInference.Desc.LinkJoin (seatsPubB shapesPubB batchAt)
open VerifiableInference.Desc.First (momentAt shiftAt)
open VerifiableInference.Desc.First.Look (sigList lastMoment)
open VerifiableInference.Desc.First.FillSent (ownAt)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open P2Law.K3M (sentW numsW)

/-- The link's own oracle messages, all moments, at the written shape; the radii at 0. -/
def digW (m : ℕ) : List (OracleShape × ℕ) := sigList sentW (fun _ => 0) m (lastMoment sentW m)

/-- seatsPubB at the written terms, at the place of link m's batching; up: how far the seats are
shifted. -/
def cellSeatsW (up m : ℕ) : Bool :=
  (P5J.At.ps[batchAt P5J.fullLinks P5J.At.ps m]?).any fun p =>
    seatsPubB (ownAt sentW.shape numsW P5J.At.links P5J.At.ps #[] m
        (momentAt (shiftAt P5J.At.links m) p.piece)) numsW (some p) LFull (numsW.group m)
      (List.ofFn fun j : Fin (digW m).length => P6T.seatT P5T.psFull m (j.1 + up))

/-- shapesPubB at the written terms, against a list M of shapes. -/
def cellShapesW (M : List OracleShape) (m : ℕ) : Bool :=
  (P5J.At.ps[batchAt P5J.fullLinks P5J.At.ps m]?).any fun p =>
    shapesPubB (ownAt sentW.shape numsW P5J.At.links P5J.At.ps #[] m
        (momentAt (shiftAt P5J.At.links m) p.piece)) numsW (some p) M ((digW m).map (·.1))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The seats: all 25 accept.** -/
theorem cellSeats_written : (List.range 25).all (cellSeatsW 0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- A NEGATIVE TEST: every seat one member higher: each of the 25 rejects. -/
theorem cellSeats_control : (List.range 25).all (fun m => !cellSeatsW 1 m) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The shapes: all 25 accept.** -/
theorem cellShapes_written : (List.range 25).all (cellShapesW MFull) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- A NEGATIVE TEST: the list of shapes begun one message later: each of the 25 rejects. -/
theorem cellShapes_control :
    (List.range 25).all (fun m => !cellShapesW (MFull.drop 1) m) = true := by decide +kernel

end P2Law.K9C

#print axioms P2Law.K9C.cellSeats_written
#print axioms P2Law.K9C.cellSeats_control
#print axioms P2Law.K9C.cellShapes_written
#print axioms P2Law.K9C.cellShapes_control
