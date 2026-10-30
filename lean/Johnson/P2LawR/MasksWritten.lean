-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/MasksWritten.lean: THE KIND "LOOKUP" (K3): THE MASKS' TESTS maskTestsB (×25 at the
calls, ×25 at the digits) AND oneShapeB's CORE, AT WRITTEN VALUES, BY LEAN's KERNEL. Closed terms
and closed facts alone: no head, no public file. Each fact with a control that rejects.
  sentW the written codes and shape as the lookups' public data (its layout is the written one; its
      tables of names are empty: NO TEST HERE READS EITHER).
  numsW   the written seats' numbers, filled off the written list of what the sub-protocols tell.
  callsW l · digitsW l   the two tests' texts at these terms, at segment l.
  **calls_written · digits_written**   they accept at all 25 segments.
  calls_control · digits_control NEGATIVE TESTS: with every seat taken one member higher each
      rejects AT EACH of the 25.
  shapesP ps · **shapes_written** any two sampled seats of the written plan at one (tree, tenant)
      have one shape.
  shapes_control   A NEGATIVE TEST: the same test on the seats' trees alone rejects.
Limits. NOTHING TIES THESE TERMS TO A HEAD HERE: that is Johnson/P2LawR/MasksAtHead.lean's. The full
size alone. The written values rest on their own files' heads. Raised limits: maxRecDepth 1000000
and maxHeartbeats 4000000 at the six closed facts. Nothing on soundness.

-/
import Johnson.Desc.First.Look.K3Base
import Johnson.Desc.First.Look.K3MaskOkTools
import Johnson.Desc.First.Look.K3DigitsMaskOk
import Johnson.Desc.First.Att.K05MasksAtt
import Johnson.Desc.First.SentAtMoment
import Johnson.Desc.First.CutWritten
import Johnson.HB.LLHARD.LaidWritten
import Johnson.P5T.PlanSeatsFull
import Johnson.P5T.SeatsAt
import Johnson.P5J.LettersAt
import Johnson.Goal.Numbers.RequestWritten
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P2Law.K3M
open VerifiableInference.OnPublicFiles (maskTestsB maskOwnIx k3K)
open VerifiableInference.Desc.First (Numbers toldCut flatPlacesOf)
open VerifiableInference.Desc.First.Look (Sent keptAt)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open VerifiableInference.Desc.First.FillSent (sentDataAt ownAt)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open VerifiableInference.Desc.Sound (linksFull)

/-- The written codes and shape, as the lookups' public data. -/
def sentW : Sent :=
  ⟨VerifiableInference.PlanWritten.proofSizedFull.codes, VerifiableInference.Desc.ReqLit.shapeFull,
    Johnson.G.layoutFull, #[]⟩

/-- The written seats' numbers, filled off what the sub-protocols tell, as written. -/
def numsW : Numbers := P5T.N0Full.withTold P5J.At.ps toldCut

/-- The masks' test at a segment's calls, at the written terms; up: how far the seats are
shifted. -/
def callsW (up l : ℕ) : Bool :=
  maskTestsB (maskMsg sentW l) (keptAt sentW l).length
    ((sentDataAt sentW.shape numsW P5J.At.links P5J.At.ps #[]).own l) numsW
    (flatPlacesOf linksFull true)[k3K l false + 1]? LFull MFull (numsW.sent l 0)
    (fun j => P6T.seatCallsT P5T.psFull sentW l (j + up))

/-- The masks' test at a segment's digits, at the written terms. -/
def digitsW (up l : ℕ) : Bool :=
  maskTestsB (maskOwnIx sentW l) 0 (ownAt sentW.shape numsW P5J.At.links P5J.At.ps #[] l 3) numsW
    (flatPlacesOf linksFull true)[k3K l true + 1]? LFull MFull (numsW.group l)
    (fun j => P6T.seatT P5T.psFull l (j + up))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **At the calls: all 25 accept.** -/
theorem calls_written : (List.range 25).all (callsW 0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- A NEGATIVE TEST: every seat one member higher: each of the 25 rejects. -/
theorem calls_control : (List.range 25).all (fun l => !callsW 1 l) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **At the digits: all 25 accept.** -/
theorem digits_written : (List.range 25).all (digitsW 0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- A NEGATIVE TEST: every seat one member higher: each of the 25 rejects. -/
theorem digits_control : (List.range 25).all (fun l => !digitsW 1 l) = true := by decide +kernel

/-- Any two sampled seats of a plan at one key have one shape. -/
def shapesP {κ : Type} [DecidableEq κ] (key : P5T.PSeat → κ) (ps : List P5T.PSeat) : Bool :=
  (ps.filter (·.smpd)).all fun p => (ps.filter (·.smpd)).all fun q =>
    !decide (key p = key q) || p.shape == q.shape

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **One seat, one shape, at the written plan.** -/
theorem shapes_written : shapesP (·.seat) P5T.psFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- A NEGATIVE TEST: by the tree alone the test rejects. -/
theorem shapes_control : shapesP (·.seat.1) P5T.psFull = false := by decide +kernel

end P2Law.K3M

#print axioms P2Law.K3M.calls_written
#print axioms P2Law.K3M.calls_control
#print axioms P2Law.K3M.digits_written
#print axioms P2Law.K3M.digits_control
#print axioms P2Law.K3M.shapes_written
#print axioms P2Law.K3M.shapes_control
