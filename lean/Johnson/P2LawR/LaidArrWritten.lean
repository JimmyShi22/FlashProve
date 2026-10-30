-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LaidArrWritten.lean: THE KIND K9 (a link's batching): AT THE WRITTEN LAYOUT, CODES
AND SHAPE: EVERY ARRAY OF EVERY ONE OF THE 25 LINKS PASSES THE PROGRAMS' OWN TEST ON ITS LAYOUT
(laidMatrixOk, OnBytes/Iop/ReqRows.lean) AT THE BITS THAT ITS OWN ORACLE MESSAGE's SHAPE AND THE
CODES GIVE. One closed fact by Lean's kernel, with a control. For laidArrB
(Johnson/Desc/First/Link/Law/CellPub.lean): whichever array a link's list names, it passes.
  laidLinkW less i the test, at every array of link i; less: how many bits are taken off the table's
      rows.
  **laidAll_written**   it accepts.
  laidAll_control A NEGATIVE TEST: with one bit less for the table's rows EACH of the 25 links has
      an array that fails.
Limits. A fact on written terms alone: nothing ties them to a head here
(Johnson/P2LawR/LaidArrAtHead.lean). Where an array's message's number lies outside the link's list
the test is silent: that it lies inside is asked elsewhere. The full size alone. Raised limits:
maxRecDepth 1000000 and maxHeartbeats 4000000 at the two closed facts. Nothing on soundness.

-/
import Johnson.P2LawR.CellsWritten
import Johnson.Desc.First.Link.Law.CellPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P2Law.K9C
open OnBytes
open VerifiableInference.Desc.K9 (rowBitsOf placeBitsOf)
open P2Law.K3M (sentW)

/-- At link i: every array passes, at its own message's bits; less: bits taken off the rows'. -/
def laidLinkW (less i : ℕ) : Bool :=
  ((sentW.layout.link[i]?).getD []).all fun a =>
    ((digW i)[a.message]?).all fun sh =>
      laidMatrixOk a (rowBitsOf sh.1 .main - less) (placeBitsOf sentW.codes sh.1 .main)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Every array of every link passes.** -/
theorem laidAll_written : (List.range 25).all (laidLinkW 0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- A NEGATIVE TEST: one bit less for the table's rows: each of the 25 links fails. -/
theorem laidAll_control : (List.range 25).all (fun i => !laidLinkW 1 i) = true := by
  decide +kernel

end P2Law.K9C

#print axioms P2Law.K9C.laidAll_written
#print axioms P2Law.K9C.laidAll_control
