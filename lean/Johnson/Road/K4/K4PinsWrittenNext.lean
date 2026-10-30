-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsWrittenNext.lean: THREE OF K4's TESTS ON THE INDEX MASKS' MESSAGE AS CLOSED
FACTS ON WRITTEN VALUES, DECIDED BY LEAN's KERNEL: `nextFitsB`
(Johnson/Road/K4/Rec/NextEntryStatement.lean), `maskFitsB`
(Johnson/Road/K4/Rec/MaskEntryStatement.lean), `indexTieB`
(Johnson/Road/K4/K4PinsAtWide.lean), each at all twelve groups, at: the written codes
(`proofSizedFull.codes`), the written shapes and seats (`mW`, `laidW?`,
Johnson/Road/K4/K4PinsSends.lean), the written numbers (`nW`, Johnson/Road/K4/K4PinsBook.lean), the
closed list of flags (`fvsFull`, Johnson/Road/K4/Riders/BuiltFvs.lean), the members by the make off
the written seats at the radii 0 (`listsW`, Johnson/Road/K4/K4PlanWritten.lean). Ten theorems, each
by `decide +kernel`.

  `free0_written`: the index masks' message has 255 free entries. (No negative test beside it.)
  THE NEGATIVE TESTS BELOW STAND AT GROUP 0 ALONE.
  `nextFits_written` · NEGATIVE: `nextFits_written_no` (one free entry more is claimed) ·
    `nextFits_written_no'` (in front of the sending that tells the message).
  `maskFits_written` · NEGATIVE: `maskFits_written_no` (all 255 entries are taken) ·
    `maskFits_written_no'` (one tree fewer is told).
  `indexTie_written` · NEGATIVE: `indexTie_written_no` (the numbers name another tenant) ·
    `indexTie_written_no'` (more entries are read than the message's mask rows hold).

Limits. K04_law IS NOT PROVED BY THIS. CLOSED FACTS, OUTSIDE THE VERIFIER: no theorem of this file
names the public parameters Z: the carrying stands in Johnson/Road/K4/K4PinsPaid.lean. The written
values rest on prints of Lean's evaluator (their files' heads). The full size alone.
-/
import Johnson.Road.K4.K4PinsBook
import Johnson.Road.K4.K4PinsSends
import Johnson.Road.K4.K4PinsAtWide
import Johnson.Road.K4.K4PlanWritten
import Johnson.Road.K4.Riders.BuiltFvs
import Johnson.Road.K4.Rec.NextEntryStatement
import Johnson.Road.K4.Rec.MaskEntryStatement
import Johnson.Top.H0.Fill.D1At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.First (flatPlacesOf FillP1.free0Of)
open VerifiableInference.Desc.Sound (linksFull msOf)
open OnBytes.Road.K4.Rec (nextFitsB maskFitsB)
open OnBytes.Road.K4.Riders (fvsFull)

/-- the table's own list of places -/
local notation "𝐩𝐬" => (flatPlacesOf linksFull true)

/-- the written codes -/
local notation "𝐜𝐬" => proofSizedFull.codes

set_option maxRecDepth 1000000 in
/-- The index masks' message has 255 free entries. -/
theorem free0_written : FillP1.free0Of 𝐜𝐬 mW nW.indexNo = 255 := by decide +kernel

/-! ## The next entry's name -/

set_option maxRecDepth 1000000 in
/-- **At the written values the test accepts at all twelve groups.** -/
theorem nextFits_written :
    ((List.range 12).all fun g =>
      nextFitsB 𝐜𝐬 mW (nW.msgsAt 𝐩𝐬[28 * g + 4 + 1]?) nW.indexNo
        (FillP1.free0Of 𝐜𝐬 mW nW.indexNo) fvsFull (2 * g)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one free entry more is claimed. -/
theorem nextFits_written_no :
    nextFitsB 𝐜𝐬 mW (nW.msgsAt 𝐩𝐬[28 * 0 + 4 + 1]?) nW.indexNo
      (FillP1.free0Of 𝐜𝐬 mW nW.indexNo + 1) fvsFull 0 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: in front of the sending that tells the message. -/
theorem nextFits_written_no' :
    nextFitsB 𝐜𝐬 mW (nW.msgsAt 𝐩𝐬[2]?) nW.indexNo (FillP1.free0Of 𝐜𝐬 mW nW.indexNo) fvsFull 0 =
      false := by
  decide +kernel

/-! ## The mask entry -/

set_option maxRecDepth 1000000 in
/-- **At the written values the test accepts at all twelve groups**, g entries being taken. -/
theorem maskFits_written :
    (laidW?.any fun L => (List.range 12).all fun g =>
      maskFitsB 𝐜𝐬 mW L (nW.msgsAt 𝐩𝐬[28 * g + 4 + 1]?) (nW.treesAt 𝐩𝐬[28 * g + 4 + 1]?)
        nW.indexNo g) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: all 255 entries are taken. -/
theorem maskFits_written_no :
    (laidW?.any fun L =>
      maskFitsB 𝐜𝐬 mW L (nW.msgsAt 𝐩𝐬[28 * 0 + 4 + 1]?) (nW.treesAt 𝐩𝐬[28 * 0 + 4 + 1]?)
        nW.indexNo 255) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one tree fewer is told. -/
theorem maskFits_written_no' :
    (laidW?.any fun L =>
      maskFitsB 𝐜𝐬 mW L (nW.msgsAt 𝐩𝐬[28 * 0 + 4 + 1]?) (nW.treesAt 𝐩𝐬[28 * 0 + 4 + 1]? - 1)
        nW.indexNo 0) = false := by
  decide +kernel

/-! ## The tie of the index masks' message -/

set_option maxRecDepth 1000000 in
/-- **At the written values the test accepts at all twelve groups**, g + 1 entries being read. -/
theorem indexTie_written :
    (laidW?.any fun L => (List.range 12).all fun g =>
      indexTieB 𝐜𝐬 mW L.places (msOf listsW) nW (g + 1)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the numbers name another tenant. -/
theorem indexTie_written_no :
    (laidW?.any fun L =>
      indexTieB 𝐜𝐬 mW L.places (msOf listsW) { nW with index := (1, 1) } 1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: more entries are read than the message's mask rows hold. -/
theorem indexTie_written_no' :
    (laidW?.any fun L => indexTieB 𝐜𝐬 mW L.places (msOf listsW) nW 257) = false := by
  decide +kernel

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.free0_written
#print axioms OnBytes.Road.K4.nextFits_written
#print axioms OnBytes.Road.K4.nextFits_written_no
#print axioms OnBytes.Road.K4.nextFits_written_no'
#print axioms OnBytes.Road.K4.maskFits_written
#print axioms OnBytes.Road.K4.maskFits_written_no
#print axioms OnBytes.Road.K4.maskFits_written_no'
#print axioms OnBytes.Road.K4.indexTie_written
#print axioms OnBytes.Road.K4.indexTie_written_no
#print axioms OnBytes.Road.K4.indexTie_written_no'
