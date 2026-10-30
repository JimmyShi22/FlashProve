-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsWrittenArrays.lean: K4's TEST ON THE SEGMENT's NINE ARRAYS AS A CLOSED FACT
ON WRITTEN VALUES, DECIDED BY LEAN's KERNEL: `arrayPlanB`'s text behind the look-up of the name
(`arrayArm`, Johnson/Road/K4/K4PinsAnyRad.lean: tied to `arrayPlanB` by a theorem at all letters),
at all
twelve groups, at the nine matrices' written owners, names and sizes (`ownerW`, `sizeW`,
Johnson/Road/K4/K4PlanNine.lean) and at the letters of Johnson/Road/K4/K4PinsWrittenMask.lean. Three
theorems, each by `decide +kernel`.

  `arrays_written` · NEGATIVE, AT GROUP 0 AND ITS FIRST MATRIX ALONE: `arrays_written_no'` (the
    seats read a tenant further). `arrays_written_no` (no tenant is the segment's) is no control: it
    cannot fail, because without a tenant `seatP` returns nothing at every plan.

Limits. K04_law IS NOT PROVED BY THIS. CLOSED FACTS, OUTSIDE THE VERIFIER: no theorem of this file
names the public parameters Z: the carrying stands in Johnson/Road/K4/K4PinsPaid.lean. The written
values rest on prints of Lean's evaluator (their files' heads). The full size alone.
-/
import Johnson.Road.K4.K4PinsWrittenMask

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open Meaning (nameOf)

/-- the table's own list of places -/
local notation "𝐩𝐬" => (flatPlacesOf linksFull true)

set_option maxRecDepth 1000000 in
/-- **At the written values the test at an array accepts at all nine, at all twelve groups.** -/
theorem arrays_written :
    (laidW?.any fun L => (List.range 12).all fun g => (List.range 9).all fun μ =>
      arrayArm sentW (fun _ => 0) (2 * g) (seatW (2 * g)) (ownSentW g) (recW L)
        (nW.msgsAt 𝐩𝐬[28 * g + 4]?) (2 * g) (Alg.symRows (sizeW μ).1) (sizeW μ).2
        ((ownerW g μ).1, nameOf (ownerW g μ).2)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A closed fact, no control: with no tenant at all `seatP` returns nothing at every plan, so the
test rejects whatever the other values are. -/
theorem arrays_written_no :
    (laidW?.any fun L =>
      arrayArm sentW (fun _ => 0) 0 (seatW 0) [] (recW L) (nW.msgsAt 𝐩𝐬[4]?) 0
        (Alg.symRows (sizeW 0).1) (sizeW 0).2 ((ownerW 0 0).1, nameOf (ownerW 0 0).2)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the seats read a tenant further. -/
theorem arrays_written_no' :
    (laidW?.any fun L =>
      arrayArm sentW (fun _ => 0) 0 (fun j => ((seatW 0 j).1, (seatW 0 j).2 + 1)) (ownSentW 0)
        (recW L) (nW.msgsAt 𝐩𝐬[4]?) 0 (Alg.symRows (sizeW 0).1) (sizeW 0).2
        ((ownerW 0 0).1, nameOf (ownerW 0 0).2)) = false := by
  decide +kernel

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.arrays_written
#print axioms OnBytes.Road.K4.arrays_written_no
#print axioms OnBytes.Road.K4.arrays_written_no'
