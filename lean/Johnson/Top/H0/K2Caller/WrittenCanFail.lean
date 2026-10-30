-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/WrittenCanFail.lean: the test `SwRow.writtenOK` of WrittenMeets.lean can
fail at the written records of the small example: at each of the 5 it says no if the sending has no
tree; if the first sample's cube has 2 ^ 70 variables; if the group in front has positions of 65
bits. Evaluations in Lean's kernel, a theorem for each record.
  alteredW: three altered records of a record
  small_written_can_fail: the test says no at each
A file of controls: WrittenCanFailFull.lean alone imports it.
Limits: written numbers; three alterations; which clause of the test says no at an altered record is
not said. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WrittenMeets

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Lean checks this file's theorems one after another, not side by side: as measured, the peak of
-- memory is then lower and steadier.
set_option Elab.async false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params

/-- Three altered records of a record. -/
def alteredW (r : SwRow) : List SwRow :=
  [{ r with roots := 0 },
    { r with o := r.o.modifyHead fun x => { x with cubeBits := 2 ^ 70 } },
    { r with g := { r.g with main := { r.g.main with logN := 65 } } }]

set_option maxRecDepth 1000000 in
theorem small0_wfails :
    ((alteredW (smallAt 0)).all fun x => !x.writtenOK) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small1_wfails :
    ((alteredW (smallAt 1)).all fun x => !x.writtenOK) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small2_wfails :
    ((alteredW (smallAt 2)).all fun x => !x.writtenOK) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small3_wfails :
    ((alteredW (smallAt 3)).all fun x => !x.writtenOK) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small4_wfails :
    ((alteredW (smallAt 4)).all fun x => !x.writtenOK) = true := by decide +kernel

/-- The test can fail. -/
theorem small_written_can_fail :
    (tableSmallLit.all fun r => (alteredW r).all fun x => !x.writtenOK) = true :=
  small_all _ small0_wfails small1_wfails small2_wfails small3_wfails small4_wfails

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.small_written_can_fail
