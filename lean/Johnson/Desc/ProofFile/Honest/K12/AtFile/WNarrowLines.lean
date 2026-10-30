-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WNarrowLines.lean: closed lines that tie the shape narrowW to the
written lists: the messages' shapes, places, trees' shapes, pads and codes, and which messages can sit
under the own group's codes.

Limits.
- Kernel evaluations at the written lists, nothing on any run.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WNarrowAtW
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.Own (padMade)

set_option maxRecDepth 1000000 in
theorem msgs_written : OnBytes.Road.K4.mW[4]? = some indexMsg.shape ∧
    OnBytes.Road.K4.mW[197]? = some wMsg.shape ∧ OnBytes.Road.K4.mW[198]? = some maskMsg.shape := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem places_written : LFull.places[4]? = some (1, 0) ∧ LFull.places[197]? = some (82, 0) ∧
    LFull.places[198]? = some (82, 1) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem treeShapes_written : LFull.shapes[1]? = some indexTree.shape ∧
    LFull.shapes[82]? = some wTree.shape := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem pads_written :
    ((padMade H2K.Member.codesFull indexMsg.shape).map fun l => l.map fun p => (p.part, p.index)) =
      some indexMsg.pad ∧
    ((padMade H2K.Member.codesFull wMsg.shape).map fun l => l.map fun p => (p.part, p.index)) =
      some wMsg.pad ∧
    ((padMade H2K.Member.codesFull omegaMsg.shape).map fun l => l.map fun p => (p.part, p.index)) =
      some omegaMsg.pad := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Of the written messages just three can sit under the own group's codes. -/
theorem ownCodes_written : (List.range 199).filter (fun o =>
    (OnBytes.Road.K4.mW[o]?).any fun s => (s.mainRows == 0 || s.code == 11) &&
      (s.maskRows == 0 || s.maskCode == 12)) = [4, 197, 198] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem codes_written : Johnson.G.codesFull2 = H2K.Member.codesFull := by
  decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.msgs_written
#print axioms ProofFile.Honest.K12.AtFile.places_written
#print axioms ProofFile.Honest.K12.AtFile.treeShapes_written
#print axioms ProofFile.Honest.K12.AtFile.pads_written
#print axioms ProofFile.Honest.K12.AtFile.ownCodes_written
#print axioms ProofFile.Honest.K12.AtFile.codes_written
