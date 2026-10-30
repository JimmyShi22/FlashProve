-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyNineLinesKernel.lean

KeyNineLinesGuards.lean's lines BY THE KERNEL's OWN EVALUATION, each with a control.

Limits. At `QK`, `keyBook`. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyNineLinesGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyDoorUClosed
open AtPublicFiles.KeyBook (atFull keyBook)
open H2K.Member (piKUFull piKOFull)

theorem members_U : (shapeU.core.st.groups[shapeU.g]?).map (·.members) = some [0, 3] := by
  decide +kernel

theorem members_U_next : (shapeU.core.st.groups[shapeU.g + 1]?).map (·.members) ≠ some [0, 3] := by
  decide +kernel

theorem col_fit : colFitsU AQ piKUFull = true := by decide +kernel

theorem col_bent : colFitsU AQ piKOFull = false := by decide +kernel

theorem fresh_fit : freshFitsU AQ piKUFull = true := by decide +kernel

theorem fresh_bent : freshFitsU AQ piKOFull = false := by decide +kernel

theorem cuts_fit : atFull (fun K => bookCutsU (keyBook K) AQ piKUFull) = true := by decide +kernel

theorem cuts_bent : atFull (fun K => !bookCutsU (keyBook K) AQ piKOFull) = true := by decide +kernel

end ProofFile.Honest.K12.Light.KeyDoorUClosed

#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.members_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.members_U_next
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.col_fit
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.col_bent
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.fresh_fit
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.fresh_bent
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.cuts_fit
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.cuts_bent
