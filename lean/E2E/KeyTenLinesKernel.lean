-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyTenLinesKernel.lean

KeyTenLinesGuards.lean's lines BY THE KERNEL's OWN EVALUATION, each with a control but `plan_U`. One more: the
place that the sim's facts name is `piKOFull`. Whether the kernel bears each at this size is part of the trial.

Limits. As in KeyTenLinesGuards.lean. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyTenLinesGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyDoorUClosed
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.KeyBook (atFull keyBook)
open H2K.Member (piKUFull piKOFull)
open ProofFile.Honest.Sh (claimsB)
open ProofFile.Honest.K14 (jobOmega)

theorem codes_O : shapeOm.core.st.codes = QK.codes := by decide +kernel

theorem codes_O_bent : shapeOm.core.st.codes ≠ ⟨#[], #[]⟩ := by decide +kernel

theorem door_O : doorAt piKOFull shapeOm = true := by decide +kernel

theorem door_O_g : doorAt piKOFull { shapeOm with g := 99 } = false := by decide +kernel

theorem door_O_mask : doorAt piKOFull { shapeOm with mask := some 0 } = false := by decide +kernel

theorem three_O : threeL fallOm = [true, true, true] := by decide +kernel

theorem three_O_g : claimsB { fallOm with g := 99 } = false := by decide +kernel

theorem plan_U : planU.all id = true := by decide +kernel

theorem ts_O : tsLenOf piKOFull (ProofFile.Honest.Sh.thinOf shapeOm) = 3 := by decide +kernel

theorem ts_O_g : tsLenOf piKOFull (ProofFile.Honest.Sh.thinOf { shapeOm with g := 99 }) ≠ 3 := by
  decide +kernel

theorem plain_O : frontPlainB₀ piKOFull (ProofFile.Honest.Sh.thinOf shapeOm) = true := by decide +kernel

theorem plain_O_g : frontPlainB₀ piKOFull (ProofFile.Honest.Sh.thinOf { shapeOm with g := 99 }) = false := by
  decide +kernel

theorem many_O : manyFitsS piKOFull msO bareO.trees (ProofFile.Honest.Sh.thinOf shapeOm) = true := by
  decide +kernel

theorem many_O_trees :
    manyFitsS piKOFull msO bareO.trees.dropLast (ProofFile.Honest.Sh.thinOf shapeOm) = false := by
  decide +kernel

theorem many_O_mems :
    manyFitsS piKOFull msO.dropLast bareO.trees (ProofFile.Honest.Sh.thinOf shapeOm) = false := by
  decide +kernel

theorem trees_O : bareO.trees.map (·.1) = [22, 13, 13] := by decide +kernel

theorem trees_O_bent : bareO.trees.map (·.1) ≠ [22, 13, 14] := by decide +kernel

theorem width_O_both : widthFits (jobOmega AQ) 0 = true ∧ widthFits (jobOmega AQ) 1 = true := by
  decide +kernel

theorem width_O_five : widthFits (jobOmega AQ) 5 = false := by decide +kernel

theorem col_O : colFitsOmega AQ piKOFull = true := by decide +kernel

theorem col_O_codes : colFitsOmega ⟨{ QK with codes := ⟨#[], #[]⟩ }, 0⟩ piKOFull = false := by
  decide +kernel

theorem fresh_O : freshFitsOmega piKOFull = true := by decide +kernel

theorem fresh_O_place : freshFitsOmega piKUFull = false := by decide +kernel

theorem cuts_O : atFull (fun K => bookCutsOmega (keyBook K) AQ piKOFull) = true := by decide +kernel

theorem cuts_O_place : atFull (fun K => !bookCutsOmega (keyBook K) AQ piKUFull) = true := by
  decide +kernel

theorem place_sim : ProofFile.Honest.K12.Light.pKO = piKOFull := by
  first
    | decide +kernel
    | rfl

end ProofFile.Honest.K12.Light.KeyDoorUClosed

#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.codes_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.codes_O_bent
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.door_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.door_O_g
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.door_O_mask
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.three_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.three_O_g
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.plan_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.ts_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.ts_O_g
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.plain_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.plain_O_g
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.many_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.many_O_trees
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.many_O_mems
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.trees_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.trees_O_bent
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.width_O_both
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.width_O_five
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.col_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.col_O_codes
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.fresh_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.fresh_O_place
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.cuts_O
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.cuts_O_place
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.place_sim
