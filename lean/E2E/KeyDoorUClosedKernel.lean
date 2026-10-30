-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyDoorUClosedKernel.lean

The closed lines at the key's test on G_u that Accepted at 9 asks, BY THE KERNEL's OWN EVALUATION, each with a
control but `plans_U`, whose second line is a second yes: the eight's planOk is F7's `plan_eight` too. It imports KeyDoorUClosedGuards.lean, where the evaluator says the same first. Those over doorU are
the ones that the kernel may not bear: one that it will not bear is a finding.

Limits. Public numbers and shapes at QK, PF. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyDoorUClosedGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyDoorUClosed
open H2K.Member (piKUFull piKOFull)
open AtPublicFiles.AtFiles.Full (QK)
open VerifiableInference.Desc.Ground.Sh (stTidyB)
open ProofFile.Honest.Sh (claimsB)
open ProofFile.Honest.K14 (jobU jobOmega sendingsFit)

theorem front_U : frontFiveB piKUFull QK.codes shapeU = true := by decide +kernel
theorem front_U_place : frontFiveB piKOFull QK.codes shapeU = false := by decide +kernel
theorem front_U_mask : frontFiveB piKUFull QK.codes { shapeU with mask := none } = false := by
  decide +kernel

theorem many_U : manyFitsS piKUFull msU bareU.trees (ProofFile.Honest.Sh.thinOf shapeU) = true := by
  decide +kernel
theorem many_U_trees :
    manyFitsS piKUFull msU bareU.trees.dropLast (ProofFile.Honest.Sh.thinOf shapeU) = false := by
  decide +kernel
theorem many_U_mems :
    manyFitsS piKUFull msU.dropLast bareU.trees (ProofFile.Honest.Sh.thinOf shapeU) = false := by
  decide +kernel

theorem ts_U : tsLenOf piKUFull (ProofFile.Honest.Sh.thinOf shapeU) = 2 := by decide +kernel
theorem ts_U_g : tsLenOf piKUFull (ProofFile.Honest.Sh.thinOf { shapeU with g := 99 }) ≠ 2 := by
  decide +kernel

theorem three_U : threeL fallUK = [true, true, true] := by decide +kernel
theorem three_U_g : claimsB { fallUK with g := 99 } = false := by decide +kernel
theorem three_U_bare : stTidyB { fallUK with st := { fallUK.st with oracles := #[] } }.st = false := by
  decide +kernel

theorem opens_U : opensAtU false [24, 13] [.own 0, .own 2] 3 = true := by decide +kernel
theorem opens_U_sent : opensAtU false [24, 13] [.own 0, .own 2] 4 = false := by decide +kernel
theorem opens_U_depth : opensAtU false [23, 13] [.own 0, .own 2] 3 = false := by decide +kernel
theorem opens_U_src : opensAtU false [24, 13] [.own 1, .own 2] 3 = false := by decide +kernel
theorem opens_U_word : opensAtU true [24, 13] [.own 0, .own 2] 3 = false := by decide +kernel

theorem ells_U : ellsB AQ = true := by decide +kernel
theorem ells_U_codes : ellsB (planOf ⟨#[], #[]⟩ default) = false := by decide +kernel

theorem sendings_U : sendingsFit QK = true := by decide +kernel
theorem sendings_U_codes : sendingsFit { QK with codes := ⟨#[], #[]⟩ } = false := by decide +kernel

theorem width_U : widthFits (jobU AQ) 0 = true ∧ widthFits (jobOmega AQ) 1 = true := by decide +kernel
theorem width_U_five : widthFits (jobU AQ) 5 = false ∧ widthFits (jobOmega AQ) 5 = false := by
  decide +kernel

theorem room_U : roomU = true := by decide +kernel
theorem room_U_z : 2 * (stage₀ piKUFull).k + 1 > (stage₀ piKUFull).h := by decide +kernel

theorem depth_U : bareU.trees.map (·.1) = [24, 13] := by decide +kernel
theorem depth_U_bent : bareU.trees.map (·.1) ≠ [24, 14] := by decide +kernel

theorem plans_U : hpB = true := by decide +kernel
theorem plans_U_eight : (Desc.K14.blocks QK).map (·.length) = some 8 := by decide +kernel

end ProofFile.Honest.K12.Light.KeyDoorUClosed

#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.front_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.front_U_place
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.front_U_mask
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.many_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.many_U_trees
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.many_U_mems
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.ts_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.ts_U_g
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.three_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.three_U_g
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.three_U_bare
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.opens_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.opens_U_sent
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.opens_U_depth
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.opens_U_src
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.opens_U_word
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.ells_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.sendings_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.sendings_U_codes
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.width_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.width_U_five
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.room_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.depth_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.depth_U_bent
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.plans_U
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.plans_U_eight
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.ells_U_codes
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.room_U_z
