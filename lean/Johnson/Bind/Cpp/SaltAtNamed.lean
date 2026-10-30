-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/SaltAtNamed.lean: the proposition `SaltAt` (Johnson/Bind/Cpp/Defs.lean: the frame's
salts have 40 bytes) at the two named sets of public files, `storedPublicFiles` and `zGap`.

Two theorems, each UNDER A PREMISE: that the tests on the public files pass (`protocolDataWellFormed`) at that set.
That the set is in scope is a theorem (`VerifierAndGoals.filesRead`). The premise is a closed equation between
two values of a type with two members. No theorem of the main library holds it. The side library
proves it at both sets with no premise (`theLive_zFull`, AtFullSide/Top/LiveAtFull.lean;
`theLive_zGap`, AtFullSide/Top/LiveAtPolicies.lean), under the limits of
AtFullSide/Top/LiveAtFull.lean.
The two theorems are `saltAt_of_live` (Johnson/Bind/Cpp/SaltAt.lean) at the two named sets, with "in
scope" proved. They trade one closed fact (the number is 40: evaluated below) for a stronger closed
fact (the tests pass): they serve whoever holds the stronger fact as a theorem, and say nothing to
whoever holds the first.
Then EVALUATIONS of the very term of which `SaltAt` speaks, at both sets, and at files that the
planner rejects. AN EVALUATION IS A RUN OF CODE, NO PROOF: Lean's kernel has not checked these
evaluations, and no theorem rests on them. WHERE THE EXPECTED VALUES COME FROM: the numbers 40 and 0
are written by hand from what the statements ask (`SaltAt` asks 40; where the planner rejects the
files the number is 0: `salt_of_refused`, Johnson/Bind/SaltPlan.lean); they are taken from no run of
the programs. The files at which they are evaluated are the library's own written copies
(Ladder/Stored.lean), which this file does not write anew. That file's head says whose bytes they
are meant to be and what of that is not tested, and: "The example's weights are synthetic
(lean/OnBytes/LIMITS.md)."

Limits. `SaltAt storedPublicFiles` and `SaltAt zGap` are no theorems of the main library without a premise. Not
among the evaluations below: files in scope other than the two named; files at which the planner
returns another number than 40 (none has been seen). Nothing on soundness, on correctness of
extraction or on a binding of the commitment.

-/
import Johnson.Bind.Cpp.SaltAt
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Bind.Cpp
open VerifierAndGoals FlashProve

/-- At the stored full-size files, where the tests on the public files pass (`protocolDataWellFormed`). -/
theorem saltAt_zFull (hl : protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true) : SaltAt storedPublicFiles :=
  saltAt_of_live filesRead.full.1 hl

/-- At the same files with the other policy, where the tests on the public files pass
(`protocolDataWellFormed`). -/
theorem saltAt_zGap (hl : protocolDataWellFormed (asDescriptionFiles zGap) = true) : SaltAt zGap :=
  saltAt_of_live filesRead.other.1 hl

/-! ## Evaluations: no proof -/

#guard saltLen storedPublicFiles == 40
#guard saltLen zGap == 40
-- Negative tests: the evaluation can say otherwise: at files that the planner rejects the number
-- is 0.
#guard saltLen ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty⟩ == 0
#guard saltLen { storedPublicFiles with KL := ByteArray.empty } == 0

end Bind.Cpp

#print axioms Bind.Cpp.saltAt_zFull
#print axioms Bind.Cpp.saltAt_zGap
