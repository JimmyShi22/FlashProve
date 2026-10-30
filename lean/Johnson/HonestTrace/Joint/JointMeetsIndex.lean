-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/JointMeetsIndex.lean

Nothing on hiding. No property of the protocol is claimed.
ONE LAW, which the files on the trace over the matrices share: at a matrix that holds an index, "fullIn"'s trace read through
"indexOf" (the field "trace" of "matrixInput") is "fullIn"'s trace at that index, there or not. It stands apart so that a
file that needs it alone need not import what JointMeetsPlug.lean imports.
Limit: "indexOf" is by choice: no program computes it.
-/
import Johnson.Desc.ProofFile.Honest.AtPureFullIn
import Johnson.Flat.LedgerClaim
import E2E.ObjectAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open ProofFile.Honest (fullIn)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open VerifiableInference.OnPublicFiles.Flat (indexOf Holds)

/-- At a matrix that holds an index, the trace of "fullIn" read through the index that the matrix
holds is the trace of "fullIn" at that index, there or not. -/
theorem fullIn_trace_through_of_holds (Zp : ProofFile.Pub) {M : FullSizeMatrix} {i : Cm.Idx}
    (hi : Holds M i) (ξ : ProofFile.Inst) :
    ((indexOf M).bind fun j => fullIn.trace Zp j ξ) =
      fullIn.trace Zp i ξ := by
  have e := VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl hi
  exact congrArg (fun o : Option Cm.Idx => o.bind fun j => fullIn.trace Zp j ξ) e

end HonestTraceRun.Meets

#print axioms HonestTraceRun.Meets.fullIn_trace_through_of_holds
