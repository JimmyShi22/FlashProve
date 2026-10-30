-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/PlanWritten/SizedTies.lean: the written values of
Johnson/Desc/Ok/PlanWritten/SizedLit.lean are the values that other files of the library have
written for the same things.

The library holds the link's sizes at the full size as `recordLink`, `recordTable`, `recordG1` and
`recordStages`, and the setting as `recordSet` (OnBytes/Params/EntryStagesRecord.lean), and the
codes of the proof file's chains as `codesFull2` (Johnson/G/PackLit.lean). SizedLit.lean spells
these values a second time, from a print. A public quantity that is written twice wants a tie. Here
are three.

Row or tool. Every declaration here is a tool: an equation between closed written values.

What is here, each by an evaluation in Lean's kernel.
  `linkSizedFull_eq`: `linkSizedFull` is `⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩`:
    the value that `record_link` (OnBytes/Params/EntryParamsRecord.lean) proves the sizing of a link
    to return at the record's lines.
  `proofCodes_eq`: `proofSizedFull.codes` is `codesFull2`.
  `proofSet_eq`: `proofSizedFull.set` is `recordSet`.

Limits. The other fields of `proofSizedFull`, and `sixFull`, are tied to no other written value
here. An equation between two written values says nothing of what a planner makes. Nothing on
soundness.


-/
import Johnson.Desc.Ok.PlanWritten.Sized
import OnBytes.Params.EntryStagesRecord
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes.Params

/-- The link's written sizes are the record's. -/
theorem linkSizedFull_eq :
    linkSizedFull = ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩ := by
  decide +kernel

/-- The proof file's written codes are the library's other written codes. -/
theorem proofCodes_eq : proofSizedFull.codes = Johnson.G.codesFull2 := by decide +kernel

/-- The proof file's written setting is the record's. -/
theorem proofSet_eq : proofSizedFull.set = recordSet := by decide +kernel

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.linkSizedFull_eq
#print axioms VerifiableInference.PlanWritten.proofCodes_eq
#print axioms VerifiableInference.PlanWritten.proofSet_eq
