-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/ProofLinPoint.lean: the factor for the requests of a batch stands
inside the written error of the round "LIN point" of the proof file's second written priced plan
(Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean).

The second chain of a proof file is shared by the requests of a batch. The planner's text prices its
round "LIN point", the point that all requests share, at the number of requests times degree / |E|,
plus the closeness term of the fold of the table's rows (`planLinShared`,
OnBytes/Params/Planner.lean). The planner's text has two more places for a factor: a round in a
request's own scope is multiplied by the setting's number of instances where that is above 1
(`close`), and the combinations of the smallness test grow with its logarithm (`rngCombinations`).
Both are idle here: the written setting has one instance.

Definitions.
  `linPointAt n`: that price at n requests, at the written setting and table and the written number
    of low variables: (n times `fieldError` at the 18 variables of the point, plus `tableFoldError`
    at the later distance), as an error from above.
Statements.
  `lin_point_written`: the second written plan (`pricedProofRecsFull1`,
    Johnson/Desc/ProofFile/Written/Priced.lean) has one distinct round under the name "LIN point";
    it draws the point's 18 elements, and its error is `linPointAt 64`. `lin_point_slots`: 64 is the
    written lines' number of slots.
  `one_instance`: the written setting of the proof file's plans has one instance.
  `lin_point_one`: `linPointAt 1` is another number, and `linPointAt 65` too.
By evaluations in Lean's kernel (`decide +kernel`): all.

What of OnBytes/Model/ is used: nothing.

Limits. Whether the other rounds of the shared chain need a factor for the requests is a matter of
the protocol's analysis: the format's page (docs/format/FORMAT.md, section 18, condition 10) names
this round in its condition on the number of requests, and does not say that no other round has one.
The term with the factor is small beside the closeness term (no statement here shows it). That
`linPointAt` is the planner's expression is a reading of `planLinShared`'s text: no theorem ties the
two. That the error bounds a count is not said here. The written plan stands on prints of the
library's own planner (see the head of Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean).
Nothing on soundness.
-/
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open OnBytes OnBytes.Params Johnson.G

/-- The planner's price of the round "LIN point" of a later test at n requests, at the written
setting and table. -/
def linPointAt (n : ℕ) : Binary :=
  (Bound.ofNat n * fieldError recordSet (recordTable.v + 7) +
    tableFoldError recordSet recordTable (tableAnalysis recordSet recordTable).later).error

set_option maxRecDepth 1000000 in
/-- **The written error of "LIN point" is the planner's price at 64 requests.** -/
theorem lin_point_written :
    (pricedProofRecsFull1.filter fun r => r.entry.name == "LIN point").map
        (fun r => (r.entry.drawE, r.error)) = [(recordTable.v + 7, linPointAt 64)] := by
  decide +kernel

/-- The written setting of the proof file's plans has one instance. -/
theorem one_instance : pricedProofSetFull.instances = 1 := by decide +kernel

/-- 64 is the written lines' number of slots. -/
theorem lin_point_slots : recordLines.slots = 64 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At one request, and at 65, the price is another number. -/
theorem lin_point_one : linPointAt 1 ≠ linPointAt 64 ∧ linPointAt 65 ≠ linPointAt 64 := by
  decide +kernel

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.lin_point_written
#print axioms VerifiableInference.Number.ByRuns.one_instance
#print axioms VerifiableInference.Number.ByRuns.lin_point_slots
#print axioms VerifiableInference.Number.ByRuns.lin_point_one
