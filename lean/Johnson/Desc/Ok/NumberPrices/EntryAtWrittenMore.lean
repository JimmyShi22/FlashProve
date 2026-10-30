-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/EntryAtWrittenMore.lean: further facts and negative tests on the entry
file's written priced plan and its test (Johnson/Desc/Ok/NumberPrices/EntryAtWritten.lean,
EntryAtWrittenTeeth.lean), each one evaluation in Lean's kernel.

Facts on a written value, and on that value bent here. No row is to be laid on them.

What is here.
  `entry_once`: every round of the plan has the scope "once", and the setting has one instance. So
    none of the planner's factors for a number of requests is in these errors. `scope` is the
    written record's own word.
  `record_not_passed_41`: held against the plan's first 41 entries, "RECORD" among them, the data's
    41 entries are not these. The two lists are of one length, so it is the entries that part.
  `short_all`, `long_all`: with the last round dropped, and with one round more, `Desc.chainAll 32`
    still says yes: so in `short_no` and `long_no` it is the comparison of entries that says no.
  `workAt`, `entryWork31`: the plan with 31 bits of work for 32 at its round 4, "LINK".
    `work31_all`: `Desc.chainAll 32` says yes there: the price has room for one bit.
    `work31_not_aligned`, `work31_no`: the comparison of entries alone refuses it: the price would
    stand at one bit of work less than the data's round counts.
  `all_31_no`: `Desc.chainAll 31` says no at the written plan: the bound 32 on a round's work has no
    slack.

Limits. Those of the two files named. Nothing on soundness.


-/
import Johnson.Desc.Ok.NumberPrices.EntryAtWrittenTeeth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open _root_.Run OnBytes.Params OnBytes.Slice OnBytes.Flat OnBytes.Flat.Held
open OnBytes.Maker Johnson.G

/-- Every round of the plan has the scope "once", and the setting has one instance. -/
theorem entry_once :
    (pricedEntryFull.rounds.all fun r => decide (r.scope = .once)) = true ∧
      pricedEntrySetFull.instances = 1 := by decide +kernel

/-- Held against the plan's first 41 entries, the data's 41 entries are not these. -/
theorem record_not_passed_41 :
    decide (frD.ds.map (·.entry) = pricedEntryFull.rounds.dropLast.map (·.entry)) = false := by
  decide +kernel

/-- With the last round dropped the test on the plan alone still says yes. -/
theorem short_all : Desc.chainAll 32 shortEntry = true := by decide +kernel

/-- With one round more it still says yes. -/
theorem long_all : Desc.chainAll 32 longEntry = true := by decide +kernel

/-- The rounds with the work of the round i set to w. -/
def workAt : ℕ → ℕ → List PlanRound → List PlanRound
  | _, _, [] => []
  | 0, w, r :: rs => { r with entry := { r.entry with work := w } } :: rs
  | i + 1, w, r :: rs => r :: workAt i w rs

/-- The plan with 31 bits of work for 32 at its round 4, "LINK". -/
def entryWork31 : Planned := ⟨pricedEntrySetFull, workAt 4 31 pricedEntryRoundsFull⟩

/-- The test on the plan alone says yes there. -/
theorem work31_all : Desc.chainAll 32 entryWork31 = true := by decide +kernel

/-- The comparison of entries says no. -/
theorem work31_not_aligned : decide (Aligned frD.ds entryWork31) = false := by decide +kernel

/-- **So the test says no.** -/
theorem work31_no : entryLitOk entryWork31 = false := by decide +kernel

/-- The bound 32 on a round's work has no slack. -/
theorem all_31_no : Desc.chainAll 31 pricedEntryFull = false := by decide +kernel

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.entry_once
#print axioms VerifiableInference.Number.ByRuns.record_not_passed_41
#print axioms VerifiableInference.Number.ByRuns.short_all
#print axioms VerifiableInference.Number.ByRuns.long_all
#print axioms VerifiableInference.Number.ByRuns.work31_all
#print axioms VerifiableInference.Number.ByRuns.work31_not_aligned
#print axioms VerifiableInference.Number.ByRuns.work31_no
#print axioms VerifiableInference.Number.ByRuns.all_31_no
