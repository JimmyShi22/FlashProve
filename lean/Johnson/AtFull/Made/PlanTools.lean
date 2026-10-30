-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/PlanTools.lean: three tests on a plan that is written as distinct rounds and
runs fall to tests on the distinct rounds and on the runs. General in the written plan.

A written plan (`Lit`, Johnson/G/RunsDefs.lean) holds a setting, the distinct rounds, and runs that
say which round stands how often in a row. The long plans of the full size have tens of thousands of
entries and few distinct rounds. The tests are those that the laws of
Johnson/AtFull/Made/ReadsOfConfigure.lean ask of a plan: `planB` (it fits the format's words, is in
order, and all its names are the format's) and `noSample` (it has no entry for a table's own
sample).

`namesKnown_of_lit`, `ok_of_lit`, `planB_of_lit`, `noSample_of_lit`. A test on all entries follows
from the same test on all distinct rounds' entries. The number of entries for a table's own sample
is counted along the runs.

Limits. The premises ask a test of every distinct round, also of one that no run names: more than is
needed. Nothing on soundness.
-/
import Johnson.AtFull.Made.ReadsOfConfigure
import Johnson.Desc.Ok.NumberPrices.ByRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.G.Runs
open VerifiableInference.Number.ByRuns (Lit entries_of_lit)

theorem namesKnown_of_lit (L : Lit)
    (h : ((L.recs.map (·.entry)).all fun e =>
      e.name == recordName || (kindOf e.name).isSome) = true) :
    namesKnown L.plan.plan = true := by
  unfold namesKnown
  rw [entries_of_lit]
  exact all_of_recs L.runs h

theorem ok_of_lit (L : Lit) (h1 : ((L.recs.map (·.entry)).all fun r => r.count == 1) = true)
    (h3 : cntG (fun e : Fmt.Entry => e.name == Fmt.recordName) 0
      (valRuns (L.recs.map (·.entry)) L.runs) ≤ 1) : L.plan.plan.ok = true := by
  have a : (L.plan.plan.entries.all fun r => r.count == 1) = true := by
    rw [entries_of_lit]
    exact all_of_recs L.runs h1
  have c : (L.plan.plan.entries.filter fun r => r.name == Fmt.recordName).length ≤ 1 := by
    rw [entries_of_lit, count_unrunG]
    exact h3
  unfold Fmt.Plan.ok
  rw [a, decide_eq_true c]
  rfl

theorem planB_of_lit (L : Lit) (hf : L.plan.plan.fit = true)
    (h1 : ((L.recs.map (·.entry)).all fun r => r.count == 1) = true)
    (h3 : cntG (fun e : Fmt.Entry => e.name == Fmt.recordName) 0
      (valRuns (L.recs.map (·.entry)) L.runs) ≤ 1)
    (h : ((L.recs.map (·.entry)).all fun e =>
      e.name == recordName || (kindOf e.name).isSome) = true) : planB L.plan.plan = true :=
  Bool.and_eq_true_iff.2 ⟨hf, Bool.and_eq_true_iff.2 ⟨ok_of_lit L h1 h3, namesKnown_of_lit L h⟩⟩

theorem noSample_of_lit (L : Lit)
    (h : ((L.recs.map (·.entry)).all fun e => !(e.name == recordName)) = true) :
    noSample L.plan.plan = true := by
  have t := all_of_recs L.runs h
  unfold noSample
  rw [entries_of_lit, Option.isNone_iff_eq_none, List.find?_eq_none]
  intro e he
  have k := List.all_eq_true.1 t e he
  simpa using k

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.namesKnown_of_lit
#print axioms Johnson.AtFull.Made.ok_of_lit
#print axioms Johnson.AtFull.Made.planB_of_lit
#print axioms Johnson.AtFull.Made.noSample_of_lit
