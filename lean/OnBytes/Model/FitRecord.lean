-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/FitRecord.lean: at the lines typed for the full-size parameter file of the setting
"record with work", what `configure` makes for an entry's chain is typed, and its plan is the plan
that is read back.

OnBytes/Params/EntryParamsRecord.lean proves what `entrySized` returns at `recordLines`. From a yes
of `configure`, `entrySized` on the same lines returns what `configure` has made for the entry's
chain (`configure_entrySized`, OnBytes/Model/FitFull.lean). So at `recordLines` the made link's
sizes (shape, table, test), the entry's codes and the entry's plan are the typed ones, and the plan
holds in the planner's reckoning, whatever the shapes, the digest and the bits
(`record_entry_made`). The entry's parameter bytes as made are spelled from the typed plan, codes
and shape and from the digest (`record_entryLink`); these are the bytes that `entryParams` returns
at these lines and that digest (`record_params`). The typed plan fits the format's words, so the
made plan does (`record_entry_fit`), and by OnBytes/Model/ReadBackMade.lean the plan that
`Link.read` returns on the made bytes is the made plan and the typed plan, with no hypothesis on
words left. The table has a record here: the chain's rounds as read back are the typed entries but
for the first, and the record as read back is the first (`record_entry_read`).

Main theorems: `record_entry_made`, `record_entryLink`, `record_entry_fit`, `record_entry_read`,
`record_params`.
What is not claimed: that `configure` says yes at `recordLines`, or that `Link.read` returns a
value: both are hypotheses (a test has both, at copies of the full-size public files:
OnBytes/Model/TestChainsBackRecord.lean [not in this library; so here read: not tested in this
library]; at one typed digest the second is a theorem:
OnBytes/Params/EntryDryRecord.lean). That the example's parameter file says `recordLines` (see the
head of OnBytes/Params/EntryStagesRecord.lean). Nothing on the other six plans. Nothing here on the
codes and the link's shape as read back. Nothing on what a round's price is worth under the rule
`johnson`, or on what a round's work is worth: the planner's reckoning counts proof of work toward
the target. The bytes are not typed out, and nothing is run dry here. For proofs only; the program,
that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Model.FitFull
import OnBytes.Params.EntryParamsRecord

set_option autoImplicit false

namespace OnBytes.Params

section
variable {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}

/-- **At `recordLines`, what `configure` has made for an entry's chain is typed**: the link's sizes
(shape, table, test), the chain's codes and the plan; and the plan holds in the planner's reckoning.
-/
theorem record_entry_made (h : configure recordLines x cfg bits = .ok made) :
    made.sized.link = ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩ ∧
      made.sized.entryCodes = recordCodes ∧ made.entry.plan = recordPlan ∧
      made.entry.holds = true := by
  obtain ⟨P, hy, hp, hh⟩ := record_sized
  rw [configure_entrySized h] at hy
  have e := Except.ok.inj hy
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  exact ⟨e1, e2, e3 ▸ hp, e3 ▸ hh⟩

/-- At `recordLines` the entry's parameter bytes as made are spelled from the typed plan, codes and
shape: they are what `entryParams` returns at these lines and the same digest (`record_params`). -/
theorem record_entryLink (h : configure recordLines x cfg bits = .ok made) :
    made.entryLink = Fmt.paramsBytes recordPlan cfg
      [("codes", spellCodes recordCodes), ("the link", spellLink recordLink)] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, e, _, _, _⟩ := configure_bytes h
  obtain ⟨e1, e2, e3, _⟩ := record_entry_made h
  rw [e, e3]
  unfold madeEntryItems
  rw [e2, e1]

/-- So the entry's made plan fits the format's words. -/
theorem record_entry_fit (h : configure recordLines x cfg bits = .ok made) :
    made.entry.plan.fit = true := (record_entry_made h).2.2.1 ▸ recordPlan_fit

/-- **The entry's plan as read back is the plan as made and the typed plan**; the chain's rounds as
read back are the typed entries but for the first, and the record as read back is the first. -/
theorem record_entry_read (h : configure recordLines x cfg bits = .ok made) {q : Link}
    (hq : Link.read made.entryLink = some q) :
    q.given.plan = made.entry.plan ∧ q.given.plan = recordPlan ∧
      q.given.rounds = recordPlan.entries.tail ∧ q.given.record = recordPlan.entries.head? := by
  have e : q.given.plan = recordPlan :=
    (entry_read_made h hq (record_entry_fit h)).trans (record_entry_made h).2.2.1
  refine ⟨entry_read_made h hq (record_entry_fit h), e, ?_, ?_⟩
  · show q.given.plan.rounds = _
    rw [e]
    exact recordPlan_record.2
  · show (q.given.plan.entries.find? fun e => e.name == Fmt.recordName) = _
    rw [e]
    decide +kernel

end

/-- The parameter bytes of an entry's chain at `recordLines` and any digest: spelled from the typed
plan, codes and shape. -/
theorem record_params (cfg : ByteArray) : entryParams recordLines cfg =
    .ok (Fmt.paramsBytes recordPlan cfg
      [("codes", spellCodes recordCodes), ("the link", spellLink recordLink)]) := by
  obtain ⟨P, hy, hp, _⟩ := record_sized
  unfold entryParams
  rw [hy]
  show (Except.ok (Fmt.paramsBytes P.plan cfg
    [("codes", spellCodes recordCodes), ("the link", spellLink recordLink)]) :
      Except String ByteArray) = _
  rw [hp]

end OnBytes.Params

#print axioms OnBytes.Params.record_entry_made
#print axioms OnBytes.Params.record_entryLink
#print axioms OnBytes.Params.record_entry_fit
#print axioms OnBytes.Params.record_entry_read
#print axioms OnBytes.Params.record_params
