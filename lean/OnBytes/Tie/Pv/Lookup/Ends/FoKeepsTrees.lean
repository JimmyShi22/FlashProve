-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsTrees.lean.
Routines of OnBytes/Model/Trees.lean that keep what lies under the filled slots.

One statement for each routine but those that are left out (see below): `Keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean) or, for a routine of a link, `KeepsL`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine takes routines as arguments, the
statement has the premise that each of these has `Keeps`. Neither property says anything of a run in
which the routine refuses. Each statement is also given as a rule to the tactic `keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).
Also here: `Keeps.pushRuns`, on the step Fork.pushRuns.

Left out: LinkM.sub, LinkM.call, rootInH and t2Batch, whose statements are in
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean; LinkM.must, LinkM.mustAs, LinkM.testAs and LinkM.fork,
which have no statement of their own: the tactic opens them where a routine calls them.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsLink
import OnBytes.Model.Trees

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model OnBytes.Model.LinkM

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible first
  | exact KeepsL.rootInH _ | exact KeepsL.t2Batch _)

theorem pushRuns_slots5 {F G : Fork} {k : E} {runs : Array Run2} (h : F.pushRuns k runs = some G) :
    Slots5 F G := by
  unfold Fork.pushRuns at h
  obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.pushRuns (k : E) (runs : Array Run2) : Keeps (SubM.change (·.pushRuns k runs)) :=
  Keeps.change fun _ _ h hS => (pushRuns_slots5 h).later hS

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible exact Keeps.pushRuns _ _)

theorem keeps_Model_t2Lin (a : Aff) (runs : Array Run2)  :
    Keeps (OnBytes.Model.t2Lin a runs) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_t2Lin)

theorem keeps_Model_rowWeights (X : HTree) (r : HRow)  :
    Keeps (OnBytes.Model.rowWeights X r) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_rowWeights)

theorem keeps_Model_doorTerms (born : Nat) (array : String) (X : HTree)  :
    Keeps (OnBytes.Model.doorTerms born array X) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_doorTerms)

theorem keeps_Model_doorH (equationsLaid : Nat)  :
    KeepsL (OnBytes.Model.doorH equationsLaid) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_doorH)

end Fo
