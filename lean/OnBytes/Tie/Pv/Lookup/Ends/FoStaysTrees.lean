-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysTrees.lean.
Routines of OnBytes/Model/Trees.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysLink
import OnBytes.Model.Trees

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model OnBytes.Model.LinkM

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible first
  | exact DryL.rootInH _ | exact DryL.t2Batch _)

theorem stays_Model_t2Lin (a : Aff) (runs : Array Run2)  :
    DryS (OnBytes.Model.t2Lin a runs) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_t2Lin)

theorem stays_Model_rowWeights (X : HTree) (r : HRow)  :
    DryS (OnBytes.Model.rowWeights X r) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_rowWeights)

theorem stays_Model_doorTerms (born : Nat) (array : String) (X : HTree)  :
    DryS (OnBytes.Model.doorTerms born array X) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_doorTerms)

theorem stays_Model_doorH (equationsLaid : Nat)  :
    DryL (OnBytes.Model.doorH equationsLaid) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_doorH)

end Fo
