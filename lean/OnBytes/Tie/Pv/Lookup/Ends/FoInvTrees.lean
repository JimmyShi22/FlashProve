-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvTrees.lean.
The routines of OnBytes/Model/Trees.lean keep every property of the state that has `Prim`.

One statement a routine, but for those named under "Left out": `Inv I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a
routine of a link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Left out: LinkM.must, LinkM.mustAs, LinkM.testAs, LinkM.fork (no statement of their own: the tactic
opens them); LinkM.sub (OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean), LinkM.call
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean), rootInH (OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean),
t2Batch (OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvLink
import OnBytes.Model.Trees

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model OnBytes.Model.LinkM

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible first
  | exact InvL.rootInH _ | exact InvL.t2Batch _)

theorem inv_Model_t2Lin (a : Aff) (runs : Array Run2)  :
    Inv I (OnBytes.Model.t2Lin a runs) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_t2Lin)

theorem inv_Model_rowWeights (X : HTree) (r : HRow)  :
    Inv I (OnBytes.Model.rowWeights X r) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_rowWeights)

theorem inv_Model_doorTerms (born : Nat) (array : String) (X : HTree)  :
    Inv I (OnBytes.Model.doorTerms born array X) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_doorTerms)

theorem inv_Model_doorH (equationsLaid : Nat)  :
    InvL I (OnBytes.Model.doorH equationsLaid) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_doorH)

end Fo
