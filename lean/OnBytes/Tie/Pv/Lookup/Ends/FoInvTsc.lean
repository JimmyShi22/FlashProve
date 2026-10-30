-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvTsc.lean.
The routines of OnBytes/Model/Tsc.lean keep every property of the state that has `Prim`.

One statement a routine: `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a routine of a
link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvTrees
import OnBytes.Model.Tsc

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem inv_tscLoop : ∀ (a : List E) (r : Array E) (p : Psc), Inv I (OnBytes.Model.tscLoop a r p)
  | [], r, p => by
    rw [OnBytes.Model.tscLoop]
    inv
  | z :: zs, r, p => by
    rw [OnBytes.Model.tscLoop]
    have ih := inv_tscLoop zs
    inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_tscLoop)

theorem inv_Model_tscRounds (P : Array E) (lt : Nat)  :
    Inv I (OnBytes.Model.tscRounds P lt) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_tscRounds)

theorem inv_Model_tscIn (P : Array E) (lt shown degreeInY : Nat)  :
    Inv I (OnBytes.Model.tscIn P lt shown degreeInY) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_tscIn)

end Fo
