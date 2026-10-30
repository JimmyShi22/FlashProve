-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvMerge.lean.
The routines of OnBytes/Model/Merge.lean keep every property of the state that has `Prim`.

One statement a routine: `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a routine of a
link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvTsc
import OnBytes.Model.Merge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem inv_wsForkRounds : ∀ (a : ℕ) (r : Array E) (p : Psc),
    Inv I (OnBytes.Model.wsForkRounds a r p)
  | 0, r, p => by
    rw [OnBytes.Model.wsForkRounds]
    inv
  | n + 1, r, p => by
    rw [OnBytes.Model.wsForkRounds]
    have ih := inv_wsForkRounds n
    inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_wsForkRounds)

theorem inv_Model_wsForkMerge (lk : Nat) (sv : Array Nat)  :
    Inv I (OnBytes.Model.wsForkMerge lk sv) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_wsForkMerge)

theorem inv_Model_wsForkLin (o : WsMerged)  :
    Inv I (OnBytes.Model.wsForkLin o) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_wsForkLin)

theorem inv_Model_wsForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat)  :
    Inv I (OnBytes.Model.wsForkEnd lay cl sv) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_wsForkEnd)

end Fo
