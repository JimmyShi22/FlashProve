-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvAttentionSums.lean.
The routines of OnBytes/Model/AttentionSums.lean keep every property of the state that has `Prim`.

One statement a routine: `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a routine of a
link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvTail
import OnBytes.Model.AttentionSums

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Attention

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem inv_Attention_sc3Rounds  : ∀ (n : ℕ) (p : Model.Psc) (r : Array E),
    Inv I (OnBytes.Attention.sc3Rounds n p r)
  | 0, p, r => by
    rw [OnBytes.Attention.sc3Rounds]
    inv
  | n + 1, p, r => by
    rw [OnBytes.Attention.sc3Rounds]
    have ih := inv_Attention_sc3Rounds n
    inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_sc3Rounds)

theorem inv_Attention_sc3Shown (o : Sc3) (W : Array E) : ∀ (n b : ℕ) (s : E),
    Inv I (OnBytes.Attention.sc3Shown o W n b s)
  | 0, b, s => by
    rw [OnBytes.Attention.sc3Shown]
    inv
  | n + 1, b, s => by
    rw [OnBytes.Attention.sc3Shown]
    have ih := inv_Attention_sc3Shown o W n
    inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_sc3Shown)

theorem inv_Attention_scdRounds  : ∀ (ds : List ℕ) (p : Model.Psc) (r : Array E),
    Inv I (OnBytes.Attention.scdRounds ds p r)
  | [], p, r => by
    rw [OnBytes.Attention.scdRounds]
    inv
  | d :: ds, p, r => by
    rw [OnBytes.Attention.scdRounds]
    have ih := inv_Attention_scdRounds ds
    inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_scdRounds)

theorem inv_Attention_sc3In (nv nb : Nat) (start : Model.Aff)  :
    Inv I (OnBytes.Attention.sc3In nv nb start) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_sc3In)

theorem inv_Attention_sc3Row (o : Sc3) (W : Array E)  :
    Inv I (OnBytes.Attention.sc3Row o W) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_sc3Row)

theorem inv_Attention_scdIn (degrees : List Nat) (degreeInY n : Nat) (start : Model.Aff)  :
    Inv I (OnBytes.Attention.scdIn degrees degreeInY n start) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_scdIn)

theorem inv_Attention_scdRow (o : Scd) (s0 : E)  :
    Inv I (OnBytes.Attention.scdRow o s0) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_scdRow)

end Fo
