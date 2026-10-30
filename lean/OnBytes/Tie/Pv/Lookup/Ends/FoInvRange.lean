-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvRange.lean.
A loop over a range of numbers keeps a property of the sub-proof's state, if its body does.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes OnBytes.Model

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem Inv.rangeForIn {σ : Type} {f : ℕ → σ → SubM (ForInStep σ)} (hf : ∀ a s, Inv I (f a s))
    (r : Std.Legacy.Range) (s : σ) : Inv I (ForIn.forIn r s f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact Inv.forIn hf _ s

theorem InvL.rangeForIn {σ : Type} {f : ℕ → σ → LinkM (ForInStep σ)}
    (hf : ∀ a s, InvL I (f a s)) (r : Std.Legacy.Range) (s : σ) : InvL I (ForIn.forIn r s f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact InvL.forIn hf _ s

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible first
  | apply Inv.rangeForIn | apply InvL.rangeForIn)

end Fo
