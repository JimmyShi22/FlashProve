-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsRange.lean.
A loop over a range of numbers keeps what lies under the filled slots, if its body does.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsTail

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model

theorem Keeps.rangeForIn {σ : Type} {f : ℕ → σ → SubM (ForInStep σ)} (hf : ∀ a s, Keeps (f a s))
    (r : Std.Legacy.Range) (s : σ) : Keeps (ForIn.forIn r s f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact Keeps.forIn hf _ s

theorem KeepsL.rangeForIn {σ : Type} {f : ℕ → σ → LinkM (ForInStep σ)}
    (hf : ∀ a s, KeepsL (f a s)) (r : Std.Legacy.Range) (s : σ) : KeepsL (ForIn.forIn r s f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact KeepsL.forIn hf _ s

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible first
  | apply Keeps.rangeForIn | apply KeepsL.rangeForIn)

end Fo
