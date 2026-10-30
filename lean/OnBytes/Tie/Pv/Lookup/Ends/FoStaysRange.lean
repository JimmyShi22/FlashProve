-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysRange.lean.
A loop over a range of numbers stays on the view, if each of its passes does.

Two rules, `DryS.rangeForIn` and `DryL.rangeForIn`, for `DryS` and `DryL`
(OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean: a run on a view that returns is still on the view). Each
turns the loop into one over a list and takes the rule for lists
(OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean). The tactic `stays` is taught both.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysTail

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model

theorem DryS.rangeForIn {σ : Type} {f : ℕ → σ → SubM (ForInStep σ)} (hf : ∀ a s, DryS (f a s))
    (r : Std.Legacy.Range) (s : σ) : DryS (ForIn.forIn r s f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact DryS.forIn hf _ s

theorem DryL.rangeForIn {σ : Type} {f : ℕ → σ → LinkM (ForInStep σ)}
    (hf : ∀ a s, DryL (f a s)) (r : Std.Legacy.Range) (s : σ) : DryL (ForIn.forIn r s f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact DryL.forIn hf _ s

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible first
  | apply DryS.rangeForIn | apply DryL.rangeForIn)

end Fo
