-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Rom/DeferPublic.lean: one lemma on mode I of deferred programming (Rom/Defer.lean): if no result
  of a step's run in mode I has a violation, the state from which it runs has none
  (`noviol_of_safe`).

  Limits: this file does not prove that mode I is a public process, followed by independent uniform
  values for all tokens that are not shown.
-/
import Rom.DeferProof_tail

open scoped ENNReal
open Prob
namespace Rom
namespace DeferTail

variable {S : OSpec} {sp : Split S}





theorem noviol_of_safe {α : Type} (c : Step S sp α) (d : DSt S)
    (hs : ∀ y ∈ (c.run true d).support, y.2.viol = false) : d.viol = false := by
  obtain ⟨y, hy⟩ := (c.run true d).support_nonempty
  by_contra hc
  have := (run_ext c d y hy).viol (by simpa using hc)
  rw [hs y hy] at this
  simp at this




end DeferTail
end Rom
