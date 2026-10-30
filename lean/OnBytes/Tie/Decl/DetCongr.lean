-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Decl/DetCongr.lean: an algorithm over one oracle has one value under two families of
oracle functions that agree at every string that it asks. Generic: no hash, no file, no format.
Statement and proof.

Main name:
  `det_congr_asks`: see above; "every string that it asks" is said by a property P that all its
    queries have (`OComp.AsksIn`).
Limits: values under a family (`OComp.det`) alone; no probability.

-/
import Rom.AsksIn
import Rom.Cache

set_option autoImplicit false

namespace OnBytes.Tie

open Rom

/-- One value under two families that agree at every string that is asked. -/
theorem det_congr_asks {lam : ℕ} {α : Type} (P : List Bool → Prop) (g g' : Fam (rom lam))
    (hg : ∀ s, P s → g () s = g' () s) (c : OComp (rom lam) α)
    (h : c.AsksIn fun _ (s : List Bool) => P s) : c.det g = c.det g' := by
  induction c with
  | pure a => rfl
  | query o s k ih =>
    cases o
    simp only [OComp.det]
    rw [hg s h.1]
    exact ih _ (h.2 _)
  | sample n k ih =>
    simp only [OComp.det]
    exact ih _ (h _)

end OnBytes.Tie

#print axioms OnBytes.Tie.det_congr_asks
