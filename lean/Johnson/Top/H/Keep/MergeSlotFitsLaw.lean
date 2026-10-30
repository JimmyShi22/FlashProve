-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/MergeSlotFitsLaw.lean: The kind "lookup" (K3): THE TEST sFvFitsB
(Johnson/Desc/First/Look/MergeSlotFits.lean) IN FRONT OF A LOOKUP's
SUB-PROTOCOL GIVES, BEHIND IT, THE PREMISE hmerge OF objects_formsIn AND objects_formsInT
(Johnson/Top/H/Keep/FormsInObjects.lean, FormsInTObjects.lean): no kept row names the slot of the
merge's end value: IF THE KEPT ROWS NAME NO SLOT BELOW THE LEDGER's NEXT SLOT IN FRONT. And the
test itself passes a K3Pass. Statements and proofs.

OBJECT: K3.sFvFitsB; K9.mergeOf; K3Pass (Johnson/Top/H/Keep/FormsPassK3.lean).
Used by Johnson/Top/H/Keep/MergeApart.lean.
LETTERS: s, s', F, G, rows free.
Compiled with the whole library.

Main names:
  hmerge_of_fits: THE TIE.
  sFvFits_pass: true in front, true behind.

Limits. hfresh (EVERY SLOT THAT A KEPT ROW NAMES LIES AT OR ABOVE F.next) IS A PREMISE: OURS TO PAY
AT AN ACCEPT; NOT PAID. (Where this and
lean/THEOREM.md differ, the page holds.) It takes the place of merge_of_free
(Johnson/Top/H/Keep/LateLow.lean),
whose premise "the merge's slot is free in the ledger" cannot be met where the merge has a slot:
that slot is filled.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsPassK3
import Johnson.Desc.First.Look.MergeSlotFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (sFvFitsB)
open VerifiableInference.Desc.K9 (mergeOf)

/-- What the test says, where the merge has a slot and a ledger is open. -/
theorem sFvFits_lt {s : S} {F : Fork} {j : ℕ} (h : sFvFitsB s = true) (hm : mergeOf s = some j)
    (hF : s.fork? = some F) : j < F.next := by
  unfold sFvFitsB at h
  rw [hm, hF] at h
  simp only [Option.any_some] at h
  exact of_decide_eq_true h

/-- **THE TIE: the test in front gives hmerge behind.** -/
theorem hmerge_of_fits {s s' : S} {F G : Fork} (P : K3Pass s s' F G) (h : sFvFitsB s = true)
    {rows : Array Aff}
    (hfresh : ∀ f ∈ rows.toList, ∀ x ∈ f.slots.toList, F.next ≤ x.1) :
    ∀ f ∈ rows.toList, ∀ x ∈ f.slots.toList, mergeOf s' ≠ some x.1 := by
  intro f hf x hx e
  rw [P.merge] at e
  exact absurd (hfresh f hf x hx) (Nat.not_le.2 (sFvFits_lt h e P.front))

/-- **The test passes.** -/
theorem sFvFits_pass {s s' : S} {F G : Fork} (P : K3Pass s s' F G) (h : sFvFitsB s = true) :
    sFvFitsB s' = true := by
  unfold sFvFitsB
  rw [P.merge, P.behind]
  cases hm : mergeOf s with
  | none => rfl
  | some j =>
    simp only [Option.any_some]
    exact decide_eq_true (Nat.lt_of_lt_of_le (sFvFits_lt h hm P.front) P.later.next)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.sFvFits_lt
#print axioms VerifiableInference.OnPublicFiles.hmerge_of_fits
#print axioms VerifiableInference.OnPublicFiles.sFvFits_pass
