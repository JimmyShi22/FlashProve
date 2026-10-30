-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K09Rows.lean: THE NINE CLOSED FACTS ON THE TABLE's ROWS THAT A LINK's
LIST OF DEBTS NAMES (`LinkDebts.rowInB` … `rowCtxE`, LinkDebts.lean): what the rows of the batching,
of the frame's sub-protocol behind it and of the one equation close, open and read: AS ONE BOOL ON
THE WRITTEN LIST, WITH THE KERNEL's YES AT THE LIST `P5J.fullLinks`. A definition, theorems,
evaluations.

What is said.
  `rows9At links pl m sub`: the Bool at link m of the sort sub. `rows9Fit links pl`: at every link
    of the list. `rows9_at`: **under its yes: the nine equations at link m.** `rows9Fit_links`: the
    kernel's yes at `P5J.fullLinks` and its list of places. `rows9Fit_bent`: a negative test: with
    the first link's one equation and the sub-protocol behind it changed over in the list of places:
    no.

Limits. Closed facts on the written list. THE BOOL DOES NOT TEST THE SORTS: the rows are computed
from the same list of sorts as the right sides: with the first two links' sorts changed over, and
with the last link's sort turned from «head» to «layers» (the places left), the kernel says yes all
the same [both tried]: it tests the list of PLACES against the list of sorts' own rows. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.K09Cond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item pinsOf formsOf flatPlacesOf)

/-- The nine facts at link m of the sort sub, as a Bool. -/
def rows9At (links : List ModelPart) (pl : List Place) (m : ℕ) (sub : ModelPart) : Bool :=
  decide ((rowQ links pl (batchAt links pl m)).ins = formsOf sub m) &&
  decide ((rowQ links pl (batchAt links pl m)).outs = [.totalB m]) &&
  decide ((rowQ links pl (batchAt links pl m)).ctx = pinsOf m) &&
  decide ((rowQ links pl (batchAt links pl m + 1)).ins = [.totalB m]) &&
  decide ((rowQ links pl (batchAt links pl m + 1)).outs = [.total m]) &&
  decide ((rowQ links pl (batchAt links pl m + 1)).ctx = pinsOf m) &&
  decide ((rowQ links pl (batchAt links pl m + 1 + 1)).ins = [.total m]) &&
  decide ((rowQ links pl (batchAt links pl m + 1 + 1)).outs = [.row m .equation]) &&
  decide ((rowQ links pl (batchAt links pl m + 1 + 1)).ctx = [])

/-- At every link of the list. -/
def rows9Fit (links : List ModelPart) (pl : List Place) : Bool :=
  (List.range links.length).all fun m =>
    match links[m]? with
    | some sub => rows9At links pl m sub
    | none => false

/-- **UNDER THE BOOL's YES: THE NINE EQUATIONS AT LINK m.** -/
theorem rows9_at (links : List ModelPart) (pl : List Place) (h : rows9Fit links pl = true) (m : ℕ)
    (sub : ModelPart) (hs : links[m]? = some sub) :
    ((rowQ links pl (batchAt links pl m)).ins = formsOf sub m ∧
      (rowQ links pl (batchAt links pl m)).outs = [.totalB m] ∧
      (rowQ links pl (batchAt links pl m)).ctx = pinsOf m) ∧
    ((rowQ links pl (batchAt links pl m + 1)).ins = [.totalB m] ∧
      (rowQ links pl (batchAt links pl m + 1)).outs = [.total m] ∧
      (rowQ links pl (batchAt links pl m + 1)).ctx = pinsOf m) ∧
    (rowQ links pl (batchAt links pl m + 1 + 1)).ins = [.total m] ∧
      (rowQ links pl (batchAt links pl m + 1 + 1)).outs = [.row m .equation] ∧
      (rowQ links pl (batchAt links pl m + 1 + 1)).ctx = [] := by
  have hm : m < links.length := (List.getElem?_eq_some_iff.1 hs).1
  have h1 := List.all_eq_true.1 h m (List.mem_range.2 hm)
  rw [hs] at h1
  simp only [rows9At, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := h1
  exact ⟨⟨a1, a2, a3⟩, ⟨a4, a5, a6⟩, a7, a8, a9⟩

set_option maxRecDepth 1000000 in
/-- **THE KERNEL's YES AT THE LIST `P5J.fullLinks`.** -/
theorem rows9Fit_links : rows9Fit P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the first link's one equation and the sub-protocol behind it changed over
(numbers 11 and 12 of the list). -/
theorem rows9Fit_bent : rows9Fit P5J.fullLinks (swapAt (flatPlacesOf P5J.fullLinks true) 11) =
    false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rows9_at
#print axioms VerifiableInference.Desc.LinkJoin.rows9Fit_links
#print axioms VerifiableInference.Desc.LinkJoin.rows9Fit_bent
