-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K09More.lean: MORE CLOSED FACTS ON THE WRITTEN LIST, which the hand-on
of the promise over a link's batching and over its shutting takes: the two places' pieces, the
places behind them, and that the shutting's row closes and reads nothing: AS A BOOL, WITH THE
KERNEL's YES AT THE LIST `P5J.fullLinks`. A definition, theorems, evaluations.

What is said.
  `moreFit links pl`: the Bool, at every link. `more_batch`: **under its yes: at the batching's
    number stands a place of link m with the piece «the link's hearings + 1», and a place stands
    behind it.** `more_shut`: **four numbers on stands a place of link m with the piece «the
    hearings + 5», a place stands behind it, and the row there closes nothing and reads nothing.**
    `moreFit_links`: the kernel's yes at `P5J.fullLinks` and its list of places. `moreFit_bent`: a
    negative test: with numbers 13 and 14 of the list changed over (the first link's shutting and
    the second link's first place): no.

Limits. Closed facts on the written list. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K09Cond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart flatPlacesOf)

/-- At every link: the batching's and the shutting's places, the places behind them, the
shutting's row. -/
def moreFit (links : List ModelPart) (pl : List Place) : Bool :=
  (List.range links.length).all fun m =>
    (match pl[batchAt links pl m]?, pl[batchAt links pl m + 1]? with
      | some p, some _ => decide (p.link = some m) && decide (p.piece = hearN links m + 1)
      | _, _ => false) &&
    (match pl[batchAt links pl m + 4]?, pl[batchAt links pl m + 4 + 1]? with
      | some p, some _ => decide (p.link = some m) && decide (p.piece = hearN links m + 5)
      | _, _ => false) &&
    decide ((rowQ links pl (batchAt links pl m + 4)).ins = []) &&
    decide ((rowQ links pl (batchAt links pl m + 4)).ctx = [])

/-- **THE BATCHING's PLACE AND THE ONE BEHIND IT.** -/
theorem more_batch (links : List ModelPart) (pl : List Place) (h : moreFit links pl = true) (m : ℕ)
    (hm : m < links.length) : ∃ p p', pl[batchAt links pl m]? = some p ∧
      pl[batchAt links pl m + 1]? = some p' ∧ p.link = some m ∧ p.piece = hearN links m + 1 := by
  have h1 := List.all_eq_true.1 h m (List.mem_range.2 hm)
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.1.1.1
  cases e : pl[batchAt links pl m]? with
  | none => rw [e] at h2; exact absurd h2 Bool.false_ne_true
  | some p =>
    cases e' : pl[batchAt links pl m + 1]? with
    | none => rw [e, e'] at h2; exact absurd h2 Bool.false_ne_true
    | some p' =>
      rw [e, e'] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact ⟨p, p', rfl, rfl, h2.1, h2.2⟩

/-- **THE SHUTTING's PLACE, THE ONE BEHIND IT, AND ITS ROW.** -/
theorem more_shut (links : List ModelPart) (pl : List Place) (h : moreFit links pl = true) (m : ℕ)
    (hm : m < links.length) : (∃ p p', pl[batchAt links pl m + 4]? = some p ∧
      pl[batchAt links pl m + 4 + 1]? = some p' ∧ p.link = some m ∧
      p.piece = hearN links m + 5) ∧ (rowQ links pl (batchAt links pl m + 4)).ins = [] ∧
      (rowQ links pl (batchAt links pl m + 4)).ctx = [] := by
  have h1 := List.all_eq_true.1 h m (List.mem_range.2 hm)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨?_, h1.1.2, h1.2⟩
  have h2 := h1.1.1.2
  cases e : pl[batchAt links pl m + 4]? with
  | none => rw [e] at h2; exact absurd h2 Bool.false_ne_true
  | some p =>
    cases e' : pl[batchAt links pl m + 4 + 1]? with
    | none => rw [e, e'] at h2; exact absurd h2 Bool.false_ne_true
    | some p' =>
      rw [e, e'] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact ⟨p, p', rfl, rfl, h2.1, h2.2⟩

set_option maxRecDepth 1000000 in
/-- **THE KERNEL's YES AT THE LIST `P5J.fullLinks`.** -/
theorem moreFit_links : moreFit P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: numbers 13 and 14 of the list changed over (the first link's shutting and
the second link's first place). -/
theorem moreFit_bent :
    moreFit P5J.fullLinks (swapAt (flatPlacesOf P5J.fullLinks true) 13) = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.more_batch
#print axioms VerifiableInference.Desc.LinkJoin.more_shut
#print axioms VerifiableInference.Desc.LinkJoin.moreFit_links
#print axioms VerifiableInference.Desc.LinkJoin.moreFit_bent
