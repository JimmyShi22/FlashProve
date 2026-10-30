-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K09Places.lean: CLOSED FACTS ON THE WRITTEN LIST's PLACES AT A LINK's
BATCHING AND AT ITS ONE EQUATION, which the facts along the fold take: the place is there, it bears
the link's number, and the batching's piece lies in the stretch in which the frame is full: AS A
BOOL, WITH THE KERNEL's YES AT THE LIST `P5J.fullLinks`. A definition, theorems, evaluations.

What is said.
  `placesFit links pl`: the Bool, at every link. `place_batch`: **under its yes: at the batching's
    number stands a place of link m whose piece lies between 7 + the link's shift and 11 + twice the
    shift.** `place_eq`: **two numbers on stands a place of link m.** `placesFit_links`: the
    kernel's yes at `P5J.fullLinks` and its list of places. `placesFit_bent`: a negative test: with
    the list's first eleven places dropped: no.

Limits. Closed facts on the written list. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K09Cond
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart flatPlacesOf shiftAt)

/-- At every link: the two places are there, with the link's number; the batching's piece lies in
the stretch. -/
def placesFit (links : List ModelPart) (pl : List Place) : Bool :=
  (List.range links.length).all fun m =>
    (match pl[batchAt links pl m]? with
      | some p => decide (p.link = some m) && decide (7 + shiftAt links m ≤ p.piece) &&
          decide (p.piece ≤ 11 + 2 * shiftAt links m)
      | none => false) &&
    (match pl[batchAt links pl m + 1 + 1]? with
      | some p => decide (p.link = some m)
      | none => false)

/-- **THE BATCHING's PLACE.** -/
theorem place_batch (links : List ModelPart) (pl : List Place) (h : placesFit links pl = true) (m : ℕ)
    (hm : m < links.length) : ∃ p, pl[batchAt links pl m]? = some p ∧ p.link = some m ∧
      7 + shiftAt links m ≤ p.piece ∧ p.piece ≤ 11 + 2 * shiftAt links m := by
  have h1 := List.all_eq_true.1 h m (List.mem_range.2 hm)
  rw [Bool.and_eq_true] at h1
  cases e : pl[batchAt links pl m]? with
  | none => rw [e] at h1; exact absurd h1.1 Bool.false_ne_true
  | some p =>
    rw [e] at h1
    have h2 := h1.1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact ⟨p, rfl, h2.1.1, h2.1.2, h2.2⟩

/-- **THE ONE EQUATION's PLACE.** -/
theorem place_eq (links : List ModelPart) (pl : List Place) (h : placesFit links pl = true) (m : ℕ)
    (hm : m < links.length) : ∃ p, pl[batchAt links pl m + 1 + 1]? = some p ∧ p.link = some m := by
  have h1 := List.all_eq_true.1 h m (List.mem_range.2 hm)
  rw [Bool.and_eq_true] at h1
  cases e : pl[batchAt links pl m + 1 + 1]? with
  | none => rw [e] at h1; exact absurd h1.2 Bool.false_ne_true
  | some p =>
    rw [e] at h1
    exact ⟨p, rfl, of_decide_eq_true h1.2⟩

set_option maxRecDepth 1000000 in
/-- **THE KERNEL's YES AT THE LIST `P5J.fullLinks`.** -/
theorem placesFit_links : placesFit P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the list's first eleven places dropped. -/
theorem placesFit_bent :
    placesFit P5J.fullLinks ((flatPlacesOf P5J.fullLinks true).drop 11) = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.place_batch
#print axioms VerifiableInference.Desc.LinkJoin.place_eq
#print axioms VerifiableInference.Desc.LinkJoin.placesFit_links
#print axioms VerifiableInference.Desc.LinkJoin.placesFit_bent
