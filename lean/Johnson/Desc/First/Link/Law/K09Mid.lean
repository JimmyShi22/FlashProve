-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K09Mid.lean: CLOSED FACTS ON THE WRITTEN LIST AT A LINK's TWO MIDDLE
PLACES (the frame's sub-protocol behind the batching; the one equation), which the hand-ons of the
promise over these two take: AS A BOOL, WITH THE KERNEL's YES AT THE LIST `P5J.fullLinks`; and two
elder Bools at these terms. A definition, theorems, evaluations.

What is said.
  `midFit links pl`: the Bool, at every link. `mid_behind`: **under its yes: one behind the
    batching's number stands a place of link m with the piece «the link's hearings + 2», and a place
    stands behind it.** `mid_eq`: **two behind: «the hearings + 3», and a place behind it.**
    `midFit_links`: the kernel's yes at `P5J.fullLinks` and its list of places. `midFit_bent`: a
    negative test: with numbers 10 and 11 of the list changed over (the first link's two middle
    places): no. `listFit_links`, `pubFitE_links`: two elder Bools (EqNumbersOf.lean, EqMg.lean) at
    the same terms, by the kernel.

Limits. Closed facts on the written list. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K09Cond
import Johnson.Desc.First.Link.Law.EqMg
import Johnson.Desc.First.Link.Law.EqNumbersOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart flatPlacesOf)

/-- At every link: the two middle places and the places behind them. -/
def midFit (links : List ModelPart) (pl : List Place) : Bool :=
  (List.range links.length).all fun m =>
    (match pl[batchAt links pl m + 1]?, pl[batchAt links pl m + 1 + 1]? with
      | some p, some _ => decide (p.link = some m) && decide (p.piece = hearN links m + 2)
      | _, _ => false) &&
    (match pl[batchAt links pl m + 1 + 1]?, pl[batchAt links pl m + 1 + 1 + 1]? with
      | some p, some _ => decide (p.link = some m) && decide (p.piece = hearN links m + 3)
      | _, _ => false)

/-- **THE PLACE OF THE FRAME's SUB-PROTOCOL BEHIND THE BATCHING, AND THE ONE BEHIND IT.** -/
theorem mid_behind (links : List ModelPart) (pl : List Place) (h : midFit links pl = true) (m : ℕ)
    (hm : m < links.length) : ∃ p p', pl[batchAt links pl m + 1]? = some p ∧
      pl[batchAt links pl m + 1 + 1]? = some p' ∧ p.link = some m ∧
      p.piece = hearN links m + 2 := by
  have h1 := List.all_eq_true.1 h m (List.mem_range.2 hm)
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.1
  cases e : pl[batchAt links pl m + 1]? with
  | none => rw [e] at h2; exact absurd h2 Bool.false_ne_true
  | some p =>
    cases e' : pl[batchAt links pl m + 1 + 1]? with
    | none => rw [e, e'] at h2; exact absurd h2 Bool.false_ne_true
    | some p' =>
      rw [e, e'] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact ⟨p, p', rfl, rfl, h2.1, h2.2⟩

/-- **THE ONE EQUATION's PLACE, AND THE ONE BEHIND IT.** -/
theorem mid_eq (links : List ModelPart) (pl : List Place) (h : midFit links pl = true) (m : ℕ)
    (hm : m < links.length) : ∃ p p', pl[batchAt links pl m + 1 + 1]? = some p ∧
      pl[batchAt links pl m + 1 + 1 + 1]? = some p' ∧ p.link = some m ∧
      p.piece = hearN links m + 3 := by
  have h1 := List.all_eq_true.1 h m (List.mem_range.2 hm)
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.2
  cases e : pl[batchAt links pl m + 1 + 1]? with
  | none => rw [e] at h2; exact absurd h2 Bool.false_ne_true
  | some p =>
    cases e' : pl[batchAt links pl m + 1 + 1 + 1]? with
    | none => rw [e, e'] at h2; exact absurd h2 Bool.false_ne_true
    | some p' =>
      rw [e, e'] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact ⟨p, p', rfl, rfl, h2.1, h2.2⟩

set_option maxRecDepth 1000000

/-- **THE KERNEL's YES AT THE LIST `P5J.fullLinks`.** -/
theorem midFit_links : midFit P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

/-- A negative test: numbers 10 and 11 of the list changed over. -/
theorem midFit_bent :
    midFit P5J.fullLinks (swapAt (flatPlacesOf P5J.fullLinks true) 10) = false := by
  decide +kernel

theorem listFit_links : listFit P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

theorem pubFitE_links :
    pubFitE moreAll P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mid_behind
#print axioms VerifiableInference.Desc.LinkJoin.mid_eq
#print axioms VerifiableInference.Desc.LinkJoin.midFit_links
#print axioms VerifiableInference.Desc.LinkJoin.midFit_bent
#print axioms VerifiableInference.Desc.LinkJoin.listFit_links
#print axioms VerifiableInference.Desc.LinkJoin.pubFitE_links
