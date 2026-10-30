-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Ins.lean: WHAT A PLACE OF THE KIND K10 CLOSES OR READS, AT THE WRITTEN LISTS: ROWS
AND PINS OF ITS OWN LINK, AND "NO MARK": the premise hins of `k10_hQ_of_parts`
(Johnson/Desc/First/Close/Law/HQOfParts.lean). Statements and proofs; two evaluations by the kernel.

  `k10InsBy ok`: a test with code, general in what is allowed (ok): at every number below 358 whose
    place in `At.ps` is of the kind K10: every item of the table's row's ins and ctx meets ok at the
    place's link. `rowOrPin m`: the item is `row m c` or `pin m t`. `rowOnly m`: it is `row m c`.
  `k10_ins_full`: at `rowOrPin` the test says yes: by the kernel. `k10_ins_bent`: A NEGATIVE TEST:
    at `rowOnly` it says no: by the kernel.
  `k10_ins_at`: so at such a place: every item with `insQ fullLinks At.ps i` is a row of the place's
    own link, a pin of it, or "no mark": hins, at m := the place's link.
Limits. A fact on the table's written lists. Nothing on the laws. Nothing on soundness.

-/
import Johnson.P5J.K10Low
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace P5J

open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (Item rowOf)
open VerifiableInference.Desc.Sound (insQ rowQ)
open VerifiableInference.Desc.Kinds.Head.Law (ps_length)

/-- Is the item a row or a pin of link m? -/
def rowOrPin (m : ℕ) : Item → Bool
  | .row m' _ => m' == m
  | .pin m' _ => m' == m
  | _ => false

/-- Is it a row of link m? -/
def rowOnly (m : ℕ) : Item → Bool
  | .row m' _ => m' == m
  | _ => false

/-- The test, general in what is allowed. -/
def k10InsBy (ok : ℕ → Item → Bool) : Bool :=
  (List.range 358).all fun i => (At.ps[i]?).all fun a =>
    a.kind != KindName.K10 ||
      ((rowOf fullLinks a).ins ++ (rowOf fullLinks a).ctx).all (ok (a.link.getD 0))

theorem k10_ins_full : k10InsBy rowOrPin = true := by decide +kernel

/-- A negative test: rows alone do not suffice. -/
theorem k10_ins_bent : k10InsBy rowOnly = false := by decide +kernel

/-- **What a place of the kind K10 closes or reads.** -/
theorem k10_ins_at (i : ℕ) (a : Place) (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K10) :
    ∀ j, insQ fullLinks At.ps i j →
      (∃ c, j = Item.row (a.link.getD 0) c) ∨ (∃ t, j = Item.pin (a.link.getD 0) t) ∨
        j = Item.unmarked := by
  intro j hj
  have hi : i < 358 := ps_length ▸ (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k10_ins_full i (List.mem_range.2 hi)
  rw [ha] at h
  have h1 : (a.kind != KindName.K10 ||
      ((rowOf fullLinks a).ins ++ (rowOf fullLinks a).ctx).all (rowOrPin (a.link.getD 0))) =
      true := h
  rw [hk] at h1
  have h2 : ((rowOf fullLinks a).ins ++ (rowOf fullLinks a).ctx).all
      (rowOrPin (a.link.getD 0)) = true := h1
  have er : rowQ fullLinks At.ps i = rowOf fullLinks a := by
    unfold rowQ
    rw [ha]
    rfl
  have hj' : j ∈ (rowOf fullLinks a).ins ++ (rowOf fullLinks a).ctx ++ [Item.unmarked] := by
    have := hj
    unfold insQ at this
    rwa [er] at this
  rcases List.mem_append.1 hj' with hm | hm
  · have h3 := List.all_eq_true.1 h2 j hm
    cases j with
    | row m' c =>
      have : m' = a.link.getD 0 := by simpa [rowOrPin] using h3
      exact Or.inl ⟨c, by rw [this]⟩
    | pin m' t =>
      have : m' = a.link.getD 0 := by simpa [rowOrPin] using h3
      exact Or.inr (Or.inl ⟨t, by rw [this]⟩)
    | _ => simp [rowOrPin] at h3
  · exact Or.inr (Or.inr (by simpa using hm))

end P5J

#print axioms P5J.k10_ins_full
#print axioms P5J.k10_ins_bent
#print axioms P5J.k10_ins_at
