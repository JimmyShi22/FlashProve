-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Lays.lean: AT A PLACE OF THE KIND K10 A SEAT OF THE LINK's GROUP IS LAID BY THE
EXTRACTOR OR KEPT: the premise hGrp of `k10_hQ_at_fa` (Johnson/Desc/First/Close/Law/HQAtFa.lean),
down to "the seat lies in the group". Statements and proofs; two evaluations by the kernel.

  `laid_or_kept` (general in the numbers, the links and the place): the place is of the kind K10;
    its row lays; t lies in the group of the place's link: THEN t is among `laysSeats Nu links p` or
    among `Nu.keptOf` of that link. By `laysSeats`' own text (Johnson/Desc/First/Borders.lean): the
    group's seats but the kept ones.
  `k10_lays_full`: at every place of the kind K10 of `At.ps` the table's row lays: by the kernel.
    `k10_lays_bent`: A NEGATIVE TEST: not every place of `At.ps` has a row that lays: by the kernel.
    `k10_lays_at`: the first, at one place.
  `k10_grp_at`: so at such a place, at any numbers Nu: t ∈ Nu.group (the place's link) → t ∈
    `laysSeats Nu fullLinks a` ∨ t ∈ Nu.keptOf (the place's link).
Limits. THAT THE SEAT OF A MEMBER WITH A MAIN ROW OF THE GROUP's LIST LIES IN THE GROUP is a fact on
the plan: not here. Nothing on the laws. Nothing on soundness.

-/
import Johnson.P5J.K10Open

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace P5J

open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (Numbers ModelPart rowOf laysSeats)

/-- **A seat of the group is laid or kept.** -/
theorem laid_or_kept (Nu : Numbers) (links : List ModelPart) (p : Place) (hK : p.kind = KindName.K10)
    (hl : (rowOf links p).lays = true) (t : ℕ × ℕ) (ht : t ∈ Nu.group (p.link.getD 0)) :
    t ∈ laysSeats Nu links p ∨ t ∈ Nu.keptOf (p.link.getD 0) := by
  by_cases hk : t ∈ Nu.keptOf (p.link.getD 0)
  · exact Or.inr hk
  · refine Or.inl ?_
    unfold laysSeats
    rw [hl, hK]
    refine List.mem_filter.2 ⟨ht, ?_⟩
    have h2 : (Nu.keptOf (p.link.getD 0)).contains t = false :=
      Bool.eq_false_iff.2 fun h => hk (List.contains_iff_mem.1 h)
    rw [h2]
    rfl

/-- The rows at the places that meet sel lay. -/
def laysBy (sel : Place → Bool) : Bool :=
  At.ps.all fun a => !sel a || (rowOf fullLinks a).lays

theorem k10_lays_full : laysBy (fun a => a.kind == KindName.K10) = true := by decide +kernel

/-- A negative test: not every place's row lays. -/
theorem k10_lays_bent : laysBy (fun _ => true) = false := by decide +kernel

theorem k10_lays_at (i : ℕ) (a : Place) (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K10) :
    (rowOf fullLinks a).lays = true := by
  have h := List.all_eq_true.1 k10_lays_full a (List.mem_of_getElem? ha)
  have h1 : (!(a.kind == KindName.K10) || (rowOf fullLinks a).lays) = true := h
  rw [hk] at h1
  exact h1

/-- **hGrp, down to "the seat lies in the group".** -/
theorem k10_grp_at (Nu : Numbers) (i : ℕ) (a : Place) (ha : At.ps[i]? = some a)
    (hk : a.kind = KindName.K10) (t : ℕ × ℕ) (ht : t ∈ Nu.group (a.link.getD 0)) :
    t ∈ laysSeats Nu fullLinks a ∨ t ∈ Nu.keptOf (a.link.getD 0) :=
  laid_or_kept Nu fullLinks a hk (k10_lays_at i a ha hk) t ht

end P5J

#print axioms P5J.laid_or_kept
#print axioms P5J.k10_lays_full
#print axioms P5J.k10_lays_bent
#print axioms P5J.k10_lays_at
#print axioms P5J.k10_grp_at
