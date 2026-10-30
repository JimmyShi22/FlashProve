-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/ShapeRides.lean: THE BOOK-KEEPING CLAUSE OF THE PROMISE RIDES PAST A BLOCK THAT
LEAVES WHERE THE CHAIN STANDS. One test on the table, one theorem. Small; no Mathlib. A file BESIDE
the table of joints: it turns nothing of it.

Why. A block's second tie asks `shapeAt` (Johnson/Desc/First/Borders.lean) of the record behind, at
the next place. At most blocks inside a segment nothing that the clause reads turns: where the chain
stands, whether a count of rows waits, the open segment's number. That is no kind's fact: it is said
here once.

What is said. `sameStand`: A TEST ON THE TABLE, at two places: both lie in one segment, the table
says the same stand at both, and at the second a count may wait if it may at the first.
`shapeAt_rides`: under that test's yes, and three facts on the two records (the stand, "no count
waits" and the open segment's number are the same): `shapeAt` at the first place and record gives
`shapeAt` at the second.

Limits. (1) Where the stand turns (a segment is opened or left; the head's front; the finish) or a
count begins to wait, the test says no: there the clause is the block's own kind's files' to show.
(2) Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- A TEST ON THE TABLE: the two places lie in one segment (or both in none), the table says one
stand at both, and where a count may wait at the first it may at the second. -/
def sameStand (links : List ModelPart) (p p' : Place) : Bool :=
  p'.link == p.link && standAt links p' == standAt links p &&
    (!mayWait links p || mayWait links p')

/-- **The book-keeping rides.** -/
theorem shapeAt_rides (links : List ModelPart) (p p' : Place) (s s' : S)
    (ht : sameStand links p p' = true) (hst : standOf s' = standOf s)
    (hw : s'.noneWaits = s.noneWaits)
    (hl : s'.link?.map (·.link) = s.link?.map (·.link))
    (h : shapeAt links (some p) s = true) : shapeAt links (some p') s' = true := by
  unfold sameStand at ht
  unfold shapeAt at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at ht h ⊢
  obtain ⟨⟨e1, e2⟩, e3⟩ := ht
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨by rw [hst, e2]; exact h1, ?_⟩, ?_⟩
  · rcases h2 with h2 | h2
    · exact Or.inl (by rw [hw]; exact h2)
    · rcases e3 with e3 | e3
      · rw [e3] at h2
        exact absurd h2 (by simp)
      · exact Or.inr e3
  · cases hs' : s'.link? with
    | none => rfl
    | some L' =>
      cases hs : s.link? with
      | none => rw [hs', hs] at hl; simp at hl
      | some L =>
        rw [hs', hs] at hl
        rw [hs] at h3
        simp only [Option.map_some, Option.some.injEq] at hl
        simp only [Option.all_some, beq_iff_eq] at h3 ⊢
        rw [e1, h3, hl]

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.shapeAt_rides
