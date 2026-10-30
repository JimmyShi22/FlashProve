-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Absent.lean: three small facts that other files take as conditions.

A row that has passed the tests of the adding has no coefficient on a table that is not there
(RowIn.absent): this is the condition of Johnson/Desc/Means/RowSumTie.lean, so for such a row what
it says of words can be written in the plain sum (says_plain_of_rowIn). Tables that hold the words
as the layout lays them hold them on the blocks (Laid.laidOn); so the tables as the words fill them
do (laidOn_tablesOf): the sets that the laws on batching count are taken over tables of which there
is at least this one.

Main theorems: RowIn.absent, says_plain_of_rowIn, Laid.laidOn, laidOn_tablesOf.

What is not claimed. Nothing on soundness.

-/
import Johnson.Desc.Means.RowSumTie
import Johnson.Desc.Means.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {S : Statement} {G : Group} {L : GroupLayout} {row : Row}

/-- A row that has passed the tests has the coefficient 0 on a table that is not there. -/
theorem RowIn.absent (hr : RowIn S G row) {o : Nat} {part : Part} (hh : S.has o part = false)
    (idx : Nat) : ρ.val (row.coefficient o part idx) = 0 := by
  rw [Row.coefficient_val]
  have add4 : ∀ a b c d : K, a = 0 → b = 0 → c = 0 → d = 0 → a + b + c + d = 0 := by
    intro a b c d ha hb hc hd
    rw [ha, hb, hc, hd]
    simp
  apply add4
  · apply sum_map_zero
    intro t ht
    rw [if_neg]
    rintro ⟨c1, c2⟩
    have h1 := ((placeOk_iff _ _ _ _ _ _).1 (hr.terms t ht)).2.1
    rw [c1, c2, hh] at h1
    cases h1
  · apply sum_map_zero
    intro u hu
    rw [if_neg]
    rintro ⟨c1, c2⟩
    have h1 := ((placeOk_iff _ _ _ _ _ _).1 (hr.units u hu)).2.1
    rw [c1, c2, hh] at h1
    cases h1
  · apply sum_map_zero
    intro w hw
    rw [if_neg]
    rintro ⟨c1, c2⟩
    have h1 := ((placeOk_iff _ _ _ _ _ _).1 (hr.runs w hw).2.2).2.1
    rw [c1, c2, hh] at h1
    cases h1
  · apply sum_map_zero
    intro f hf
    rw [if_neg]
    rintro ⟨c1, c2⟩
    have h1 := ((placeOk_iff _ _ _ _ _ _).1 (hr.forms f hf).1).2.1
    rw [c1, ← c2, hh] at h1
    cases h1

/-- What a row that has passed the tests says of words, in the plain sum. -/
theorem says_plain_of_rowIn (hr : RowIn S G row) (m : Words K) :
    Says ρ S row m ↔ (∑ o ∈ Finset.range S.oracles.size,
      ((∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
          ρ.val (row.coefficient o .main J) * m o .main J) +
        ∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
          ρ.val (row.coefficient o .mask j) * m o .mask j)) = ρ.val row.target :=
  says_plain ρ S row m fun _ _ hh J => hr.absent ρ hh J

/-- Tables that hold the words as the layout lays them hold them on the blocks. -/
theorem Laid.laidOn {m : Words K} {T : Tables K} (h : Laid S L m T) : LaidOn S L m T :=
  ⟨h.main_at, h.mask_at, h.kept_at⟩

/-- The tables as the words fill them hold the words on the blocks. -/
theorem laidOn_tablesOf (F : LayFacts S G L) (m : Words K) : LaidOn S L m (tablesOf S L m) :=
  (tablesOf_laid F m).laidOn

end OnBytes.Means
