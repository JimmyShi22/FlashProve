-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/CatchesMany.lean: the batching catches for a finite family of words at once.

Where a prover is bound to a list of words and not to one, the batched row must fail for each word
of the list. Johnson/Desc/Means/Catches.lean bounds the multipliers for one choice of words. This
file adds the bounds up over a finite family, by the library's union bound (Alg/Count.lean:
count_exists_le).

Main theorem: combine_catches_many.

What is not claimed. Nothing on how long a list is, on who draws x, or on how the readings of the
drawn elements are spread over K. Nothing on soundness.

-/
import Johnson.Desc.Means.Catches

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] [IsDomain K] [Finite K] (ρ : Reading K)
variable {ι : Type} [Fintype ι]

/-- **The batching on a group catches, for a family of words.** If for each word of the family one
of the rows does not hold, the elements of K as which x reads, for some x at which Bat.combine's row
holds of tables that hold SOME word of the family on the blocks, are at most the size of the family
times one less than the number of rows. -/
theorem combine_catches_many (S : Statement) (g : Nat) (G : Group) (L : GroupLayout)
    (rows : Array Row) (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : ∀ r ∈ rows.toList, RowIn S G r) (m : ι → Words K)
    (hbad : ∀ i, ¬ AllSay ρ S rows.toList (m i)) :
    Nat.card {y : K // ∃ (i : ι) (x : E) (out : GroupRow) (T : Tables K), ρ.val x = y ∧
      Bat.combine S g ⟨L, rows⟩ x = some out ∧ LaidOn S L (m i) T ∧ GroupSays ρ S L out T} ≤
      Fintype.card ι * (rows.size - 1) := by
  refine le_trans (Alg.count_exists_le _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ (rows.size - 1) fun i _ =>
    combine_catches ρ S g G L rows hG hL hOk hr (m i) (hbad i)) ?_
  simp

end OnBytes.Means
