-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/CatchesList.lean: the batching catches for a list of witnesses.

Where a prover is bound to a word only up to a radius, there is a list of witnesses near the word,
each with tables of its own. This file shows: if the witnesses near the word are at most lst, each
near witness's tables hold words on the blocks, and for each near witness one of the rows does not
hold of its words, then the elements of K as which x reads, for some x at which Bat.combine's row
holds of the tables of some near witness, are at most lst times one less than the number of rows.
The witnesses, their tables and words, and the rows come first, x after them.

Main theorem: catches_list.

What is not claimed. Nothing on how long a list is: lst is a condition here, and a bound on it is
the codes' matter. The witnesses are a finite type; the words themselves are not. Nothing on who
draws x, or on how the readings of the drawn elements are spread over K. Nothing on soundness.

-/
import Johnson.Desc.Means.CatchesMany

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K]

variable [IsDomain K] [Finite K] (ρ : Reading K)

/-- **The batching on a group catches, for a list of witnesses.** -/
theorem catches_list {W : Type} [Finite W] (near : W → Prop) (lst : ℕ)
    (hl : Nat.card {w : W // near w} ≤ lst) (tab : W → Tables K) (m : W → Words K)
    (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (rows : Array Row)
    (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : ∀ r ∈ rows.toList, RowIn S G r) (hT : ∀ w, near w → LaidOn S L (m w) (tab w))
    (hbad : ∀ w, near w → ¬ AllSay ρ S rows.toList (m w)) :
    Nat.card {y : K // ∃ (x : E) (out : GroupRow) (w : W), ρ.val x = y ∧
      Bat.combine S g ⟨L, rows⟩ x = some out ∧ near w ∧ GroupSays ρ S L out (tab w)} ≤
      lst * (rows.size - 1) := by
  classical
  haveI : Fintype {w : W // near w} := Fintype.ofFinite _
  have h1 := combine_catches_many ρ S g G L rows hG hL hOk hr
    (fun i : {w : W // near w} => m i.1) (fun i => hbad i.1 i.2)
  refine le_trans (Alg.count_mono fun y hy => ?_) (le_trans h1 ?_)
  · obtain ⟨x, out, w, e1, e2, e3, e4⟩ := hy
    exact ⟨⟨w, e3⟩, x, out, tab w, e1, e2, hT w e3, e4⟩
  · rw [← Nat.card_eq_fintype_card]
    exact Nat.mul_le_mul_right _ hl

end OnBytes.Means
