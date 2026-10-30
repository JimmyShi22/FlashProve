-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/Worth.lean: WHAT THE THREE SORTS OF COEFFICIENTS OF A CODE SWITCH's
ROWS ARE WORTH ON A TABLE OF WORDS: sums over a table's indices, turned into sums over the entries
that the coefficients were made of. Statements and proofs. The field, sums and lists; no coin, no
round, no frame, no statement of the protocol.

  `stretch_worth`   coefficients on a stretch of the rest (`stretchAt`,
                    OnBytes/Slice/BlkCsStretch.lean): entry i's coefficient times the word at the
                    place of entry i
  `lift_worth`      a form on the main row's message, carried to the new table (`switchLift`): entry
                    j's coefficient times the word at `cutIndex`'s index
  `kept_worth`      a form on a kept member's table, carried over: on the copy outside the pad's
                    places, and at the pad's places on what is laid elsewhere: together the form on
                    the member's own entries

By: `formAt_switchLift_cutIndex`, `formAt_switchLift_off` (Johnson/Top/H0/H2K/SwitchLiftAt.lean);
`cutIndex_inj` (OnBytes/Slice/SwitchPlacesLaws.lean).

Limits. Nothing on which words stand in a table. Nothing on any property.

-/
import Johnson.Top.H0.H2K.SwitchLiftAt
import OnBytes.Slice.BlkCsStretch
import OnBytes.Slice.SwitchPlacesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE formAt stretchAt)
open Finset (range)

/-- Coefficients on a stretch of the rest, on a table of N words. -/
theorem stretch_worth (places : SwitchPlaces) (a n : Nat) (c w : Nat → GE) (N : Nat)
    (hN : ∀ i, i < n → places.get (a + i) < N) :
    ∑ J ∈ range N, stretchAt places a n c J * w J =
      ∑ i ∈ range n, c i * w (places.get (a + i)) := by
  unfold stretchAt
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have h := hN i (Finset.mem_range.1 hi)
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [h]

/-- A form on the main row's message, carried to the new table. -/
theorem lift_worth (c : Form) (vars : Nat) (q : RowCut) (R tb : Nat)
    (hc : ∀ v ∈ c.tensors, v.vars = vars) (hb : q.bits ≤ vars) (hR : q.bits ≤ R)
    (hv : vars + (R - q.bits) ≤ tb) (hal : 2 ^ q.bits ∣ q.firstRow)
    (hf : q.firstRow / 2 ^ q.bits < 2 ^ (R - q.bits))
    (hlt : ∀ j, j < 2 ^ vars → cutIndex q R j < 2 ^ tb) (w : Nat → GE) :
    ∑ J ∈ range (2 ^ tb), formAt (switchLift c vars q R tb) J * w J =
      ∑ j ∈ range (2 ^ vars), formAt c j * w (cutIndex q R j) := by
  have hsub : (range (2 ^ vars)).image (cutIndex q R) ⊆ range (2 ^ tb) := by
    intro J hJ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hJ
    exact Finset.mem_range.2 (hlt j (Finset.mem_range.1 hj))
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [H2K.Lift.formAt_switchLift_cutIndex c vars q R tb hc hb hR hv hal hf j
      (Finset.mem_range.1 hj)]
  · intro j _ j' _ h
    exact cutIndex_inj (Nat.pow_le_pow_right (by omega) hR) h
  · intro J hJ hn
    rw [H2K.Lift.formAt_switchLift_off c vars q R tb hc hb hR hv hal hf J (Finset.mem_range.1 hJ),
      zero_mul]
    intro j hj e
    exact hn (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, e⟩)

/-- A form on a kept member's table, carried over. idx: the pad's indices. u: the copy's words. e:
the member's own entries. -/
theorem kept_worth (f : Nat → GE) (idx : List Nat) (hn : idx.Nodup) (N : Nat)
    (hN : ∀ J ∈ idx, J < N) (u e : Nat → GE) (hu : ∀ J, J < N → J ∉ idx → u J = e J) :
    ∑ J ∈ range N, (if J ∈ idx then 0 else f J) * u J + (idx.map fun J => f J * e J).sum =
      ∑ J ∈ range N, f J * e J := by
  have h1 : (idx.map fun J => f J * e J).sum = ∑ J ∈ range N, if J ∈ idx then f J * e J else 0 := by
    rw [← List.sum_toFinset _ hn, ← Finset.sum_filter]
    apply Finset.sum_congr _ fun _ _ => rfl
    ext J
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨hN J h, h⟩, fun h => h.2⟩
  rw [h1, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h : J ∈ idx
  · simp [h]
  · simp [h, hu J (Finset.mem_range.1 hJ) h]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.stretch_worth
#print axioms VerifiableInference.Desc.K2.Honest.lift_worth
#print axioms VerifiableInference.Desc.K2.Honest.kept_worth
