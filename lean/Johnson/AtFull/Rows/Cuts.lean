-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Cuts.lean: Slice.lean's WALK IN SLICES, FOR SLICES OF UNEQUAL WIDTH: a
table of cuts in the list of a routine's noted calls. (Every slice's closed fact runs the routine
once for its calls: so few and even slices are cheaper for the kernel than many of one width.)
Theorems. A law file; no running text imports it.
  `walk_from_cuts`, `good_of_cuts` as walk_from_slices | good_of_slices, with «cut i» for «i * w»
                  and «cut (i + 1) - cut i» for «w»; the cuts begin at 0, do not fall, and reach the
                  calls' end.
  `all27`         a sentence on each of 0 … 26 is a sentence on all i < 27.
Limits. No closed fact is here. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.Slice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem walk_from_cuts {s : Setting} {truth : List PlanRound} (L : List Call) (cut : Nat → Nat)
    (m : Nat)
    (tab : Nat → SmallSt × Nat) (hc : ∀ i, i < m → cut i ≤ cut (i + 1)) (hl : L.length ≤ cut m)
    (h : ∀ i, i < m →
      walkCalls s truth (tab i) ((L.drop (cut i)).take (cut (i + 1) - cut i)) =
        some (tab (i + 1))) :
    ∀ k j, j + k = m → walkCalls s truth (tab j) (L.drop (cut j)) = some (tab m)
  | 0, j, e => by
    have ej : j = m := by omega
    subst ej
    rw [List.drop_of_length_le hl]
    unfold walkCalls
    rfl
  | k + 1, j, e => by
    have hj : j < m := by omega
    have ih := walk_from_cuts L cut m tab hc hl h k (j + 1) (by omega)
    have e1 : L.drop (cut j) =
        (L.drop (cut j)).take (cut (j + 1) - cut j) ++ L.drop (cut (j + 1)) := by
      have e2 : cut (j + 1) = cut j + (cut (j + 1) - cut j) := by
        have := hc j hj
        omega
      conv => rhs; rhs; rw [e2]
      rw [← List.drop_drop, List.take_append_drop]
    rw [e1]
    exact walk_append _ _ _ _ _ (h j hj) ih

/-- **A table over slices of unequal width of a faithful routine's noted calls gives the walk.** -/
theorem good_of_cuts {s : Setting} {truth : List PlanRound} {x : N Unit} {σ₀ : SmallSt}
    {sc' : Scope}
    (hx : Faith x) (cut : Nat → Nat) (m : Nat) (tab : Nat → SmallSt × Nat)
    (h0 : tab 0 = (σ₀, 0)) (c0 : cut 0 = 0) (hc : ∀ i, i < m → cut i ≤ cut (i + 1))
    (hl : (callsAt s σ₀ x).size ≤ cut m)
    (h : ∀ i, i < m →
      sliceD s truth (tab i) x σ₀ (cut i) (cut (i + 1) - cut i) = some (tab (i + 1)))
    (hm : 0 < m) (he : tab m = (⟨sc', 0, 0, 0⟩, truth.length)) : Good s truth (σ₀, 0) x := by
  cases e : (x.run #[]).run (σ₀.plan s) with
  | error msg =>
    have h' := h 0 hm
    unfold sliceD at h'
    rw [e] at h'
    cases h'
  | ok r =>
    obtain ⟨⟨u, cs⟩, q⟩ := r
    have hcs : callsAt s σ₀ x = cs := by
      unfold callsAt outAt
      rw [e]
      rfl
    rw [hcs] at hl
    have hs : ∀ i, i < m →
        walkCalls s truth (tab i) ((cs.toList.drop (cut i)).take (cut (i + 1) - cut i)) =
          some (tab (i + 1)) := by
      intro i hi
      have h' := h i hi
      unfold sliceD at h'
      rw [e] at h'
      dsimp only at h'
      rw [walkR_eq] at h'
      exact h'
    have hw := walk_from_cuts cs.toList cut m tab hc (by simpa using hl) hs m 0 (by omega)
    rw [c0, List.drop_zero, h0, he] at hw
    refine good_oneC (sc' := sc') hx ?_
    unfold pieceC
    dsimp only
    rw [e]
    exact hw

theorem all27 {P : Nat → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P
    8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) (h14 : P 14) (h15 : P 15) (h16
    : P 16) (h17 : P 17) (h18 : P 18) (h19 : P 19) (h20 : P 20) (h21 : P 21) (h22 : P 22) (h23 : P
    23) (h24 : P 24) (h25 : P 25) (h26 : P 26) :
    ∀ i, i < 27 → P i := by
  intro i hi
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | 8, _ => exact h8
  | 9, _ => exact h9
  | 10, _ => exact h10
  | 11, _ => exact h11
  | 12, _ => exact h12
  | 13, _ => exact h13
  | 14, _ => exact h14
  | 15, _ => exact h15
  | 16, _ => exact h16
  | 17, _ => exact h17
  | 18, _ => exact h18
  | 19, _ => exact h19
  | 20, _ => exact h20
  | 21, _ => exact h21
  | 22, _ => exact h22
  | 23, _ => exact h23
  | 24, _ => exact h24
  | 25, _ => exact h25
  | 26, _ => exact h26
  | n + 27, h => exact absurd h (by omega)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.walk_from_cuts
#print axioms VerifiableInference.Desc.LinkJoin.good_of_cuts
#print axioms VerifiableInference.Desc.LinkJoin.all27
