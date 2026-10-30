-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/LevelPoint.lean: the point that the flat function of a product layer leaves (the
challenges laid at their variables' places, levelR) reads, coordinate by coordinate, as the point
that the library's records of the layers' own rounds read off the typed output: the output's point
in the order heard, carried through the inverse of the layer's permutation.

A product layer's round j runs in variable order[j]; its challenge is stored at place
mu - 1 - order[j] (OnBytes/Model/Psc.lean: levelRounds; OnBytes/Desc/First/P1/FlSpec.lean: levelR).
The typed layer takes a permutation e: round j binds coordinate e j;
OnBytes/Tie/Pv/Lay/OrderE.lean has e := ordE mu order h with (e j).val = mu - 1 - order[j]. The
library's records read "fun i => outPt (e.symm i)" (Cb/Pv/Lay/End/NormsBill.lean: normsEAt.r1).

Main names:
  `levelR_keep`: a place that is no later variable's keeps its entry.
  `levelR_size`: the array keeps its size.
  `levelR_get`: the challenge of round j lies at place mu - 1 - order[j].
  `level_point`: the tie, for any function outPt on the rounds that reads the challenges in the
    order heard.
  `heard_point`, `turned_point`: the like for a point that holds the challenges in the order heard
    (a token sumcheck's) and turned round (the batched sumcheck's).
Limits. That outPt reads the challenges in the order heard (OutIs.pt says it of a typed
output) and that the typed permutation is ordE mu order h are premises. Identities on public
numbers: nothing on a world, on a draw, on soundness or on hiding.


-/
import OnBytes.Desc.First.P1.FlSpec
import OnBytes.Tie.Pv.Lay.OrderE
import Johnson.Road.FormsKeysEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes.Model (Reading)
open OnBytes.Desc.First.P1 (levelR)
open OnBytes.Tie.Pv.Lay (ordE ordE_val)

/-- The array keeps its size. -/
theorem levelR_size (mu : ℕ) : ∀ (order : List ℕ) (xs : List E) (r : Array E),
    (levelR mu order xs r).size = r.size
  | [], _, _ => by simp [levelR]
  | _ :: _, [], _ => by simp [levelR]
  | v :: order, x :: xs, r => by
    rw [levelR, levelR_size mu order xs]
    simp

/-- A place that is no later variable's keeps its entry. -/
theorem levelR_keep (mu p : ℕ) : ∀ (order : List ℕ) (xs : List E) (r : Array E),
    (∀ v ∈ order, mu - 1 - v ≠ p) → (levelR mu order xs r).getD p zeroE = r.getD p zeroE
  | [], _, _, _ => by simp [levelR]
  | _ :: _, [], _, _ => by simp [levelR]
  | v :: order, x :: xs, r, h => by
    rw [levelR, levelR_keep mu p order xs _ fun w hw => h w (List.mem_cons_of_mem _ hw)]
    have hv : mu - 1 - v ≠ p := h v List.mem_cons_self
    by_cases hp : p < r.size
    · simp [Array.getD, Array.set!, hp, hv]
    · simp [Array.getD, Array.set!, hp]

/-- The challenge of round j lies at place mu - 1 - order[j]. -/
theorem levelR_get (mu : ℕ) : ∀ (order : List ℕ) (xs : List E) (r : Array E),
    order.length = xs.length → order.Nodup → (∀ v ∈ order, v < mu) → mu ≤ r.size →
    ∀ j (hj : j < order.length),
      (levelR mu order xs r).getD (mu - 1 - order[j]) zeroE = xs.getD j zeroE
  | [], _, _, _, _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | v :: order, [], _, hl, _, _, _, _, _ => by simp at hl
  | v :: order, x :: xs, r, hl, hn, hv, hr, j, hj => by
    have hn' := List.nodup_cons.mp hn
    have hv0 : v < mu := hv v List.mem_cons_self
    rw [levelR]
    cases j with
    | zero =>
      rw [List.getElem_cons_zero, levelR_keep mu (mu - 1 - v) order xs _ fun w hw e => by
        have hw' : w < mu := hv w (List.mem_cons_of_mem _ hw)
        have : w = v := by omega
        exact hn'.1 (this ▸ hw)]
      have hp : mu - 1 - v < r.size := by omega
      simp [Array.getD, Array.set!, hp]
    | succ j =>
      rw [List.getElem_cons_succ, List.getD_cons_succ]
      exact levelR_get mu order xs _ (by simpa using hl) hn'.2
        (fun w hw => hv w (List.mem_cons_of_mem _ hw)) (by simpa using hr) j (by simpa using hj)

variable {K : Type} [Field K] {ρ : Reading K}

/-- **A product layer's point, read, is the typed output's point carried through the inverse of the
layer's permutation.** xs: the challenges in the order heard. -/
theorem level_point {mu : ℕ} {order : List ℕ} (h : order.Perm (List.range mu)) {xs : List E}
    (hx : xs.length = mu) {r : Array E} (hr : mu ≤ r.size) {outPt : Fin mu → K}
    (hpt : ∀ i : Fin mu, outPt i = ρ.val (xs.getD i.val zeroE)) {j : ℕ} (hj : j < mu) :
    pt ρ (levelR mu order xs r) j =
      Blocks.nat (fun i => outPt ((ordE mu order h).symm i)) j := by
  have hl : order.length = mu := by rw [h.length_eq, List.length_range]
  have hq := ordE_val mu order h ((ordE mu order h).symm ⟨j, hj⟩)
  rw [Equiv.apply_symm_apply] at hq
  have hq' : j = mu - 1 - order[((ordE mu order h).symm ⟨j, hj⟩).val]'(by
      rw [hl]; exact ((ordE mu order h).symm ⟨j, hj⟩).2) := hq
  unfold Blocks.nat pt
  rw [dif_pos hj]
  show ρ.val _ = outPt ((ordE mu order h).symm ⟨j, hj⟩)
  rw [hpt]
  congr 1
  conv_lhs => rw [hq']
  exact levelR_get mu order xs r (by rw [hl, hx]) (h.nodup_iff.mpr List.nodup_range)
    (fun v hv => List.mem_range.mp (h.subset hv)) hr _ _

omit [Field K] in
/-- An entry of an array, off its list. -/
theorem getD_toList (r : Array E) (i : ℕ) : r.getD i zeroE = r.toList.getD i zeroE := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  by_cases h : i < r.size
  · rw [Array.getD, dif_pos h, getElem?_pos r i h]
    rfl
  · rw [Array.getD, dif_neg h, getElem?_neg r i h]
    rfl

/-- A point that holds the challenges in the order heard. -/
theorem heard_point {k : ℕ} {r : Array E} {xs : List E} (hr : r.toList = xs) {outPt : Fin k → K}
    (hpt : ∀ i : Fin k, outPt i = ρ.val (xs.getD i.val zeroE)) {j : ℕ} (hj : j < k) :
    pt ρ r j = Blocks.nat outPt j := by
  unfold Blocks.nat pt
  rw [dif_pos hj, hpt ⟨j, hj⟩, ← hr, getD_toList]

/-- A point that holds the challenges turned round. -/
theorem turned_point {k : ℕ} {r : Array E} {xs : List E} (hr : r.toList = xs.reverse)
    (hx : xs.length = k) {outPt : Fin k → K}
    (hpt : ∀ i : Fin k, outPt i = ρ.val (xs.getD i.val zeroE)) {j : ℕ} (hj : j < k) :
    Blocks.nat outPt j = ρ.val (r.getD (k - 1 - j) zeroE) := by
  unfold Blocks.nat
  rw [dif_pos hj, hpt ⟨j, hj⟩]
  congr 1
  have hj' : j < xs.length := by rw [hx]; exact hj
  have hk : k - 1 - j < xs.reverse.length := by
    rw [List.length_reverse]
    omega
  have a1 : xs.getD j zeroE = xs[j]'hj' := List.getD_eq_getElem _ _ hj'
  have a2 : xs.reverse.getD (k - 1 - j) zeroE = xs.reverse[k - 1 - j]'hk :=
    List.getD_eq_getElem _ _ hk
  show xs.getD j zeroE = r.getD (k - 1 - j) zeroE
  rw [getD_toList, hr, a1, a2, List.getElem_reverse]
  congr 1
  omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.heard_point
#print axioms OnBytes.Road.K4.turned_point
#print axioms OnBytes.Road.K4.levelR_get
#print axioms OnBytes.Road.K4.level_point
