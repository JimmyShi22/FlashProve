-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPadSum.lean: the padding of a sub-proof's lookup, counted by call, is
the verifier's own number of padding keys.

The verifier describes the padding by tree: pub[y] padding keys in tree y, and whole trees of
padding (Shape.emptyKeys). Shape.padding adds these up; it enters the target of the counts' sum, 2^v
- padding (Forest.planeClaims).
The assembled lookup takes the padding by row of the joined table: for each call c the row that its
padding keys hold and how many keys hold it (FoNums.pads). pads_sum: where FoNums.ok h holds, the
second numbers of these pairs add up to Shape.padding h.
So the natural number in the target of the assembled lookup's row on the counts, 2^v less padNum
(numRowF, Cb/Pv/Lookup/Blocks/HeadF.lean), is the verifier's 2^v - padding (forA_padNum, with ok_v
of OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean). No statement compares the two rows or the two field
elements.

Main theorems: sum_by_class, pads_sum_of, pads_sum, padding_le, forA_padNum.
Not claimed: that the product of (alpha - row)^count over the pairs is the public factor of
Forest.draws.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoHole

set_option autoImplicit false

namespace Cb.Fo
open Cb Cb.LdLkp Cb.Lkp

theorem sum_pick (a k : ℕ) :
    ∀ N, ((List.range N).map fun c => if k = c then a else 0).sum = if k < N then a else 0
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_pick a k N]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases h1 : k < N
    · rw [if_pos h1, if_neg (by omega), if_pos (by omega), Nat.add_zero]
    · by_cases h2 : k = N
      · rw [if_neg h1, if_pos h2, if_pos (by omega), Nat.zero_add]
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]

/-- A sum over a list, taken class by class. -/
theorem sum_by_class (g f : ℕ → ℕ) (N : ℕ) : ∀ ys : List ℕ, (∀ y ∈ ys, g y < N) →
    ((List.range N).map fun c => ((ys.filter fun y => g y = c).map f).sum).sum = (ys.map f).sum
  | [], _ => by simp
  | y :: ys, hy => by
    have ih := sum_by_class g f N ys fun z hz => hy z (List.mem_cons_of_mem _ hz)
    have e : (fun c => (((y :: ys).filter fun y => g y = c).map f).sum) =
        fun c => (if g y = c then f y else 0) + ((ys.filter fun y => g y = c).map f).sum := by
      funext c
      by_cases hc : g y = c
      · simp [hc]
      · simp [hc]
    rw [e, List.sum_map_add, ih, sum_pick, if_pos (hy y List.mem_cons_self), List.map_cons,
        List.sum_cons]

theorem array_sum (a : Array ℕ) (e : ℕ) :
    a.foldl (· + ·) e = e + ((List.range a.size).map fun y => a.getD y 0).sum := by
  rw [← Array.foldl_toList, OnBytes.foldl_add]
  congr 1
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [Array.length_toList] at h1
  simp [Array.getD, h1]

/-- The padding counted by call is the verifier's number of padding keys: from the three facts that
the proof reads. -/
theorem pads_sum_of {h : Sh} (a2 : 1 ≤ h.NC) (a6 : h.pub.size = h.NT)
    (b : ∀ y < h.NT, FoNums.co h y < h.NC) :
    padNum (FoNums.pads h) = h.padding := by
  unfold padNum FoNums.pads OnBytes.Model.Forest.Shape.padding
  rw [array_sum, a6, List.map_map]
  have e : (Prod.snd ∘ fun c => (FoNums.padRow h c, FoNums.padCount h c)) =
      fun c => (((List.range h.NT).filter fun y => FoNums.co h y = c).map fun y => h.pub.getD y
          0).sum + if 0 = c then h.emptyKeys else 0 := by
    funext c
    show FoNums.padCount h c = _
    unfold FoNums.padCount
    by_cases hc : c = 0
    · rw [if_pos hc, if_pos hc.symm]
    · rw [if_neg hc, if_neg (Ne.symm hc)]
  rw [e, List.sum_map_add, sum_by_class _ _ _ _ (fun y hy => b y (List.mem_range.1 hy)), sum_pick,
      if_pos (show 0 < h.NC from a2), Nat.add_comm]

/-- The padding counted by call is the verifier's number of padding keys. -/
theorem pads_sum {h : Sh} (H : FoNums.ok h = true) : padNum (FoNums.pads h) = h.padding :=
  pads_sum_of (ok_parts H).1.2.1 (ok_parts H).1.2.2.2.2.2.1 fun y hy => ((ok_parts H).2.1 y hy).1

theorem sum_le_mul (f : ℕ → ℕ) (B : ℕ) (hf : ∀ y, f y ≤ B) : ∀ n, ((List.range n).map f).sum ≤ n * B
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, Nat.succ_mul]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact Nat.add_le_add (sum_le_mul f B hf n) (hf n)

/-- There are at most as many padding keys as keys, if no tree holds more of them than it has
places. -/
theorem padding_le {h : Sh} (a4 : h.NT ≤ 2 ^ h.rK) (a6 : h.pub.size = h.NT)
    (hb : ∀ y, h.pub.getD y 0 ≤ 2 ^ h.dT) :
    h.padding ≤ 2 ^ h.v := by
  unfold OnBytes.Model.Forest.Shape.padding OnBytes.Model.Forest.Shape.emptyKeys
      OnBytes.Model.Forest.Shape.v
  rw [array_sum, a6, Nat.pow_add, Nat.mul_comm (2 ^ h.dT)]
  have h1 := sum_le_mul (fun y => h.pub.getD y 0) (2 ^ h.dT) hb h.NT
  have h2 : (2 ^ h.rK - h.NT) * 2 ^ h.dT + h.NT * 2 ^ h.dT = 2 ^ h.rK * 2 ^ h.dT := by
    rw [← Nat.add_mul, Nat.sub_add_cancel a4]
  omega

theorem forA_padNum (E : Type) [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    {h : Sh} (L : Lay E St₀ J₀)
    (H : FoNums.ok h = true) : padNum (forA E h L).pads = h.padding := pads_sum H

end Cb.Fo
