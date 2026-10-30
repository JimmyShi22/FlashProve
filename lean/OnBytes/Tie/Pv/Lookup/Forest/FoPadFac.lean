-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPadFac.lean.
The padding of a sub-proof's lookup: the public factor, in the verifier's own form.

The flat function of the lookup reads the padding as a list of pairs (row of the joined table,
how many padding keys hold it), one pair for each call (`FoNums.pads`).
The verifier reads it tree by tree: tree y of call `callOf y` has `pub y` padding keys, and the
trees that belong to no call hold call 0's padding key alone.
This file states that the two readings give one public factor. (That they give one number of padding
keys is `pads_sum` of OnBytes/Tie/Pv/Lookup/Forest/FoPadSum.lean.) All is stated over a commutative
ring K, on plain data.

Main names, at every lawful shape h (`FoNums.ok h`):
  `padKeyK h θ c`: the padding key of call c, moved by the shift θ. `tab_padRow`: it is the joined
  table's row `FoNums.padRow h c`, for c < NC.
  `facK h θ α`: the public factor, by the verifier's rule: the product over the trees y < NT of (α -
  padding key of the tree's call) ^ (pub y), from (α - padding key of call 0) ^ (keys in the trees
  of padding alone) on.
  `pad_fac`: the flat function's factor `TwV.fac` at the forest's numbers is `facK`.
  `pin_target`: the target of the flat function's row that sums the counts is 2^v - h.padding.

Limits: that `padKeyK` and `facK` are the verifier's functions on its own field elements is not
  stated here. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTies
import OnBytes.Tie.Pv.Lookup.Forest.FoPadSum
import OnBytes.Tie.Pv.Lookup.Forest.FoV
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace Cb.Fo.PadFac
open TwV Cb.Fo Finset

section
variable {K : Type} [CommRing K]

/-- The padding key of call c, moved by the shift. -/
def padKeyK (h : Sh) (θ : K) (c : ℕ) : K :=
  ((FoNums.tauN h c (FoNums.t0Of h c) : ℕ) : K) + (c : K) * θ

/-- The public factor, by the verifier's rule. -/
def facK (h : Sh) (θ α : K) : K :=
  (List.range h.NT).foldl (fun a y => a * (α - padKeyK h θ (FoNums.co h y)) ^ h.pub.getD y 0)
    ((α - padKeyK h θ 0) ^ h.emptyKeys)

theorem foldl_mul (g : ℕ → K) : ∀ (n : ℕ) (a : K),
    (List.range n).foldl (fun a y => a * g y) a = a * ∏ y ∈ range n, g y
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, foldl_mul g n a, prod_range_succ, ← mul_assoc]
    rfl

theorem prod_map_range (g : ℕ → K) : ∀ n : ℕ, ((List.range n).map g).prod = ∏ y ∈ range n, g y
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, prod_map_range g n, prod_range_succ]
    simp

theorem sum_filter_range (p : ℕ → Prop) [DecidablePred p] (g : ℕ → ℕ) : ∀ n : ℕ,
    (((List.range n).filter fun y => decide (p y)).map g).sum = ∑ y ∈ (range n).filter p, g y
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
        sum_filter_range p g n, range_add_one,
      filter_insert]
    by_cases hp : p n
    · rw [if_pos hp, sum_insert (by simp)]
      simp [hp, add_comm]
    · rw [if_neg hp]
      simp [hp]

/-- how many padding keys hold call c's padding row, as a sum -/
theorem padCount_eq (h : Sh) (c : ℕ) : FoNums.padCount h c =
    (∑ y ∈ (range h.NT).filter fun y => FoNums.co h y = c, h.pub.getD y 0) + if c = 0 then
        h.emptyKeys else 0 := by
  unfold FoNums.padCount
  rw [← sum_filter_range (fun y => FoNums.co h y = c)]

variable (h : Sh) (H : FoNums.ok h = true)
include H

/-- The padding key of a call is its padding row of the joined table. -/
theorem tab_padRow (θ : K) (c : ℕ) (hc : c < h.NC) : _root_.Fo.tabF h θ (FoNums.padRow h c) =
    padKeyK h θ c := by
  obtain ⟨⟨_, h1, h2, _⟩, _, h3, _⟩ := ok_parts H
  have ht := (h3 c hc).1
  have hm : (c + 2 ^ h.cK * FoNums.t0Of h c) % 2 ^ h.cK = c := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lt_of_lt_of_le hc h2)]
  have hq : (c + 2 ^ h.cK * FoNums.t0Of h c) / 2 ^ h.cK = FoNums.t0Of h c := by
    rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero
        (by positivity)), Nat.div_eq_of_lt (lt_of_lt_of_le hc h2), Nat.zero_add]
  have hf : FoNums.fT h (FoNums.padRow h c) = c := by
    unfold FoNums.fT FoNums.padRow
    rw [hm]
    omega
  have hr : FoNums.rowOf h (FoNums.padRow h c) = (c, FoNums.t0Of h c) := by
    unfold FoNums.rowOf
    rw [hf]
    unfold FoNums.padRow
    rw [hq, Nat.mod_eq_of_lt ht]
  unfold _root_.Fo.tabF padKeyK
  rw [hr]

/-- **The flat function's public factor is the verifier's.** -/
theorem pad_fac (lm jLK : ℕ) (θ α : K) : fac (_root_.Fo.numsF h lm jLK θ) α = facK h θ α := by
  obtain ⟨⟨_, h1, _⟩, h2, _⟩ := ok_parts H
  unfold fac facK
  show (((List.range h.NC).map fun c => (FoNums.padRow h c, FoNums.padCount h c)).map
    fun e => (α - _root_.Fo.tabF h θ e.1) ^ e.2).prod = _
  rw [List.map_map, prod_map_range, foldl_mul]
  have e1 : ∀ c ∈ range h.NC, ((fun e : ℕ × ℕ => (α - _root_.Fo.tabF h θ e.1) ^ e.2) ∘ fun c =>
      (FoNums.padRow h c, FoNums.padCount h c)) c =
      (∏ y ∈ (range h.NT).filter fun y => FoNums.co h y = c,
          (α - padKeyK h θ (FoNums.co h y)) ^ h.pub.getD y 0) *
        (α - padKeyK h θ c) ^ (if c = 0 then h.emptyKeys else 0) := by
    intro c hc
    show (α - _root_.Fo.tabF h θ (FoNums.padRow h c)) ^ FoNums.padCount h c = _
    rw [tab_padRow h H θ c (mem_range.mp hc), padCount_eq, pow_add, ← prod_pow_eq_pow_sum]
    refine congrArg (· * _) (prod_congr rfl fun y hy => ?_)
    rw [(mem_filter.mp hy).2]
  rw [prod_congr rfl e1, prod_mul_distrib,
    prod_fiberwise_of_maps_to (fun y hy => mem_range.mpr (h2 y (mem_range.mp hy)).1), mul_comm]
  refine congrArg (· * _) ?_
  rw [prod_eq_single 0 (fun c _ hc => by
      rw [if_neg hc, pow_zero]) (fun hn => absurd (mem_range.mpr h1) hn), if_pos rfl]

/-- The target of the row that sums the counts. -/
theorem pin_target (lm jLK : ℕ) (θ : K) :
    (rowNum (_root_.Fo.numsF h lm jLK θ)).tg = ((2 ^ h.v - h.padding : ℕ) : K) := by
  show ((2 ^ (FoNums.v' h + 1) - ((FoNums.pads h).map Prod.snd).sum : ℕ) : K) = _
  rw [show ((FoNums.pads h).map Prod.snd).sum = h.padding from pads_sum H, ← ok_v H]

end
end Cb.Fo.PadFac
