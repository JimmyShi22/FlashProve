-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoEndsE.lean.
The lookup of a sub-proof: the weight of a call's trees, written in two ways.

The record of end values (Fo.endsOf) gives the weight of call c as the sum, over the trees y of
that call, of eq(the point of the trees' numbers, y). The byte-level verifier computes a product
over the top rK - iota_c coordinates of that point (Forest.callWeight; its plain twin is Fo.eK):
the trees of a call share the top bits of their numbers. This file shows that the sum is Fo.eK. That
Fo.eK is Forest.callWeight, read, is stated in OnBytes/Tie/Pv/Lookup/Port/FoTwins.lean (weight_val),
not here.

States:
  eK_list: the product, as the equality weight of a list, for every list and every call.
  sum_filter: a sum over the members of a range that meet a condition, as a sum over a Finset.
  trees_of: under the test of the shape's numbers the trees of call c are the 2^iota_c numbers from
    the call's first tree on.
  weight_sum: the sum over a call's trees is the weight of the top coordinates.
  ends_e: entry c of the record's field e is eK at the record's field zy.
Premises: FoNums.ok h = true; c < NC; in weight_sum the list has rK members. K is any commutative
ring.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinOut

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset Cb.Fo

section
variable {K : Type} [CommRing K]

/-- A product over the bits of X from the top, as the equality weight of the reversed list. -/
theorem prod_top (g : ℕ → K) : ∀ (n X : ℕ),
    ((List.range n).map fun i =>
      if (X / 2 ^ (n - 1 - i)) % 2 = 1 then g i else 1 - g i).prod =
      eqN ((List.range n).map g).reverse X
  | 0, _ => rfl
  | n + 1, X => by
    rw [range_succ_rev, List.range_succ, List.map_append, List.prod_append]
    show _ = (if X % 2 = 1 then g n else 1 - g n) * eqN _ (X / 2)
    rw [← prod_top g n (X / 2), mul_comm]
    congr 1
    · simp
    · refine congrArg List.prod (List.map_congr_left fun i hi => ?_)
      have hi' : i < n := List.mem_range.mp hi
      have e : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
      rw [e, pow_succ', Nat.div_div_eq_div_mul]

/-- Forest.callWeight's twin, as the equality weight of a list. -/
theorem eK_list (h : FoNums.Sh) (zy : List K) (c : ℕ) :
    eK h zy c =
      eqN ((List.range (h.rK - io h c)).map fun i => zy.getD i 0).reverse
        (fst h c / 2 ^ io h c) := by
  unfold eK
  rw [foldl_mul, one_mul]
  exact prod_top (fun i => zy.getD i 0) _ _

theorem sum_filter (p : ℕ → Prop) [DecidablePred p] (g : ℕ → K) : ∀ n : ℕ,
    (((List.range n).filter fun y => decide (p y)).map g).sum = ∑ y ∈ (range n).filter p, g y
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, sum_filter p g n,
      range_add_one, filter_insert]
    by_cases hp : p n
    · rw [if_pos hp, sum_insert (by simp), add_comm]
      simp [hp]
    · rw [if_neg hp]
      simp [hp]

end

/-- The trees of a call. -/
theorem trees_of (h : FoNums.Sh) (H : FoNums.ok h = true) (c : ℕ) (hc : c < h.NC) :
    ((range h.NT).filter fun y => co h y = c) = Ico (fst h c) (fst h c + 2 ^ io h c) := by
  obtain ⟨_, b, d, _⟩ := ok_parts H
  ext y
  simp only [mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨hy, rfl⟩
    exact ⟨(b y hy).2.1, (b y hy).2.2⟩
  · rintro ⟨h1, h2⟩
    have := (d c hc).2.2.2 (y - fst h c) (by omega)
    rw [Nat.add_sub_cancel' h1] at this
    exact ⟨this.1, this.2.1⟩

section
variable {K : Type} [CommRing K]

/-- The sum of eq(q, y) over a call's trees is the weight of q's top coordinates. -/
theorem weight_sum (h : FoNums.Sh) (H : FoNums.ok h = true) (c : ℕ) (hc : c < h.NC) (q : List K)
    (hq : q.length = h.rK) :
    (((List.range h.NT).filter fun y => co h y = c).map fun y => eqN q y).sum =
      eqN (q.drop (io h c)) (fst h c / 2 ^ io h c) := by
  have hio : io h c ≤ h.rK := (ok_prem H).le c hc
  have hdv : fst h c % 2 ^ io h c = 0 := (ok_prem H).dvd c hc
  have hl : (q.take (io h c)).length = io h c := by rw [List.length_take, hq]; omega
  rw [sum_filter (fun y => co h y = c), trees_of h H c hc, sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left]
  have e : ∀ b ∈ range (2 ^ io h c), eqN q (fst h c + b) =
      eqN (q.take (io h c)) b * eqN (q.drop (io h c)) (fst h c / 2 ^ io h c) := by
    intro b hb
    have hb' : b < 2 ^ io h c := mem_range.mp hb
    conv_lhs => rw [← List.take_append_drop (io h c) q]
    rw [eqN_append, hl]
    have e1 : (fst h c + b) % 2 ^ io h c = b := by
      rw [Nat.add_mod, hdv, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hb']
    have e2 : (fst h c + b) / 2 ^ io h c = fst h c / 2 ^ io h c := by
      have hm := Nat.div_add_mod (fst h c) (2 ^ io h c)
      rw [hdv, Nat.add_zero] at hm
      conv_lhs => rw [← hm]
      rw [Nat.mul_add_div (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hb', Nat.add_zero]
    rw [e1, e2]
  rw [sum_congr rfl e, ← Finset.sum_mul]
  have ht := eqN_total (q.take (io h c))
  rw [hl] at ht
  rw [ht, one_mul]

/-- **Entry c of the record's weights is eK, the plain twin of Forest.callWeight's product.** -/
theorem ends_e (h : FoNums.Sh) (H : FoNums.ok h = true) (lm jLK : ℕ) (rs : Rounds K) (c : ℕ)
    (hc : c < h.NC) :
    (endsOf h lm jLK rs).e.getD c 0 = eK h (endsOf h lm jLK rs).zy c := by
  have hio : io h c ≤ h.rK := (ok_prem H).le c hc
  have hp := pntK_len h H lm jLK rs
  have hq : ((pntK (forN h lm jLK rs) (forTrace h lm jLK rs)).take h.rK).length = h.rK := by
    rw [List.length_take, hp]; omega
  generalize hQ : (pntK (forN h lm jLK rs) (forTrace h lm jLK rs)).take h.rK = q at hq
  have e1 : (endsOf h lm jLK rs).e.getD c 0 =
      (((List.range h.NT).filter fun y => co h y = c).map fun y => eqN q y).sum := by
    rw [← hQ]
    show ((List.range h.NC).map fun c => (((List.range h.NT).filter fun y => co h y = c).map
      fun y => eqN ((pntK (forN h lm jLK rs) (forTrace h lm jLK rs)).take h.rK) y).sum).getD c 0 = _
    rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]
  have e2 : (endsOf h lm jLK rs).zy = q.reverse := by rw [← hQ]; rfl
  rw [e1, e2, weight_sum h H c hc q hq, eK_list]
  congr 1
  have e3 : ((List.range (h.rK - io h c)).map fun i => q.reverse.getD i 0) =
      q.reverse.take (h.rK - io h c) := by
    refine List.ext_getElem (by simp [hq]) fun i h1 h2 => ?_
    rw [List.getElem_map, List.getElem_range, List.getElem_take,
      List.getD_eq_getElem _ _ (by simp at h1 ⊢; omega)]
  rw [e3, List.take_reverse, List.reverse_reverse, hq]
  congr 1
  omega

end
end Fo
