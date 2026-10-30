-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPlane.lean.
The lookup of a sub-proof: how its end claims read the planes of counts.

The lookup's last rows read the bits of the counts at a point: the sum over all (row of the joined
table, plane) of an equality weight times the bit. The byte-level verifier does not
walk over these 2^(5 + d) bits. The bits lie in a matrix of 2^lm rows: bit j of the count of row t
of call c lies in row (the low lm - 5 bits of t | j) and column (c | the other bits of t).
The caller hands in, for each column, the sum over the matrix's rows under the weights phiB; the
verifier adds these sums under the weights of the column.

States:
  phiBK, planesK: plain forms, in a commutative ring and on lists, of the byte-level verifier's
    Forest.phiB and Forest.planesAt (OnBytes/Model/Look.lean), at the level of values.
  plane_split: the equality weight of the bit (t | c | j) is the product of phiB's weight of its row
    and the two weights of its column.
  plane_sum: the value of the lookup's form on the bits (TwV.bitsForm at the numbers Fo.numsF) is
    planesK of the columns' sums, for every reading of the places that reads the place "zero" as 0.
Premises: on public numbers alone: 5 ≤ lm ≤ kT + 5, NC ≤ 2^cK, the lengths of the point's four
parts.
Does not say: that phiBK and planesK are Forest.phiB and Forest.planesAt read in a ring. For planesK
that is planesAff_value (OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean); for phiBK it is phiB_val
(OnBytes/Tie/Pv/Lookup/Forest/FoPhi.lean).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTab

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes.Model

section
variable {K : Type} [CommRing K]

/-- The value of a sparse form under a reading of the places. -/
def valS {P : Type} (cf : List (P × K)) (μ : P → K) : K := (cf.map fun pc => pc.2 * μ pc.1).sum

/-- The plain form of Forest.phiB: the weights on the rows of the planes' matrix. -/
def phiBK (h : Sh) (lm : ℕ) (z : List K) : List K :=
  eqTabK (exL z (h.kT + 5 - lm) h.kT ++ exL z (h.kT + h.cK) z.length)

/-- Forest.planesAt, at the level of values: bit col is the value of the caller's form for column
col. -/
def planesK (h : Sh) (lm : ℕ) (z : List K) (bit : ℕ → K) : K :=
  (List.range (h.NC * 2 ^ (h.kT + 5 - lm))).foldl
    (fun f col => f + bit col *
      ((eqTabK (exL z h.kT (h.kT + h.cK))).getD (col / 2 ^ (h.kT + 5 - lm)) 0 *
        (eqTabK (exL z 0 (h.kT + 5 - lm))).getD (col % 2 ^ (h.kT + 5 - lm)) 0)) 0

/-- Four cubes. -/
theorem eqN_split4 (xp xc xl xh : List K) (F : ℕ → ℕ → ℕ → ℕ → K) :
    ∑ e ∈ range (2 ^ (xp.length + (xc.length + (xl.length + xh.length)))),
        eqN (xp ++ (xc ++ (xl ++ xh))) e *
          F (e % 2 ^ xp.length) (e / 2 ^ xp.length % 2 ^ xc.length)
            (e / 2 ^ xp.length / 2 ^ xc.length % 2 ^ xl.length)
            (e / 2 ^ xp.length / 2 ^ xc.length / 2 ^ xl.length) =
      ∑ j ∈ range (2 ^ xp.length), eqN xp j * ∑ c ∈ range (2 ^ xc.length), eqN xc c *
        ∑ a ∈ range (2 ^ xl.length), eqN xl a * ∑ b ∈ range (2 ^ xh.length), eqN xh b * F j c a b :=
            by
  have h1 := eqN_split xp (xc ++ (xl ++ xh)) fun j u =>
    F j (u % 2 ^ xc.length) (u / 2 ^ xc.length % 2 ^ xl.length) (u / 2 ^ xc.length / 2 ^ xl.length)
  rw [List.length_append, List.length_append] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := eqN_split xc (xl ++ xh) fun c t => F j c (t % 2 ^ xl.length) (t / 2 ^ xl.length)
  rw [List.length_append] at h2
  rw [h2]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  rw [eqN_split xl xh fun a b => F j c a b]

/-- Four nested weighted sums, in another order. -/
theorem nest4 (J C A B : Finset ℕ) (wj wc wa wb : ℕ → K) (F : ℕ → ℕ → ℕ → ℕ → K) :
    ∑ j ∈ J, wj j * ∑ c ∈ C, wc c * ∑ a ∈ A, wa a * ∑ b ∈ B, wb b * F j c a b =
      ∑ c ∈ C, ∑ b ∈ B, ∑ a ∈ A, ∑ j ∈ J, (wj j * wa a) * F j c a b * (wc c * wb b) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j
      _ => ?_
  ring

/-- What a reading that reads "zero" as 0 finds at the place of bit j of row u's count. -/
theorem bAt_val (h : Sh) (lm jLK : ℕ) (θ : K) (μ : Pl → K) (h0 : μ .zero = 0) (u j : ℕ) :
    μ ((numsF h lm jLK θ).bAt u j) =
      if u % 2 ^ h.cK < h.NC then
        μ (.cell (2 ^ 5 * (u / 2 ^ h.cK % 2 ^ (lm - 5)) + j)
          (2 ^ (h.kT + 5 - lm) * (u % 2 ^ h.cK) + u / 2 ^ h.cK / 2 ^ (lm - 5)))
      else 0 := by
  show μ (match cellOf h u j with
    | some x => .cell (cellRC h lm x).1 (cellRC h lm x).2
    | none => .zero) = _
  unfold cellOf
  by_cases hc : u % 2 ^ h.cK < h.NC
  · rw [if_pos hc, if_pos hc, Nat.mul_comm (2 ^ 5), Nat.mul_comm (2 ^ (h.kT + 5 - lm))]
    rfl
  · rw [if_neg hc, if_neg hc]
    exact h0

/-- The weight of the bit (t | c | j), t = a + 2^(lm - 5) b: phiB's weight of its row, times the two
weights of its column. -/
theorem plane_split (xp xc xl xh : List K) (j c a b : ℕ) (hj : j < 2 ^ xp.length) (hc : c < 2 ^
    xc.length)
    (ha : a < 2 ^ xl.length) (hb : b < 2 ^ xh.length) :
    eqN (xp ++ (xc ++ (xl ++ xh))) (2 ^ xp.length * (2 ^ xc.length * (2 ^ xl.length * b + a) + c) +
        j) =
      (eqTabK (xl.reverse ++ xp.reverse)).getD (2 ^ xp.length * a + j) 0 *
        ((eqTabK xc.reverse).getD c 0 * (eqTabK xh.reverse).getD b 0) := by
  have dm : ∀ (n q r : ℕ), r < 2 ^ n → (2 ^ n * q + r) % 2 ^ n = r ∧ (2 ^ n * q + r) / 2 ^ n = q :=
      by
    intro n q r hr
    exact ⟨by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr],
      by rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hr, Nat.add_zero]⟩
  rw [eqN_append, (dm _ _ j hj).1, (dm _ _ j hj).2, eqN_append, (dm _ _ c hc).1, (dm _ _ c hc).2,
    eqN_append, (dm _ _ a ha).1, (dm _ _ a ha).2]
  have hrow : 2 ^ xp.length * a + j < 2 ^ (xl.reverse ++ xp.reverse).length := by
    rw [List.length_append, List.length_reverse, List.length_reverse, pow_add]
    calc 2 ^ xp.length * a + j < 2 ^ xp.length * a + 2 ^ xp.length := by omega
      _ = 2 ^ xp.length * (a + 1) := by ring
      _ ≤ 2 ^ xp.length * 2 ^ xl.length := Nat.mul_le_mul_left _ ha
      _ = 2 ^ xl.length * 2 ^ xp.length := Nat.mul_comm _ _
  rw [eqTabK_get, if_pos hrow, List.reverse_append, List.reverse_reverse, List.reverse_reverse,
      eqN_append,
    (dm _ _ j hj).1, (dm _ _ j hj).2, eqTabK_get, List.length_reverse, if_pos hc,
        List.reverse_reverse,
    eqTabK_get, List.length_reverse, if_pos hb, List.reverse_reverse]
  ring

/-- phiB's weight of the row (a | j). -/
theorem phi_get (xp xl : List K) (j a : ℕ) (hj : j < 2 ^ xp.length) (ha : a < 2 ^ xl.length) :
    (eqTabK (xl.reverse ++ xp.reverse)).getD (2 ^ xp.length * a + j) 0 = eqN xp j * eqN xl a := by
  have hrow : 2 ^ xp.length * a + j < 2 ^ (xl.reverse ++ xp.reverse).length := by
    rw [List.length_append, List.length_reverse, List.length_reverse, pow_add]
    calc 2 ^ xp.length * a + j < 2 ^ xp.length * a + 2 ^ xp.length := by omega
      _ = 2 ^ xp.length * (a + 1) := by ring
      _ ≤ 2 ^ xp.length * 2 ^ xl.length := Nat.mul_le_mul_left _ ha
      _ = 2 ^ xl.length * 2 ^ xp.length := Nat.mul_comm _ _
  rw [eqTabK_get, if_pos hrow, List.reverse_append, List.reverse_reverse, List.reverse_reverse,
      eqN_append,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hj, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hj,
        Nat.add_zero]

/-- The lookup's form on the bits, at a point given by coordinate (plane | call | the row's low lm -
5 bits | its other bits, each the lowest bit first), has the value that planesK, the plain form of
Forest.planesAt, adds up from the columns' sums, at the same point as a list, the top bit first. -/
theorem plane_sum (h : Sh) (lm jLK : ℕ) (θ : K) (μ : Pl → K) (h0 : μ .zero = 0) (hNC : h.NC ≤ 2 ^
    h.cK)
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (xp xc xl xh : List K) (hp : xp.length = 5)
    (hc : xc.length = h.cK) (hl : xl.length = lm - 5) (hh : xh.length = h.kT + 5 - lm) :
    valS (bitsForm (numsF h lm jLK θ) (xp ++ (xc ++ (xl ++ xh)))) μ =
      planesK h lm (xp ++ (xc ++ (xl ++ xh))).reverse fun col =>
        ∑ row ∈ range (2 ^ lm),
          (phiBK h lm (xp ++ (xc ++ (xl ++ xh))).reverse).getD row 0 * μ (.cell row col) := by
  have hz : (xp ++ (xc ++ (xl ++ xh))).reverse = xh.reverse ++ (xl.reverse ++ (xc.reverse ++
      xp.reverse)) := by
    simp only [List.reverse_append, List.append_assoc]
  have eh : exL (xh.reverse ++ (xl.reverse ++ (xc.reverse ++ xp.reverse))) 0 (h.kT + 5 - lm) =
      xh.reverse := by
    have := exL_mid [] xh.reverse (xl.reverse ++ (xc.reverse ++ xp.reverse))
    rwa [List.length_reverse, hh, List.length_nil, Nat.zero_add, List.nil_append] at this
  have el : exL (xh.reverse ++ (xl.reverse ++ (xc.reverse ++ xp.reverse))) (h.kT + 5 - lm) h.kT =
      xl.reverse := by
    have := exL_mid xh.reverse xl.reverse (xc.reverse ++ xp.reverse)
    rw [List.length_reverse, List.length_reverse, hh, hl] at this
    rwa [show h.kT + 5 - lm + (lm - 5) = h.kT by omega] at this
  have ec : exL (xh.reverse ++ (xl.reverse ++ (xc.reverse ++ xp.reverse))) h.kT (h.kT + h.cK) =
      xc.reverse := by
    have := exL_mid (xh.reverse ++ xl.reverse) xc.reverse xp.reverse
    rw [List.length_append, List.length_reverse, List.length_reverse, List.length_reverse, hh, hl,
        hc,
      List.append_assoc] at this
    rwa [show h.kT + 5 - lm + (lm - 5) = h.kT by omega] at this
  have ep : exL (xh.reverse ++ (xl.reverse ++ (xc.reverse ++ xp.reverse))) (h.kT + h.cK)
      (xh.reverse ++ (xl.reverse ++ (xc.reverse ++ xp.reverse))).length = xp.reverse := by
    have := exL_mid (xh.reverse ++ (xl.reverse ++ xc.reverse)) xp.reverse []
    rw [List.append_nil, List.append_assoc, List.append_assoc] at this
    have e1 : (xh.reverse ++ (xl.reverse ++ xc.reverse)).length = h.kT + h.cK := by
      simp only [List.length_append, List.length_reverse, hh, hl, hc]
      omega
    have e2 : (xh.reverse ++ (xl.reverse ++ (xc.reverse ++ xp.reverse))).length =
        h.kT + h.cK + xp.reverse.length := by
      simp only [List.length_append, List.length_reverse, hh, hl, hc]
      omega
    rw [e1] at this
    rw [e2]
    exact this
  -- the left side
  have hL : valS (bitsForm (numsF h lm jLK θ) (xp ++ (xc ++ (xl ++ xh)))) μ =
      ∑ e ∈ range (2 ^ (5 + (h.cK + (lm - 5 + (h.kT + 5 - lm))))), eqN (xp ++ (xc ++ (xl ++ xh))) e
          *
        (if e / 2 ^ 5 % 2 ^ h.cK < h.NC then
          μ (.cell (2 ^ 5 * (e / 2 ^ 5 / 2 ^ h.cK % 2 ^ (lm - 5)) + e % 2 ^ 5)
            (2 ^ (h.kT + 5 - lm) * (e / 2 ^ 5 % 2 ^ h.cK) + e / 2 ^ 5 / 2 ^ h.cK / 2 ^ (lm - 5)))
        else 0) := by
    unfold valS bitsForm
    rw [List.map_map, lsum]
    have hexp : (numsF h lm jLK θ).w + (numsF h lm jLK θ).d = 5 + (h.cK + (lm - 5 + (h.kT + 5 -
        lm))) := by
      show 5 + (h.kT + h.cK) = _
      omega
    rw [hexp]
    refine Finset.sum_congr rfl fun e _ => ?_
    show eqN _ e * μ ((numsF h lm jLK θ).bAt (e / 2 ^ 5) (e % 2 ^ 5)) = _
    rw [bAt_val h lm jLK θ μ h0]
  have h4 := eqN_split4 xp xc xl xh fun j c a b =>
    if c < h.NC then μ (.cell (2 ^ 5 * a + j) (2 ^ (h.kT + 5 - lm) * c + b)) else 0
  rw [hp, hc, hl, hh] at h4
  rw [hL, h4, nest4, hz]
  unfold planesK phiBK
  rw [eh, el, ec, ep, foldl_sum, Nat.mul_comm h.NC, sum_mul]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 hNC)]
  · refine Finset.sum_congr rfl fun c hcm => Finset.sum_congr rfl fun b hbm => ?_
    have hc' : c < h.NC := Finset.mem_range.mp hcm
    have hb' : b < 2 ^ (h.kT + 5 - lm) := Finset.mem_range.mp hbm
    have e1 : (2 ^ (h.kT + 5 - lm) * c + b) / 2 ^ (h.kT + 5 - lm) = c := by
      rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hb', Nat.add_zero]
    have e2 : (2 ^ (h.kT + 5 - lm) * c + b) % 2 ^ (h.kT + 5 - lm) = b := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
    rw [e1, e2, eqTabK_get, List.length_reverse, hc, if_pos (lt_of_lt_of_le hc' hNC),
        List.reverse_reverse,
      eqTabK_get, List.length_reverse, hh, if_pos hb', List.reverse_reverse,
      show 2 ^ lm = 2 ^ 5 * 2 ^ (lm - 5) by rw [← pow_add]; congr 1; omega]
    beta_reduce
    rw [sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ham => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hjm => ?_
    have hph := phi_get xp xl j a (by rw [hp]; exact Finset.mem_range.mp hjm)
      (by rw [hl]; exact Finset.mem_range.mp ham)
    rw [hp] at hph
    rw [hph, if_pos hc']
  · intro c _ hcn
    have hc' : ¬ c < h.NC := fun hlt => hcn (Finset.mem_range.mpr hlt)
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun j _ =>
        ?_
    rw [if_neg hc']
    ring

end
end Fo
