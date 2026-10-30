-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoReadsBZ.lean: the planes of the counts in the smallness test's own
lookup: the sums that its three claims on the planes write, against the flat function's forms.

The smallness test does not call Forest.planeClaims. HTailF2.linBits9 writes the three claims by
hand, as runs on virtual rows of the array BZ. Bit number X = (t | c | j) of the planes (t: the row
of the call's table, c: the call, j: the plane), that is X = u * 32 + j for row u = t * 2^cK + c of
the joined table, stands in row X / KB and column X % KB of BZ, where KB = 2^(kT + cK); BZ has 32
rows. A claim's run has the weights w on the columns; its virtual row is a combination of BZ's rows.
For a point z of 5 + m coordinates (an array, the top bit first; m = kT + cK) the first five
coordinates give the weights on the rows, the others the weights on the columns.

 - OnBZ N μ m B: the entries μ at the flat function's places of the bits are BZ's entries B, by
   that map.
 - bits_on_bz: the flat function's form of the planes at the point z (bitsForm) is the sum over
   BZ's columns of eqTabK (z.drop 5) times the sum over BZ's rows of eqTabK (z.take 5) times the
   entry.
 - count_on_bz: the form of the claim on the counts' sum (rowNum) is the sum over BZ's columns of
   2^(column mod 32) times the sum over BZ's rows of the entry.
Both hold over every commutative ring, for all public numbers N, entries μ and B. Premises of both:
OnBZ N μ m B; N.d = m. Of bits_on_bz also: N.w = 5; z has 5 + m coordinates; its form is bitsForm N
at the reversal of z. Of count_on_bz also: N.n = 30; 5 ≤ m.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run of linBits9 adds these sums to the one equation, or that a virtual row
of BZ is the combination of rows that is named here.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPin

set_option autoImplicit false

namespace Fo
open TwV Finset Cb.Fo.Pin

section
variable {P K : Type} [CommRing K]

/-- The entries at the flat function's places of the bits are BZ's entries: bit j of the count of
row u of the joined table is bit number u * 32 + j. Asked at the table's 2^m rows alone. -/
def OnBZ (N : Nums P K) (μ : P → K) (m : ℕ) (B : ℕ → ℕ → K) : Prop :=
  ∀ u j, u < 2 ^ m → j < 32 → μ (N.bAt u j) = B ((u * 32 + j) / 2 ^ m) ((u * 32 + j) % 2 ^ m)

/-- A point's weights, cut into BZ's rows and columns. -/
theorem bz_split (z : List K) (m : ℕ) (hz : z.length = 5 + m) (B : ℕ → ℕ → K) :
    ∑ X ∈ range (2 ^ (m + 5)), eqN z.reverse X * B (X / 2 ^ m) (X % 2 ^ m) =
      ∑ i ∈ range (2 ^ m), (eqTabK (z.drop 5)).getD i 0 *
        ∑ r ∈ range 32, (eqTabK (z.take 5)).getD r 0 * B r i := by
  have hlo : (z.drop 5).reverse.length = m := by rw [List.length_reverse, List.length_drop]; omega
  have hhi : (z.take 5).reverse.length = 5 := by rw [List.length_reverse, List.length_take]; omega
  have hr : z.reverse = (z.drop 5).reverse ++ (z.take 5).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  have h := eqN_split (z.drop 5).reverse (z.take 5).reverse fun i r => B r i
  rw [← hr, hlo, hhi] at h
  rw [h]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < 2 ^ (z.drop 5).length := by
    rw [← List.length_reverse, hlo]
    exact Finset.mem_range.mp hi
  rw [eqTabK_get, if_pos hi']
  congr 1
  refine Finset.sum_congr rfl fun r hr' => ?_
  have hr'' : r < 2 ^ (z.take 5).length := by
    rw [← List.length_reverse, hhi]
    exact Finset.mem_range.mp hr'
  rw [eqTabK_get, if_pos hr'']

/-- The planes at a point, on BZ. -/
theorem bits_on_bz (N : Nums P K) (μ : P → K) (m : ℕ) (B : ℕ → ℕ → K) (hw : N.w = 5)
    (hd : N.d = m) (hB : OnBZ N μ m B) (z : List K) (hz : z.length = 5 + m) :
    valS (bitsForm N z.reverse) μ =
      ∑ i ∈ range (2 ^ m), (eqTabK (z.drop 5)).getD i 0 *
        ∑ r ∈ range 32, (eqTabK (z.take 5)).getD r 0 * B r i := by
  rw [← bz_split z m hz B]
  unfold valS bitsForm
  rw [List.map_map, lsum, hw, hd, Nat.add_comm 5 m]
  refine Finset.sum_congr rfl fun X hX => ?_
  have hX' : X / 2 ^ 5 < 2 ^ m := by
    have := Finset.mem_range.mp hX
    rw [pow_add] at this
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at this)
  show eqN z.reverse X * μ (N.bAt (X / 2 ^ 5) (X % 2 ^ 5)) = _
  rw [hB _ _ hX' (Nat.mod_lt _ (by norm_num)), show (2 : ℕ) ^ 5 = 32 from rfl, Nat.div_add_mod']

/-- The counts' sum, on BZ. -/
theorem count_on_bz (N : Nums P K) (μ : P → K) (m : ℕ) (B : ℕ → ℕ → K) (hn : N.n = 30)
    (hd : N.d = m) (h5 : 5 ≤ m) (hB : OnBZ N μ m B) :
    valS (rowNum N).cf μ =
      ∑ i ∈ range (2 ^ m), (2 : K) ^ (i % 32) * ∑ r ∈ range 32, B r i := by
  have e1 : valS (rowNum N).cf μ =
      ∑ X ∈ range (32 * 2 ^ m), (2 : K) ^ (X % 32) * B (X / 2 ^ m) (X % 2 ^ m) := by
    rw [sum_mul 32]
    show valS ((List.range (2 ^ N.d)).flatMap fun u =>
      (List.range (N.n + 2)).map fun j => (N.bAt u j, (2 : K) ^ j)) μ = _
    rw [valS_flatMap, hd, hn]
    refine Finset.sum_congr rfl fun u hu => ?_
    unfold valS
    rw [List.map_map, lsum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 32 := Finset.mem_range.mp hj
    show (2 : K) ^ j * μ (N.bAt u j) = _
    rw [hB u j (Finset.mem_range.mp hu) hj', Nat.mul_comm 32 u, Nat.mul_add_mod_of_lt hj']
  rw [e1, Nat.mul_comm 32, sum_mul (2 ^ m), Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < 2 ^ m := Finset.mem_range.mp hi
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  obtain ⟨k, rfl⟩ : ∃ k, m = 5 + k := ⟨m - 5, by omega⟩
  have e2 : (2 ^ (5 + k) * r + i) % 32 = i % 32 := by
    rw [pow_add, show (2 : ℕ) ^ 5 = 32 from rfl, Nat.mul_assoc, Nat.mul_add_mod]
  rw [e2, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hi', Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hi']

end
end Fo
