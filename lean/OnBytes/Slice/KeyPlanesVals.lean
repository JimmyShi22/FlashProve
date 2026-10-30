-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyPlanesVals.lean: vectors of product form by numbers, over the field: the sum of a
table of bits under such a vector, the range table's extension, the vector of the count.

A lookup's rows on the prover's message speak of the lookup's table of bits through vectors that are
products of pairs, one pair for each variable (OnBytes/Slice/KeyData.lean: `FRow`). This file has,
by numbers: the entry of such a vector (`pairsW`); the sum of a table of bits under it (`bitsUnder`:
the plane in the low mu bits of an index, the table's row above); and three such vectors in closed
form.

Main definitions: `pairsW`, `bitsUnder`, `bitsVal`. (`countPairs` is in
OnBytes/Slice/KeyPlanesDefs.lean.)
Main theorems.
 `pairsW_append`, `pairsW_ones`   two lists of pairs; pairs (1, 1).
 `pairsW_eqPairs`     the pairs of a point give the equality vector.
 `sum_bits`           the sum of 2 ^ i times coordinate i of a point is the extension, at the point,
                     of the table whose row t is the number t.
 `pairsW_powers`, `pairsW_count`   the vector of the count has the entry 2 ^ j at plane j, in every
                                   row.
 `bitsUnder_count`    so the sum of the bits under it is the sum of 2 ^ j times the bits.
 `bitsUnder_eq`, `bitsUnder_treeMap`   the sum of the bits under the equality vector at a point is
                     the extension of the table of bits at the point.

Not claimed. Nothing on the program's functions. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyLeavesEq
import OnBytes.Slice.KeyPlanesDefs
import OnBytes.Slice.KeyData

set_option autoImplicit false

namespace OnBytes.Slice.Planes
open Prob Cb
open OnBytes.Slice.Leaves (sum_range_two_mul)

/-- The entry at index j of the vector that is the product of the pairs: of each pair the second
half if the matching bit of j is 1, else the first. The first pair goes with the lowest bit. -/
def pairsW : List (GE × GE) → ℕ → GE
  | [], _ => 1
  | p :: ps, j => (if j % 2 = 1 then p.2 else p.1) * pairsW ps (j / 2)

/-- The sum of a table of bits under a vector that is a product of pairs. Bt t j: the bit at the
table's row t and the plane j. -/
def bitsUnder (mu d : ℕ) (Bt : ℕ → ℕ → GE) (ps : List (GE × GE)) : GE :=
  ∑ j ∈ Finset.range (2 ^ mu), ∑ t ∈ Finset.range (2 ^ d), pairsW ps (j + 2 ^ mu * t) * Bt t j

/-- Two lists of pairs, one behind the other. -/
theorem pairsW_append : ∀ (a b : List (GE × GE)) (j : ℕ),
    pairsW (a ++ b) j = pairsW a j * pairsW b (j / 2 ^ a.length)
  | [], b, j => by simp [pairsW]
  | p :: a, b, j => by
    rw [List.cons_append, pairsW, pairsW, pairsW_append a b, List.length_cons, pow_succ',
      Nat.div_div_eq_div_mul, mul_assoc]

/-- Pairs (1, 1) give the factor 1 at every index. -/
theorem pairsW_ones : ∀ (d j : ℕ), pairsW (List.replicate d (1, 1)) j = 1
  | 0, _ => rfl
  | d + 1, j => by
    rw [List.replicate_succ, pairsW, pairsW_ones d]
    split <;> simp

/-- The pairs of a point give the equality vector. -/
theorem pairsW_eqPairs : ∀ (z : List GE) (j : ℕ), pairsW (eqPairs z) j = Leaves.eqW z j
  | [], _ => rfl
  | x :: z, j => by
    show (if j % 2 = 1 then x else 1 - x) * pairsW (eqPairs z) (j / 2) = _
    rw [pairsW_eqPairs z, Leaves.eqW_cons]

/-! ## The range table -/

/-- The sum of 2 ^ i times coordinate i. -/
def bitsVal : List GE → GE
  | [] => 0
  | x :: xs => x + 2 * bitsVal xs

/-- The extension of the range table: the sum of 2 ^ i times coordinate i of a point is the sum
over the numbers t of the equality vector times t. -/
theorem sum_bits : ∀ z : List GE,
    ∑ t ∈ Finset.range (2 ^ z.length), Leaves.eqW z t * (t : GE) = bitsVal z
  | [] => by simp [Leaves.eqW, bitsVal]
  | x :: xs => by
    rw [List.length_cons, pow_succ', sum_range_two_mul]
    have h : ∀ k, Leaves.eqW (x :: xs) (2 * k) * ((2 * k : ℕ) : GE) +
        Leaves.eqW (x :: xs) (2 * k + 1) * ((2 * k + 1 : ℕ) : GE) =
        2 * (Leaves.eqW xs k * (k : GE)) + x * Leaves.eqW xs k := by
      intro k
      rw [Leaves.eqW_cons, Leaves.eqW_cons, show 2 * k % 2 = 0 by omega,
        show (2 * k + 1) % 2 = 1 by omega,
        show 2 * k / 2 = k by omega, show (2 * k + 1) / 2 = k by omega, if_neg (by decide),
        if_pos rfl]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun k _ => h k, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_bits xs, Leaves.eqW_sum, bitsVal]
    ring

/-! ## The vector of the count -/

/-- The pairs (1, 2 ^ 2 ^ t) for n numbers t from s on give 2 to the power 2 ^ s times the n low
bits of the index. -/
theorem pairsW_powers : ∀ (n s j : ℕ),
    pairsW ((List.range' s n).map fun t => ((1 : GE), (2 : GE) ^ 2 ^ t)) j =
      (2 : GE) ^ (2 ^ s * (j % 2 ^ n))
  | 0, _, _ => by simp [pairsW, Nat.mod_one]
  | n + 1, s, j => by
    rw [List.range'_succ, List.map_cons, pairsW, pairsW_powers n (s + 1), pow_succ' 2 n,
      Nat.mod_mul]
    by_cases h : j % 2 = 1
    · rw [if_pos h, h, ← pow_add]
      congr 1
      rw [pow_succ]
      ring
    · rw [if_neg h, show j % 2 = 0 by omega, one_mul]
      congr 1
      rw [pow_succ]
      ring

/-- The vector of the count has the entry 2 ^ j at plane j, in every row. -/
theorem pairsW_count (mu d j t : ℕ) (hj : j < 2 ^ mu) :
    pairsW (countPairs mu d) (j + 2 ^ mu * t) = (2 : GE) ^ j := by
  unfold countPairs
  rw [pairsW_append, pairsW_ones, mul_one, List.range_eq_range', pairsW_powers, pow_zero,
    Nat.one_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

/-- The sum of the bits under the vector of the count. -/
theorem bitsUnder_count (mu d : ℕ) (Bt : ℕ → ℕ → GE) :
    bitsUnder mu d Bt (countPairs mu d) =
      ∑ j ∈ Finset.range (2 ^ mu), ∑ t ∈ Finset.range (2 ^ d), (2 : GE) ^ j * Bt t j := by
  unfold bitsUnder
  exact Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun t _ => by
    rw [pairsW_count mu d j t (Finset.mem_range.1 hj)]

/-- The sum of the bits under the equality vector at a point. -/
theorem bitsUnder_eq (mu d : ℕ) (Bt : ℕ → ℕ → GE) (z : List GE) :
    bitsUnder mu d Bt (eqPairs z) =
      ∑ j ∈ Finset.range (2 ^ mu), ∑ t ∈ Finset.range (2 ^ d),
        Leaves.eqW z (j + 2 ^ mu * t) * Bt t j := by
  unfold bitsUnder
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => by rw [pairsW_eqPairs]

/-- The sum of the bits under the equality vector at a point is the extension of the table of bits
at the point: the table on lists of 0 and 1, the highest bit of the index first, the plane in the
low mu bits of the index. -/
theorem bitsUnder_treeMap (mu d : ℕ) (Bt : ℕ → ℕ → GE) (z : List GE) (h : z.length = mu + d) :
    bitsUnder mu d Bt (eqPairs z) =
      treeMap (mu + d) (fun q =>
        Bt (Leaves.numFrom 0 q / 2 ^ mu) (Leaves.numFrom 0 q % 2 ^ mu)) z := by
  rw [Leaves.treeMap_sum (fun N => Bt (N / 2 ^ mu) (N % 2 ^ mu)) (mu + d) z h, bitsUnder_eq,
    pow_add, Leaves.sum_range_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos mu), Nat.div_eq_of_lt hj', Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj']

end OnBytes.Slice.Planes
