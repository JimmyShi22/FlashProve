-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Mle.lean: THE EQUALITY WEIGHTS OF Corner.lean AGAINST THE TABLES OF
OnBytes/Desc/First/P1/SumMle.lean (a bridge for Lemma 2b). There a table is a function of a list of
bits, the first bit the first round's; here an index's bits are read the highest first. `idxOf`: from
bits to the index. `mle_idx`: the multilinear extension of a table that is a function g of the index
is the sum of wt rs i * g i. `tot_pairs`: the table's sum under the weights (1 - z, z) is its
extension at z. `wt_append`: a point in two parts.
-/
import Mathlib
import OnBytes.Desc.First.P1.SumMle
import Johnson.Desc.Kinds.Law.Corner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Desc.First.P1 (mle tot)

/-- The n low bits of i, the highest first. -/
def bl : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, i => i.testBit n :: bl n i

theorem bl_length : ∀ (n i : Nat), (bl n i).length = n
  | 0, _ => rfl
  | n + 1, i => by simp [bl, bl_length n i]

theorem bl_congr : ∀ (n i i' : Nat), (∀ j, j < n → i.testBit j = i'.testBit j) → bl n i = bl n i'
  | 0, _, _, _ => rfl
  | n + 1, i, i', h => by
    simp only [bl]
    rw [h n (Nat.lt_succ_self n), bl_congr n i i' fun j hj => h j (Nat.lt_succ_of_lt hj)]

/-- The extension of a table, as a sum over indices. -/
theorem mle_eq_sum : ∀ (rs : List K) (A : List Bool → K),
    mle rs.length A rs = (Finset.range (2 ^ rs.length)).sum fun i => wt rs i * A (bl rs.length i)
  | [], A => by simp [mle, wt, bl]
  | r :: rs, A => by
    simp only [List.length_cons, mle]
    rw [mle_eq_sum rs, mle_eq_sum rs, pow_succ, Nat.mul_two, Finset.sum_range_add, Finset.mul_sum,
      Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [wt, bl]
      rw [Nat.testBit_lt_two_pow (Finset.mem_range.mp hi)]
      simp only [Bool.false_eq_true, if_false]
      ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [wt, bl]
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (Finset.mem_range.mp hi),
        wt_congr rs (2 ^ rs.length + i) i fun j hj => Nat.testBit_two_pow_add_gt hj i,
        bl_congr rs.length (2 ^ rs.length + i) i fun j hj => Nat.testBit_two_pow_add_gt hj i]
      simp only [Bool.not_false, if_true]
      ring

/-- From bits, the highest first, to the index. -/
def idxOf : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + idxOf bs

theorem idxOf_bl : ∀ (n i : Nat), idxOf (bl n i) = i % 2 ^ n
  | 0, i => by simp [bl, idxOf, Nat.mod_one]
  | n + 1, i => by
    simp only [bl, idxOf, bl_length]
    rw [idxOf_bl n i, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ n) with h | h <;> simp [h] <;> omega

/-- **The extension of a table that is a function of the index.** -/
theorem mle_idx (rs : List K) (g : Nat → K) :
    mle rs.length (fun b => g (idxOf b)) rs
      = (Finset.range (2 ^ rs.length)).sum fun i => wt rs i * g i := by
  rw [mle_eq_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [idxOf_bl, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]

/-- The sum of a table under the weights (1 - z, z) is its extension at z. -/
theorem tot_pairs : ∀ (zs : List K) (F : List Bool → K),
    tot (zs.map fun z => (1 - z, z)) F = mle zs.length F zs
  | [], _ => rfl
  | z :: zs, F => by
    simp only [List.map_cons, tot, List.length_cons, mle]
    rw [tot_pairs zs, tot_pairs zs]

/-- A point in two parts: the high bits' weight times the low bits'. -/
theorem wt_append : ∀ (a b : List K) (i : Nat),
    wt (a ++ b) i = wt a (i / 2 ^ b.length) * wt b i
  | [], b, i => by simp [wt]
  | x :: xs, b, i => by
    simp only [List.cons_append, wt, List.length_append]
    rw [wt_append xs b i, Nat.testBit_div_two_pow]
    ring

/-- A sum over the indices of a point in two parts. -/
theorem sum_two_parts (a b : List K) (g : Nat → K) :
    ((Finset.range (2 ^ (a ++ b).length)).sum fun i => wt (a ++ b) i * g i)
      = (Finset.range (2 ^ a.length)).sum fun t => (Finset.range (2 ^ b.length)).sum fun k =>
          wt a t * wt b k * g (2 ^ b.length * t + k) := by
  rw [List.length_append, pow_add, ← sum_blocks (2 ^ b.length) _ (2 ^ a.length)]
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hpos : 0 < 2 ^ b.length := by positivity
  rw [wt_append]
  have h1 : (2 ^ b.length * t + k) / 2 ^ b.length = t := by
    rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hk', Nat.add_zero]
  have h2 : wt b (2 ^ b.length * t + k) = wt b k := by
    apply wt_congr
    intro j hj
    rw [Nat.testBit_two_pow_mul_add _ hk', if_pos hj]
  rw [h1, h2]

end VerifiableInference.Desc.Kinds.Head.Law
