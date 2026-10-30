-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/EqN.lean: the equality polynomial eq for points indexed by ℕ, and vectors cut into rows.

The protocols (Blocks/Basic.lean: `eqN`) write a point as a function on ℕ and take m coordinates of
it from an offset on. The algebra (Alg/Mle.lean: `Alg.eqN`) writes a point as a tuple. This file
relates the two, so that the facts of Alg/Mle.lean can be used for the definitions of the protocols.
-/
import Blocks.Basic
import Alg.Mle
import Prob.Cnt

set_option autoImplicit false

namespace Blocks

open Finset Prob

variable {E : Type} [Field E]

/-- `eqN` of Blocks/Basic.lean is `Alg.eqN` of Alg/Mle.lean at the tuple of the m coordinates from
`off` on. -/
theorem eqN_eq (m off : ℕ) (a : ℕ → E) (z : ℕ) :
    eqN m off a z = Alg.eqN (fun t : Fin m => a (off + t)) z := by
  unfold eqN Alg.eqN Alg.eqk Alg.bits
  exact (Fin.prod_univ_eq_prod_range
    (fun t => if z.testBit (m - 1 - t) then a (off + t) else 1 - a (off + t)) m).symm

/-- `eqN_eq` for a tuple extended by 0 to ℕ (`nat`). -/
theorem eqN_nat (m : ℕ) (v : Fin m → E) (z : ℕ) : eqN m 0 (nat v) z = Alg.eqN v z := by
  rw [eqN_eq]
  congr 1
  funext t
  simp [nat, t.2]

/-- eq((a, a'), 2^m' z + z') = eq(a, z) eq(a', z') for z' < 2^m', from any offset on. -/
theorem eqN_append (m m' off : ℕ) (a : ℕ → E) (z : ℕ) {z' : ℕ} (hz' : z' < 2 ^ m') :
    eqN (m + m') off a (2 ^ m' * z + z') = eqN m off a z * eqN m' (off + m) a z' := by
  rw [eqN_eq, eqN_eq, eqN_eq, ← Alg.eqN_append _ _ z hz']
  congr 1
  funext t
  refine Fin.addCases (fun t => ?_) (fun t => ?_) t
  · simp [Fin.append_left]
  · simp [Fin.append_right, Nat.add_assoc]

/-- `eqN_append` with the index written z · 2^m' + z'. -/
theorem eqN_append' (m m' off : ℕ) (a : ℕ → E) (z : ℕ) {z' : ℕ} (hz' : z' < 2 ^ m') :
    eqN (m + m') off a (z * 2 ^ m' + z') = eqN m off a z * eqN m' (off + m) a z' := by
  rw [Nat.mul_comm, eqN_append m m' off a z hz']

/-- `eqN_append` at offset 0. -/
theorem eqN_split (k1 k2 : ℕ) (a : ℕ → E) (i : ℕ) {c : ℕ} (hc : c < 2 ^ k2) :
    eqN (k1 + k2) 0 a (2 ^ k2 * i + c) = eqN k1 0 a i * eqN k2 k1 a c := by
  rw [eqN_append k1 k2 0 a i hc, Nat.zero_add]

/-- Multilinear identity, for a vector of length N ≤ 2^m: if d is not zero on [N], then ∑_(y < N)
eq(a, y) d[y] = 0 for at most m |E|^(m - 1) of the |E|^m points a. -/
theorem cnt_eqN_zero_le [Fintype E] (m N : ℕ) (hN : N ≤ 2 ^ m) (d : ℕ → E) (hd : ∃ y < N, d y ≠ 0) :
    cnt (fun v : Fin m → E => ∑ y ∈ range N, eqN m 0 (nat v) y * d y = 0) ≤
      m * Fintype.card E ^ (m - 1) := by
  let d' : Fin (2 ^ m) → E := fun y => if y.val < N then d y else 0
  have hd' : d' ≠ 0 := by
    obtain ⟨y, hy, hdy⟩ := hd
    intro h0
    have := congrFun h0 ⟨y, lt_of_lt_of_le hy hN⟩
    simp only [d', hy, if_true, Pi.zero_apply] at this
    exact hdy this
  have hsum : ∀ v : Fin m → E,
      ∑ i : Fin (2 ^ m), Alg.eqN v i * d' i = ∑ y ∈ range N, eqN m 0 (nat v) y * d y := by
    intro v
    rw [Fin.sum_univ_eq_sum_range (fun y => Alg.eqN v y * (if y < N then d y else 0)) (2 ^ m)]
    rw [← sum_subset (range_subset_range.mpr hN)]
    · exact sum_congr rfl fun y hy => by rw [if_pos (mem_range.mp hy), eqN_nat]
    · intro y _ hy
      rw [if_neg (fun h => hy (mem_range.mpr h)), mul_zero]
  have h := Alg.count_eqN_zero_le d' hd'
  simp only [hsum] at h
  exact h

/-! ### Vectors that are cut into rows -/

/-- A sum up to N' ≥ N whose terms from N on vanish. -/
theorem sum_range_ite_lt {N N' : ℕ} (h : N ≤ N') (f g : ℕ → E) :
    ∑ t ∈ range N', (if t < N then f t else 0) * g t = ∑ t ∈ range N, f t * g t := by
  rw [← sum_subset (range_subset_range.mpr h)]
  · exact sum_congr rfl fun t ht => by rw [if_pos (mem_range.mp ht)]
  · intro t _ ht
    rw [if_neg (fun h' => ht (mem_range.mpr h')), zero_mul]

/-- A sum against a tuple of length k ≤ N that is extended to a function on ℕ. -/
theorem sum_range_nat_mul {k N : ℕ} (h : k ≤ N) (a : Fin k → E) (g : ℕ → E) :
    ∑ t ∈ range N, nat a t * g t = ∑ t : Fin k, a t * g t.val := by
  rw [← sum_subset (range_subset_range.mpr h)]
  · rw [← Fin.sum_univ_eq_sum_range (fun t => nat a t * g t) k]
    exact sum_congr rfl fun t _ => by simp [nat, t.2]
  · intro t _ ht
    have : ¬ t < k := fun h' => ht (mem_range.mpr h')
    simp [nat, this]

end Blocks
