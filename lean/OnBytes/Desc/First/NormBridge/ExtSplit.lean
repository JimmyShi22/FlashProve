-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/NormBridge/ExtSplit.lean: Small algebra on the library's multilinear extension
(Blocks/Ext.lean), over a field; no text of a verifier. Statements and proofs.

  eqN_shift: the equality weight from an offset on is that of the shifted point.
  ext_split: an extension over k1 + k2 coordinates, evaluated in two steps: the index is
    i 2^k2 + c, the top k1 bits first.
  eqN_const: at coordinates that are all h, with 1 - h = h, every index has the weight h^n.
  sum_range_trunc: a sum whose terms vanish from N on.
  list_sum_range: a list's sum over List.range as a sum over Finset.range.
  div_of_lt, mod_of_lt: (i B + c) / B = i and (i B + c) % B = c for c < B.

LIBRARY LEMMAS TAKEN: Blocks/EqN.lean eqN_append'; Alg/Mle.lean sum_range_mul_add. The road is that
of
Cb/Pv/Head/SquaresSum.lean (eqN_half, sq_sum), which goes through tuples.
-/
import Blocks.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Bridge
open Finset
open Blocks (ext eqN)

variable {K : Type} [Field K]

theorem eqN_shift (m k : ℕ) (a : ℕ → K) (z : ℕ) :
    eqN m k a z = eqN m 0 (fun t => a (k + t)) z := by
  simp only [Blocks.eqN, Nat.zero_add]

/-- An extension over k1 + k2 coordinates in two steps. -/
theorem ext_split (k1 k2 : ℕ) (V : ℕ → K) (a : ℕ → K) :
    ext (k1 + k2) V a =
      ∑ i ∈ range (2 ^ k1),
        eqN k1 0 a i * ext k2 (fun c => V (i * 2 ^ k2 + c)) (fun t => a (k1 + t)) := by
  unfold Blocks.ext
  rw [pow_add, Alg.sum_range_mul_add]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c hc => ?_
  rw [Blocks.eqN_append' k1 k2 0 a i (mem_range.mp hc), Nat.zero_add, eqN_shift k2 k1 a c,
    mul_assoc]

/-- A sum under equality weights over k1 + k2 coordinates in two steps. -/
theorem sum_eqN_split (k1 k2 : ℕ) (F : ℕ → K) (a : ℕ → K) :
    ∑ X ∈ range (2 ^ (k1 + k2)), eqN (k1 + k2) 0 a X * F X =
      ∑ i ∈ range (2 ^ k1), eqN k1 0 a i *
        ∑ c ∈ range (2 ^ k2), eqN k2 k1 a c * F (i * 2 ^ k2 + c) := by
  rw [pow_add, Alg.sum_range_mul_add]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c hc => ?_
  rw [Blocks.eqN_append' k1 k2 0 a i (mem_range.mp hc), Nat.zero_add, mul_assoc]

/-- At coordinates that are all h, with 1 - h = h, every index has the weight h^n. -/
theorem eqN_const (n off : ℕ) (a : ℕ → K) (h : K) (hh : 1 - h = h)
    (ha : ∀ t < n, a (off + t) = h) (z : ℕ) : eqN n off a z = h ^ n := by
  unfold Blocks.eqN
  have e : ∀ t ∈ range n,
      (if z.testBit (n - 1 - t) then a (off + t) else 1 - a (off + t)) = h := by
    intro t ht
    rw [ha t (mem_range.mp ht), hh]
    simp
  rw [prod_congr rfl e, prod_const, card_range]

theorem sum_range_trunc {N N' : ℕ} (h : N ≤ N') (f : ℕ → K) (hf : ∀ i, N ≤ i → f i = 0) :
    ∑ i ∈ range N', f i = ∑ i ∈ range N, f i :=
  (sum_subset (range_subset_range.mpr h) fun i _ hi => hf i (by simpa using hi)).symm

theorem list_sum_range (n : ℕ) (f : ℕ → K) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]
    simp

theorem div_of_lt (i : ℕ) {B c : ℕ} (hc : c < B) : (i * B + c) / B = i := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hc
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hc, Nat.zero_add]

theorem mod_of_lt (i : ℕ) {B c : ℕ} (hc : c < B) : (i * B + c) % B = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

end D6.Bridge
