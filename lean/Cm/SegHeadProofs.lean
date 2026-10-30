-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegHeadProofs.lean: lemmas on the vertices of Cm/SegHead.lean, and on sums.
The head of Cm/SegHead.lean tells the vertices in words.

Main names:
  `va_vOf`, `vi_vOf`: for a < 2^vx and i < 2^10 the vertex of (a, i) encodes its index a and
    position i (`vi_vOf`: under the second bound alone). `vi_lt`: `vi b` < `nT`.
  `vOf_va_vi`, `vOf_lt`: a vertex b < 2^(vx + 10) is the vertex of what it encodes; the vertex of
    (a, i), a < 2^vx, i < 2^10, is below 2^(vx + 10). `lenH_le`: `Plain.len f` ≤ 2^(`vxH f`).
  `sum_range_mul`: a sum over m · n numbers as a sum over m of sums over n.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegHead
import Cm.SegIdxModelProofs

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.Head Inst.Model.Layout Finset Cm.Seg.Ex

/-! ## Vertices -/

theorem va_vOf {vx a i : ℕ} (ha : a < 2 ^ vx) (hi : i < 2 ^ 10) : va vx (vOf a i) = a := by
  unfold va vOf
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 10), Nat.div_eq_of_lt hi,
    Nat.zero_add, Nat.mod_eq_of_lt ha]
theorem vi_vOf (a : ℕ) {i : ℕ} (hi : i < 2 ^ 10) : vi (vOf a i) = i := by
  unfold vi vOf
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
theorem vi_lt (b : ℕ) : vi b < nT := Nat.mod_lt _ (by norm_num)
theorem vOf_va_vi {vx b : ℕ} (hb : b < 2 ^ (vx + 10)) : vOf (va vx b) (vi b) = b := by
  unfold vOf va vi
  have h : b / 2 ^ 10 < 2 ^ vx := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact hb
  rw [Nat.mod_eq_of_lt h]
  exact Nat.div_add_mod' b (2 ^ 10)
theorem vOf_lt {vx a i : ℕ} (ha : a < 2 ^ vx) (hi : i < 2 ^ 10) : vOf a i < 2 ^ (vx + 10) := by
  unfold vOf
  rw [pow_add]
  nlinarith [Nat.two_pow_pos 10]

theorem lenH_le (f : Plain.Fam) : Plain.len f ≤ 2 ^ vxH f := by cases f <;> decide

/-- arithmetic on vertices: evaluate the powers of two, then linear arithmetic with division by numerals -/
macro "ar" : tactic => `(tactic| (simp only [vOf, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.reduceMul] at *; omega))

/-! ## Sums -/

theorem sum_range_mul {M : Type} [AddCommMonoid M] (m n : ℕ) (f : ℕ → M) :
    ∑ k ∈ range (m * n), f k = ∑ t ∈ range m, ∑ j ∈ range n, f (t * n + j) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

end Cm.Seg
