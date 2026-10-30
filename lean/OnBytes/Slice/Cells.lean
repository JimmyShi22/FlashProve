-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Cells.lean: an index into a table with 2^k rows, as a vertex with a place, and back.

The format keeps a table of 2^k rows and l places as one array: the entry in the row with the number
r at the place j has the index r + 2^k * j. The library names a row by k binary digits, a vertex.
`Sz.rowNo` (OnBytes/Slice/LinkAt.lean) gives a vertex its number, the lowest digit first.
This file shows that numbers below 2^k and vertices are the same thing, and that indices below
2^k * l and pairs of a vertex with a place are the same thing.

Main definitions.
 `cell k l i h`   the vertex and the place of the entry with the index i.
 `idxOf x`        the index of the entry at a vertex and a place.
Main theorems.
 `rowNo_lt`       the number of a vertex is below 2^k.
 `testBit_rowNo`  the bits of that number are the vertex's digits.
 `rowNo_testBit`  the vertex of the k lowest bits of i has the number i modulo 2^k.
 `sum_rowNo`      summing over all vertices b is summing over all i < 2^k, where i is b's number.
 `eqk_rowNo`      the equality weight of a vertex, from the bits of its number.
 `idxOf_lt`, `idxOf_cell`, `cell_idxOf`, `idxOf_inj`   the two maps are inverse to each other.

Not claimed. Nothing on what a table holds.
-/
import OnBytes.Slice.LinkAt
import OnBytes.Slice.Corners

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## The number of a vertex -/

/-- With one more digit: the number of the k lowest digits, and 2^k more if the top digit is set. -/
theorem rowNo_succ {k : ℕ} (b : Fin (k + 1) → Bool) :
    Sz.rowNo b = Sz.rowNo (fun t : Fin k => b t.castSucc) +
      (if b (Fin.last k) = true then 2 ^ k else 0) := by
  unfold Sz.rowNo
  rw [Fin.sum_univ_castSucc]
  rfl

/-- The number of a vertex with k digits is below 2^k. -/
theorem rowNo_lt {k : ℕ} (b : Fin k → Bool) : Sz.rowNo b < 2 ^ k := by
  induction k with
  | zero =>
    unfold Sz.rowNo
    rw [Fin.sum_univ_zero]
    exact Nat.two_pow_pos 0
  | succ k ih =>
    have h1 : Sz.rowNo (fun t : Fin k => b t.castSucc) < 2 ^ k := ih _
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, Nat.mul_two]
    rw [rowNo_succ, h2]
    by_cases hb : b (Fin.last k) = true
    · rw [if_pos hb]
      omega
    · rw [if_neg hb]
      omega

/-- The bits of the number of a vertex are the vertex's digits. -/
theorem testBit_rowNo {k : ℕ} (b : Fin k → Bool) (t : Fin k) :
    (Sz.rowNo b).testBit t.val = b t := by
  induction k with
  | zero => exact t.elim0
  | succ k ih =>
    have h1 : Sz.rowNo (fun s : Fin k => b s.castSucc) < 2 ^ k := rowNo_lt _
    rw [rowNo_succ]
    by_cases hb : b (Fin.last k) = true
    · rw [if_pos hb, Nat.add_comm]
      induction t using Fin.lastCases with
      | last =>
        show (2 ^ k + Sz.rowNo (fun s : Fin k => b s.castSucc)).testBit k = b (Fin.last k)
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h1, hb, Bool.not_false]
      | cast s =>
        show (2 ^ k + Sz.rowNo (fun s : Fin k => b s.castSucc)).testBit s.val = b s.castSucc
        rw [Nat.testBit_two_pow_add_gt s.isLt]
        exact ih _ s
    · rw [if_neg hb, Nat.add_zero]
      induction t using Fin.lastCases with
      | last =>
        show (Sz.rowNo (fun s : Fin k => b s.castSucc)).testBit k = b (Fin.last k)
        rw [Nat.testBit_lt_two_pow h1, eq_false_of_ne_true hb]
      | cast s => exact ih _ s

/-- Different vertices have different numbers. -/
theorem rowNo_inj {k : ℕ} : Function.Injective (Sz.rowNo (v := k)) := by
  intro b b' h
  funext t
  rw [← testBit_rowNo b t, h, testBit_rowNo]

/-- The vertex of the k lowest bits of i has the number i modulo 2^k. -/
theorem rowNo_testBit (k i : ℕ) : Sz.rowNo (fun t : Fin k => i.testBit t.val) = i % 2 ^ k := by
  refine testBit_inj k (rowNo_lt _) (Nat.mod_lt _ (Nat.two_pow_pos k)) fun t => ?_
  rw [testBit_rowNo, Nat.testBit_mod_two_pow, decide_eq_true t.isLt, Bool.true_and]

/-- Summing F at the number of b over all vertices b is summing F at i over all i < 2^k. -/
theorem sum_rowNo {M : Type} [AddCommMonoid M] (k : ℕ) (F : ℕ → M) :
    ∑ b : Fin k → Bool, F (Sz.rowNo b) = ∑ i ∈ Finset.range (2 ^ k), F i := by
  refine Finset.sum_bij (fun b _ => Sz.rowNo b) (fun b _ => Finset.mem_range.2 (rowNo_lt b))
    (fun b _ b' _ h => rowNo_inj h)
    (fun i hi => ⟨fun t : Fin k => i.testBit t.val, Finset.mem_univ _, ?_⟩) (fun _ _ => rfl)
  show Sz.rowNo (fun t : Fin k => i.testBit t.val) = i
  rw [rowNo_testBit, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]

/-- The equality weight of a vertex, written with the bits of the vertex's number. -/
theorem eqk_rowNo {K : Type} [Field K] (k : ℕ) (γ : Fin k → K) (b : Fin k → Bool) :
    Alg.eqk γ b = Alg.eqk γ (fun t : Fin k => (Sz.rowNo b).testBit t.val) := by
  have h : (fun t : Fin k => (Sz.rowNo b).testBit t.val) = b := funext (testBit_rowNo b)
  rw [h]

/-! ## Indices and entries -/

/-- The entry with the index i of a table of 2^k rows and l places. -/
def cell (k l i : ℕ) (h : i < 2 ^ k * l) : (Fin k → Bool) × Fin l :=
  (fun t => i.testBit t.val, ⟨i / 2 ^ k, Nat.div_lt_of_lt_mul h⟩)

/-- The index of an entry. -/
def idxOf {k l : ℕ} (x : (Fin k → Bool) × Fin l) : ℕ := Sz.rowNo x.1 + 2 ^ k * x.2.val

/-- The index of an entry is below the number of entries. -/
theorem idxOf_lt {k l : ℕ} (x : (Fin k → Bool) × Fin l) : idxOf x < 2 ^ k * l := by
  have h1 : Sz.rowNo x.1 < 2 ^ k := rowNo_lt x.1
  have h2 : 2 ^ k * (x.2.val + 1) ≤ 2 ^ k * l := Nat.mul_le_mul_left _ x.2.isLt
  rw [Nat.mul_add_one] at h2
  unfold idxOf
  omega

/-- The entry with the index i has the index i. -/
theorem idxOf_cell (k l i : ℕ) (h : i < 2 ^ k * l) : idxOf (cell k l i h) = i := by
  show Sz.rowNo (fun t : Fin k => i.testBit t.val) + 2 ^ k * (i / 2 ^ k) = i
  rw [rowNo_testBit]
  exact Nat.mod_add_div i (2 ^ k)

/-- Different entries have different indices. -/
theorem idxOf_inj {k l : ℕ} : Function.Injective (idxOf (k := k) (l := l)) := by
  intro x y h
  have h1 : Sz.rowNo x.1 = Sz.rowNo y.1 ∧ x.2.val = y.2.val :=
    idx_inj k (rowNo_lt x.1) (rowNo_lt y.1) h
  exact Prod.ext (rowNo_inj h1.1) (Fin.ext h1.2)

/-- The entry with the index of x is x. -/
theorem cell_idxOf {k l : ℕ} (x : (Fin k → Bool) × Fin l) :
    cell k l (idxOf x) (idxOf_lt x) = x :=
  idxOf_inj (idxOf_cell k l (idxOf x) (idxOf_lt x))

end OnBytes.Slice

#print axioms OnBytes.Slice.rowNo_lt
#print axioms OnBytes.Slice.testBit_rowNo
#print axioms OnBytes.Slice.rowNo_testBit
#print axioms OnBytes.Slice.sum_rowNo
#print axioms OnBytes.Slice.eqk_rowNo
#print axioms OnBytes.Slice.idxOf_lt
#print axioms OnBytes.Slice.idxOf_cell
#print axioms OnBytes.Slice.cell_idxOf
#print axioms OnBytes.Slice.idxOf_inj
