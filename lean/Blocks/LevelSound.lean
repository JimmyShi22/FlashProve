-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LevelSound.lean: lemmas on the levels (Blocks/LevelDef.lean): `endVal_congr` and the bilinear
count `cnt_bilinear`, with `sum_two_parts`, `lin_part`. (T-end) is the final equation of a level's
sumcheck (`LevSpec.endVal`). (Words of this library: lean/GLOSSARY.md.)
-/
import Blocks.LowerKit
import Alg.SumCheck
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Blocks
namespace LevelSound

open Iop Prob Finset

variable {F : Type} [Field F] {E : Type} [Field E]

/-! ## 1. The end of a sumcheck -/

section Alg1
variable [Algebra F E] (a : LevSpec F)

omit [Field F] [Algebra F E] in
/-- `endVal` depends on a candidate only through its entries below msg -/
theorem endVal_congr (c : a.Claim E) (ζ : ℕ → E) {u u' : ℕ → E} (h : ∀ j < a.code.msg, u j = u' j) :
    a.endVal c ζ u = a.endVal c ζ u' := by
  unfold LevSpec.endVal
  congr 1
  exact sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

end Alg1

/-! ## 2. Counts and sums for the claim of the next level -/

section Next
variable [Fintype E]

/-- The bilinear count for χ0, χ1, χ': if u0 or one of the x i, y i is not zero, at most 2 |E|^(q+1)
values of (χ0, χ1, χ') make u0 + ∑ i, χ' i * (χ0 * x i + χ1 * y i) zero. -/
theorem cnt_bilinear (q : ℕ) (u0 : E) (x y : Fin q → E) (h : u0 ≠ 0 ∨ ∃ i, x i ≠ 0 ∨ y i ≠ 0) :
    cnt (fun ch : E × E × (Fin q → E) => u0 + ∑ i, ch.2.2 i * (ch.1 * x i + ch.2.1 * y i) = 0) ≤
      2 * Fintype.card E ^ (q + 1) := by
  classical
  have h1 := Alg.count_bilinear_mul_le (K := E) (J := Fin 2) (I := Fin q) u0 (fun i => ![x i, y i]) (by
    rcases h with h | ⟨i, hi⟩
    · exact Or.inl h
    · refine Or.inr fun h0 => ?_
      have h2 := congrFun h0 i
      rcases hi with hi | hi
      · exact hi (by simpa using congrFun h2 0)
      · exact hi (by simpa using congrFun h2 1))
  let e : (Fin 2 → E) × (Fin q → E) ≃ E × E × (Fin q → E) :=
    ((finTwoArrowEquiv E).prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc E E _)
  have h2 := cnt_equiv e
    (fun ch : E × E × (Fin q → E) => u0 + ∑ i, ch.2.2 i * (ch.1 * x i + ch.2.1 * y i) = 0)
  rw [← h2]
  have h3 : cnt (fun p : (Fin 2 → E) × (Fin q → E) =>
        u0 + ∑ i, (e p).2.2 i * ((e p).1 * x i + (e p).2.1 * y i) = 0) =
      Nat.card {p : (Fin 2 → E) × (Fin q → E) //
          u0 + ∑ i, p.2 i * ∑ j, p.1 j * (![x i, y i] : Fin 2 → E) j = 0} := by
    refine cnt_congr fun p => ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl
  rw [h3]
  have h4 : Fintype.card ((Fin 2 → E) × (Fin q → E)) =
      Fintype.card E ^ (q + 1) * Fintype.card E := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    ring
  rw [h4, ← mul_assoc] at h1
  exact Nat.le_of_mul_le_mul_right h1 Fintype.card_pos

omit [Fintype E] in
theorem sum_two_parts (m N : ℕ) (h : 2 * m ≤ N) (g : ℕ → E) (hg : ∀ t, 2 * m ≤ t → g t = 0) :
    ∑ t ∈ range N, g t = ∑ t ∈ range m, g t + ∑ t ∈ range m, g (m + t) := by
  rw [← sum_subset (range_subset_range.mpr h) fun t _ ht =>
        hg t (Nat.le_of_not_lt fun hl => ht (mem_range.mpr hl)),
    two_mul, sum_range_add]

omit [Fintype E] in
theorem lin_part {q : ℕ} (m : ℕ) (G : Fin q → ℕ → E) (χ' : Fin q → E) (χ : E) (B : ℕ → E) :
    ∑ t ∈ range m, (∑ i, χ' i * (χ * G i t)) * B t =
      ∑ i, χ' i * (χ * ∑ t ∈ range m, G i t * B t) := by
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun t _ => by ring

end Next

end LevelSound

end Blocks
