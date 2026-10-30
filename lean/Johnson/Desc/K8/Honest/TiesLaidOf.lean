-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TiesLaidOf.lean: THE SMALLNESS TEST: THE TEST ON PUBLIC NUMBERS `tiesLaid`
(Johnson/Desc/K8/Honest/LinkedFew.lean), WHICH RUNS OVER ALL mz COLUMNS, FROM THREE LIGHT ONES: THE
ARRAYS' NUMBERS ARE APART (`apartB`, ApartOf.lean); THE MATRICES' COLUMNS LIE ONE BEHIND THE OTHER
(DgP.colsTest, OnBytes/Tie/Pv/Lookup/Digits/PortCols.lean); THE SIZES FIT. Statements and proofs. On
plain data: no block, no prover. Lemmas; none of the library's goals.

tl: the smallness test's data. off mu, m mu: a matrix's first column among ZZ's and its number of
rows of cells.
  `ColsFacts tl`   what the lemmas spend, by name: colsTest's two clauses; each matrix has a row of
      cells; without a matrix there is no column
  `cols_le`   an earlier matrix ends at or before a later one's first column
  `cols_end`   each matrix ends at or before mz
  `cols_cover`   each column below mz lies in one matrix's stretch
  **`tiesLaid_of`**   `apartB tl`, `ColsFacts tl`, and each shape has its matrix's number of rows of
      cells: then `tiesLaid tl` says yes
Limits. The three are premises here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.ApartOf
import Johnson.Desc.K8.Honest.LinkedFew
import OnBytes.Tie.Pv.Lookup.Digits.PortCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

/-- What the lemmas spend. -/
structure ColsFacts (tl : HTailF2) : Prop where
  next : ∀ mu, mu < tl.NM → tl.off.getD mu 0 + (tl.mats.getD mu {}).m =
    if mu + 1 < tl.NM then tl.off.getD (mu + 1) 0 else tl.mz
  first : tl.off.getD 0 0 = 0
  pos : ∀ mu, mu < tl.NM → 0 < (tl.mats.getD mu {}).m
  empty : tl.NM = 0 → tl.mz = 0

theorem colsFacts_of (tl : HTailF2) (h : DgP.colsTest tl = true)
    (hp : ∀ mu, mu < tl.NM → 0 < (tl.mats.getD mu {}).m) (h0 : tl.NM = 0 → tl.mz = 0) :
    ColsFacts tl := by
  unfold DgP.colsTest at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact ⟨h.1, h.2, hp, h0⟩

/-- An earlier matrix ends at or before a later one's first column. -/
theorem cols_le {tl : HTailF2} (C : ColsFacts tl) : ∀ d nu, nu + d + 1 < tl.NM →
    tl.off.getD nu 0 + (tl.mats.getD nu {}).m ≤ tl.off.getD (nu + d + 1) 0
  | 0, nu, h => by
    have e := C.next nu (by omega)
    rw [if_pos h] at e
    exact Nat.le_of_eq e
  | d + 1, nu, h => by
    have ih := cols_le C d nu (by omega)
    have e := C.next (nu + d + 1) (by omega)
    rw [if_pos (by omega)] at e
    have e' : tl.off.getD (nu + (d + 1) + 1) 0 = tl.off.getD (nu + d + 1 + 1) 0 := rfl
    omega

/-- Each matrix ends at or before mz. -/
theorem cols_end {tl : HTailF2} (C : ColsFacts tl) {mu : Nat} (h : mu < tl.NM) :
    tl.off.getD mu 0 + (tl.mats.getD mu {}).m ≤ tl.mz := by
  by_cases hl : mu + 1 < tl.NM
  · have h1 := cols_le C (tl.NM - mu - 2) mu (by omega)
    have e := C.next (tl.NM - 1) (by omega)
    rw [if_neg (by omega)] at e
    have e2 : mu + (tl.NM - mu - 2) + 1 = tl.NM - 1 := by omega
    rw [e2] at h1
    omega
  · have e := C.next mu h
    rw [if_neg hl] at e
    exact Nat.le_of_eq e

/-- Below the first column of matrix number k, or below mz at k = NM, each column lies in the
stretch of a matrix below k. -/
theorem cols_cover_to {tl : HTailF2} (C : ColsFacts tl) : ∀ k, k ≤ tl.NM → ∀ x,
    x < (if k < tl.NM then tl.off.getD k 0 else tl.mz) →
    ∃ mu, mu < k ∧ tl.off.getD mu 0 ≤ x ∧ x < tl.off.getD mu 0 + (tl.mats.getD mu {}).m
  | 0, _, x, hx => by
    by_cases h0 : 0 < tl.NM
    · rw [if_pos h0, C.first] at hx
      exact absurd hx (Nat.not_lt_zero x)
    · rw [if_neg h0, C.empty (by omega)] at hx
      exact absurd hx (Nat.not_lt_zero x)
  | k + 1, hk, x, hx => by
    have e := C.next k (by omega)
    rw [← e] at hx
    by_cases hlt : x < tl.off.getD k 0
    · obtain ⟨mu, h1, h2⟩ := cols_cover_to C k (by omega) x (by rw [if_pos (by omega)]; exact hlt)
      exact ⟨mu, by omega, h2⟩
    · exact ⟨k, by omega, by omega, hx⟩

/-- Each column below mz lies in one matrix's stretch. -/
theorem cols_cover {tl : HTailF2} (C : ColsFacts tl) {x : Nat} (hx : x < tl.mz) :
    ∃ mu, mu < tl.NM ∧ tl.off.getD mu 0 ≤ x ∧ x < tl.off.getD mu 0 + (tl.mats.getD mu {}).m :=
  cols_cover_to C tl.NM (Nat.le_refl _) x (by rw [if_neg (Nat.lt_irrefl _)]; exact hx)

/-- **The three light tests give `tiesLaid`.** -/
theorem tiesLaid_of (tl : HTailF2) (hA : apartB tl = true) (C : ColsFacts tl)
    (hF : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).m = (tl.mats.getD mu {}).m) :
    tiesLaid tl = true := by
  obtain ⟨-, ⟨a0, -⟩, ⟨a2, -⟩, a4⟩ := (apartB_iff tl).1 hA
  unfold tiesLaid
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.any_eq_true, List.mem_range]
  refine ⟨⟨⟨a0, a2⟩, fun mu hmu => ⟨⟨⟨⟨(a4 mu hmu).2.1, hF mu hmu⟩, C.pos mu hmu⟩,
    cols_end C hmu⟩, fun nu hnu => ?_⟩⟩, fun x hx => ?_⟩
  · rcases Nat.lt_trichotomy nu mu with h | h | h
    · have := cols_le C (mu - nu - 1) nu (by omega)
      have e : nu + (mu - nu - 1) + 1 = mu := by omega
      rw [e] at this
      exact Or.inl (Or.inr this)
    · exact Or.inl (Or.inl h)
    · have := cols_le C (nu - mu - 1) mu (by omega)
      have e : mu + (nu - mu - 1) + 1 = nu := by omega
      rw [e] at this
      exact Or.inr this
  · obtain ⟨mu, h1, h2, h3⟩ := cols_cover C hx
    exact ⟨mu, h1, h2, h3⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.cols_le
#print axioms VerifiableInference.Desc.First.K8.Honest.cols_end
#print axioms VerifiableInference.Desc.First.K8.Honest.cols_cover
#print axioms VerifiableInference.Desc.First.K8.Honest.tiesLaid_of
