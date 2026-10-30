-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Digits/PortCols.lean: the digit of row i of cells of matrix mu, at combination
u, as a place of the lookup on the digits.

The smallness test's equations name a digit by (matrix, row of cells, combination). The verifier's
`HTailF2.zzCol` gives its column in the array ZZ. The lookup on the digits numbers a digit's place
by (column of the low half, combination) (`Pl tl`, PortDat.lean). Here the first is carried to the
second.

Main names:
  `colsTest tl`: a Bool on the shape: the matrices' first rows follow one another from 0 on, and the
    last matrix ends at mz.
  `dgP_col_le`, `dgP_col_lt`: under the test off_mu + m_mu ≤ mz; so off_mu + i < mz for i < m_mu.
  `ixP`: the place of the digit (mu, i, u).
  `dgP_ix_lo`, `dgP_ix_hi`: the entries of `portQ tl` at that place are ZZ's entries in row u and in
    the columns that `zzCol` gives for plane 0 and for plane 1.
Limits: that the test follows from the success of the verifier's own routines is not shown. Nothing
says here that every place is the place of some (mu, i, u).

-/
import OnBytes.Tie.Pv.Lookup.Digits.PortDat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.DgP
open OnBytes OnBytes.Model CbQ

/-- The rows of cells of matrix mu; its first row among all. -/
def mOf (tl : HTailF2) (mu : ℕ) : ℕ := (tl.mats.getD mu {}).m
def offOf (tl : HTailF2) (mu : ℕ) : ℕ := tl.off.getD mu 0

/-- The matrices' first rows follow one another from 0 on, and the last matrix ends at mz. -/
def colsTest (tl : HTailF2) : Bool :=
  decide (∀ mu < tl.NM,
    offOf tl mu + mOf tl mu = if mu + 1 < tl.NM then offOf tl (mu + 1) else tl.mz) &&
  decide (offOf tl 0 = 0)

variable {tl : HTailF2}

/-- A matrix ends at or before mz. -/
theorem dgP_col_le (h : colsTest tl = true) :
    ∀ k mu, mu + k + 1 = tl.NM → offOf tl mu + mOf tl mu ≤ tl.mz := by
  have h' := of_decide_eq_true (Bool.and_eq_true _ _ ▸ h).1
  intro k
  induction k with
  | zero =>
    intro mu e
    have e1 := h' mu (by omega)
    rw [if_neg (by omega)] at e1
    omega
  | succ k ih =>
    intro mu e
    have e1 := h' mu (by omega)
    rw [if_pos (by omega)] at e1
    have e2 := ih (mu + 1) (by omega)
    omega

/-- A row of cells of a matrix is a column of ZZ's low half. -/
theorem dgP_col_lt (h : colsTest tl = true) {mu i : ℕ} (hmu : mu < tl.NM) (hi : i < mOf tl mu) :
    offOf tl mu + i < tl.mz := by
  have e := dgP_col_le h (tl.NM - mu - 1) mu (by omega)
  omega

/-- The place of the digit of row i of cells of matrix mu at combination u. -/
def ixP (h : colsTest tl = true) (mu i u : ℕ) (hmu : mu < tl.NM) (hi : i < mOf tl mu)
    (hu : u < tl.tau) : Pl tl :=
  (⟨offOf tl mu + i, dgP_col_lt h hmu hi⟩, ⟨u, hu⟩)

/-- The low digit's entry at that place is ZZ's entry in the column that the verifier gives. -/
theorem dgP_ix_lo (h : colsTest tl = true) {mu i u : ℕ} (hmu : mu < tl.NM) (hi : i < mOf tl mu)
    (hu : u < tl.tau) :
    tl.zzCol mu 0 i = some ((portQ tl).lo (ixP h mu i u hmu hi hu)).2.2 ∧
      ((portQ tl).lo (ixP h mu i u hmu hi hu)).1 = tl.ix.ZZ ∧
      ((portQ tl).lo (ixP h mu i u hmu hi hu)).2.1 = u := by
  refine ⟨?_, rfl, rfl⟩
  have hi' : i < (tl.mats.getD mu {}).m := hi
  unfold HTailF2.zzCol
  simp only [hmu, hi', decide_true, Bool.and_self, if_true, Nat.zero_le, Nat.zero_mul, Nat.zero_add]
  rfl

/-- The same for the high digit. -/
theorem dgP_ix_hi (h : colsTest tl = true) {mu i u : ℕ} (hmu : mu < tl.NM) (hi : i < mOf tl mu)
    (hu : u < tl.tau) :
    tl.zzCol mu 1 i = some ((portQ tl).hi (ixP h mu i u hmu hi hu)).2.2 ∧
      ((portQ tl).hi (ixP h mu i u hmu hi hu)).1 = tl.ix.ZZ ∧
      ((portQ tl).hi (ixP h mu i u hmu hi hu)).2.1 = u := by
  refine ⟨?_, rfl, rfl⟩
  have hi' : i < (tl.mats.getD mu {}).m := hi
  unfold HTailF2.zzCol
  simp only [hmu, hi', decide_true, Bool.and_self, if_true, Nat.le_refl, Nat.one_mul]
  show some (tl.mz + tl.off.getD mu 0 + i) = some (tl.mz + (offOf tl mu + i))
  rw [Nat.add_assoc]
  rfl

#print axioms dgP_col_lt
#print axioms dgP_ix_lo
#print axioms dgP_ix_hi

end OnBytes.DgP
