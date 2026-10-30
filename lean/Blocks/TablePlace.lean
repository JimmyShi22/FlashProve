-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/TablePlace.lean: the position of a table's cell (r, c) in a vector of several code rows (used
in Blocks/RngCalls.lean, field `tB`, for the table bit, the bits of the multiplicities of all calls
of a lookup plan, Blocks/RngPlan.lean).

Numbers only.

What follows on the implementation is known only from reading the code; no document in this
repository has the rule. The implementation cuts a table of R rows and K columns into code rows as
follows: 2^x table rows share one code row, and a long table row is cut into hB pieces of K2
columns. Cell (r, c) with r = rhi · 2^x + rlo and c = hi · K2 + cm is in code row rhi · hB + hi at
the coordinate cm · 2^x + rlo. A code row has K2 · 2^x data coordinates (`TPl.msg`).
 * `TPl`: the three numbers x, hB, K2.
 * `TPl.line` r c: the position of cell (r, c), as one number: code row · msg + coordinate.
 * `TPl.rowOf_line`, `TPl.colOf_line`: the cell at the position of (r, c) is (r, c), if 0 < K2 and c
   < hB · K2.
 * `TPl.line_lt`: the position is in the first R2 · hB code rows, if 0 < K2, r < R2 · 2^x and c < hB
   · K2.
Limits: nothing on how x, hB, K2 are chosen (the implementation's rule for a shape is not modelled);
nothing on coordinates that receive no cell.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Blocks

/-- the interleaving exponent x; the number hB of pieces of a table row; the number K2 of columns in
a piece -/
structure TPl where
  x : ℕ
  hB : ℕ
  K2 : ℕ

namespace TPl

variable (T : TPl)

/-- the number of data coordinates of a code row -/
def msg : ℕ := T.K2 * 2 ^ T.x

/-- The position of cell (r, c): code row (r / 2^x) · hB + c / K2, coordinate (c mod K2) · 2^x + r
mod 2^x. -/
def line (r c : ℕ) : ℕ :=
  (r / 2 ^ T.x * T.hB + c / T.K2) * T.msg + (c % T.K2 * 2 ^ T.x + r % 2 ^ T.x)

/-- the table row and the column of the cell at the position n -/
def rowOf (n : ℕ) : ℕ := n / T.msg / T.hB * 2 ^ T.x + n % T.msg % 2 ^ T.x
def colOf (n : ℕ) : ℕ := n / T.msg % T.hB * T.K2 + n % T.msg / 2 ^ T.x

variable {T}

theorem coord_lt (hK : 0 < T.K2) (r c : ℕ) : c % T.K2 * 2 ^ T.x + r % 2 ^ T.x < T.msg := by
  have h1 : c % T.K2 < T.K2 := Nat.mod_lt _ hK
  have h2 : r % 2 ^ T.x < 2 ^ T.x := Nat.mod_lt _ (Nat.two_pow_pos _)
  calc c % T.K2 * 2 ^ T.x + r % 2 ^ T.x < c % T.K2 * 2 ^ T.x + 2 ^ T.x := by omega
    _ = (c % T.K2 + 1) * 2 ^ T.x := by ring
    _ ≤ T.K2 * 2 ^ T.x := Nat.mul_le_mul_right _ h1

theorem line_div (hK : 0 < T.K2) (r c : ℕ) :
    T.line r c / T.msg = r / 2 ^ T.x * T.hB + c / T.K2 := by
  have h := coord_lt hK r c
  have hm : 0 < T.msg := lt_of_le_of_lt (Nat.zero_le _) h
  unfold line
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt h, Nat.zero_add]

theorem line_mod (hK : 0 < T.K2) (r c : ℕ) :
    T.line r c % T.msg = c % T.K2 * 2 ^ T.x + r % 2 ^ T.x := by
  have h := coord_lt hK r c
  unfold line
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

/-- Under `hK`, `hc`, the table row of the cell at the position of (r, c) is r. -/
theorem rowOf_line (hK : 0 < T.K2) {c : ℕ} (hc : c < T.hB * T.K2) (r : ℕ) :
    T.rowOf (T.line r c) = r := by
  have hhi : c / T.K2 < T.hB := (Nat.div_lt_iff_lt_mul hK).2 hc
  have hB : 0 < T.hB := lt_of_le_of_lt (Nat.zero_le _) hhi
  have h2 : r % 2 ^ T.x < 2 ^ T.x := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold rowOf
  rw [line_div hK, line_mod hK]
  have e1 : (r / 2 ^ T.x * T.hB + c / T.K2) / T.hB = r / 2 ^ T.x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hhi, Nat.zero_add]
  have e2 : (c % T.K2 * 2 ^ T.x + r % 2 ^ T.x) % 2 ^ T.x = r % 2 ^ T.x := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  rw [e1, e2]
  exact Nat.div_add_mod' r (2 ^ T.x)

theorem colOf_line (hK : 0 < T.K2) {c : ℕ} (hc : c < T.hB * T.K2) (r : ℕ) :
    T.colOf (T.line r c) = c := by
  have hhi : c / T.K2 < T.hB := (Nat.div_lt_iff_lt_mul hK).2 hc
  have h2 : r % 2 ^ T.x < 2 ^ T.x := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold colOf
  rw [line_div hK, line_mod hK]
  have e1 : (r / 2 ^ T.x * T.hB + c / T.K2) % T.hB = c / T.K2 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hhi]
  have e2 : (c % T.K2 * 2 ^ T.x + r % 2 ^ T.x) / 2 ^ T.x = c % T.K2 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt h2, Nat.zero_add]
  rw [e1, e2]
  exact Nat.div_add_mod' c T.K2

/-- Under `hK`, `hr`, `hc`, the position is in the first R2 · hB code rows. -/
theorem line_lt (hK : 0 < T.K2) {R2 r c : ℕ} (hr : r < R2 * 2 ^ T.x) (hc : c < T.hB * T.K2) :
    T.line r c < R2 * T.hB * T.msg := by
  have hhi : c / T.K2 < T.hB := (Nat.div_lt_iff_lt_mul hK).2 hc
  have hrh : r / 2 ^ T.x < R2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 hr
  have h := coord_lt hK r c
  have h1 : r / 2 ^ T.x * T.hB + c / T.K2 + 1 ≤ R2 * T.hB :=
    calc r / 2 ^ T.x * T.hB + c / T.K2 + 1 ≤ r / 2 ^ T.x * T.hB + T.hB := by omega
      _ = (r / 2 ^ T.x + 1) * T.hB := by ring
      _ ≤ R2 * T.hB := Nat.mul_le_mul_right _ hrh
  calc T.line r c < (r / 2 ^ T.x * T.hB + c / T.K2) * T.msg + T.msg := by unfold line; omega
    _ = (r / 2 ^ T.x * T.hB + c / T.K2 + 1) * T.msg := by ring
    _ ≤ R2 * T.hB * T.msg := Nat.mul_le_mul_right _ h1

end TPl

end Blocks
