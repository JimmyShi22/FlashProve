-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/RowSumTie.lean: a row applied to words, written without the test whether a table
is there.

value (Johnson/Desc/Means/Says.lean) sums over a table's entries if the statement has the table, and
over nothing if it has not. Another way to write a row applied to tables sums, for each of the first
N oracle messages and both parts, over 2^(row bits + place bits) entries, whether the table is there
or not. This file shows that the two are the same for a row that has no coefficient on a table that
is not there, at N the number of the statement's oracle messages (value_plain); and at every N from
that number on, for a row that also has none on later oracle messages (value_plain_le).

Main theorems: onTable_plain, value_plain, value_plain_le, says_plain.

What is not claimed. That a row has no coefficient on a table that is not there: it is a condition
here. Nothing on soundness.

-/
import Johnson.Desc.Means.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- One table. -/
theorem onTable_plain (S : Statement) (row : Row) (m : Words K) (o : Nat) (part : Part)
    (habs : S.has o part = false → ∀ J, ρ.val (row.coefficient o part J) = 0) :
    onTable ρ S row m o part =
      ∑ J ∈ Finset.range (2 ^ (S.rowBits o part + S.placeBits o part)),
        ρ.val (row.coefficient o part J) * m o part J := by
  unfold onTable tableSize
  by_cases hh : S.has o part = true
  · rw [if_pos hh]
    rfl
  · rw [if_neg hh, Finset.range_zero, Finset.sum_empty]
    symm
    apply Finset.sum_eq_zero
    intro J _
    rw [habs (Bool.eq_false_iff.2 hh) J, zero_mul]

/-- **A row applied to words, without the test.** -/
theorem value_plain (S : Statement) (row : Row) (m : Words K)
    (habs : ∀ o part, S.has o part = false → ∀ J, ρ.val (row.coefficient o part J) = 0) :
    value ρ S row m = ∑ o ∈ Finset.range S.oracles.size,
      ((∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
          ρ.val (row.coefficient o .main J) * m o .main J) +
        ∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
          ρ.val (row.coefficient o .mask j) * m o .mask j) := by
  unfold value
  apply Finset.sum_congr rfl
  intro o _
  rw [onTable_plain ρ S row m o .main (habs o .main),
    onTable_plain ρ S row m o .mask (habs o .mask)]

/-- The same at every number of oracle messages from the statement's on. -/
theorem value_plain_le (S : Statement) (row : Row) (m : Words K) (N : Nat)
    (hN : S.oracles.size ≤ N)
    (habs : ∀ o part, S.has o part = false → ∀ J, ρ.val (row.coefficient o part J) = 0)
    (hoff : ∀ o, S.oracles.size ≤ o → ∀ part J, ρ.val (row.coefficient o part J) = 0) :
    value ρ S row m = ∑ o ∈ Finset.range N,
      ((∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
          ρ.val (row.coefficient o .main J) * m o .main J) +
        ∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
          ρ.val (row.coefficient o .mask j) * m o .mask j) := by
  rw [value_plain ρ S row m habs]
  apply Finset.sum_subset
  · intro o ho
    exact Finset.mem_range.2 (Nat.lt_of_lt_of_le (Finset.mem_range.1 ho) hN)
  · intro o _ hno
    have hle : S.oracles.size ≤ o := Nat.le_of_not_lt fun c => hno (Finset.mem_range.2 c)
    have z1 : (∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
        ρ.val (row.coefficient o .main J) * m o .main J) = 0 :=
      Finset.sum_eq_zero fun J _ => by rw [hoff o hle .main J, zero_mul]
    have z2 : (∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
        ρ.val (row.coefficient o .mask j) * m o .mask j) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hoff o hle .mask j, zero_mul]
    rw [z1, z2, add_zero]

/-- What a row says of words, in the plain sum. -/
theorem says_plain (S : Statement) (row : Row) (m : Words K)
    (habs : ∀ o part, S.has o part = false → ∀ J, ρ.val (row.coefficient o part J) = 0) :
    Says ρ S row m ↔ (∑ o ∈ Finset.range S.oracles.size,
      ((∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
          ρ.val (row.coefficient o .main J) * m o .main J) +
        ∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
          ρ.val (row.coefficient o .mask j) * m o .mask j)) = ρ.val row.target := by
  unfold Says
  rw [value_plain ρ S row m habs]

end OnBytes.Means
