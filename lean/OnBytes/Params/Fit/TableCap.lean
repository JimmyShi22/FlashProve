-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/TableCap.lean: the committed table's sizes, as the derivation makes them from the
parameter file's lines, have the caps that the laws on the planner's routines ask of a table.

"deriveTable s l" (OnBytes/Params/Derive.lean) takes the table's code, its number of row variables
and its answers from the lines and takes or derives the distances. "TableOk T"
(OnBytes/Params/Fit/FitSmall.lean) asks: logN ≤ 64, v ≤ 2 ^ 32, clog2 ell ≤ 2 ^ 32, at most
four answers.

Main theorems.
 - clog2_le: n ≤ 2 ^ k gives clog2 n ≤ k.
 - deriveTable_fields: the code, v and the answers of what deriveTable returns are the lines'.
 - **tableOk_of_lines**: LinesCap l (OnBytes/Params/Fit/LinesCap.lean) and deriveTable s l = some T
   give TableOk T, at every setting s.

Limits. Nothing on the distances. The program does not import this file.

-/
import OnBytes.Params.Derive
import OnBytes.Params.Fit.FitSmall
import OnBytes.Params.Fit.LinesCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- The rounded-up logarithm is at most every exponent that is large enough. -/
theorem clog2_le {n k : Nat} (h : n ≤ 2 ^ k) : clog2 n ≤ k := by
  unfold clog2
  split
  · exact Nat.zero_le k
  · rename_i h1
    have h2 : Nat.log2 (n - 1) < k := (Nat.log2_lt (by omega)).2 (by omega)
    omega

/-- What sizeRecordedTable returns keeps the code, the row variables and the answers. -/
theorem sizeRecorded_fields {s : Setting} {T T' : TableSize} {requests pointVariables : Nat}
    (h : sizeRecordedTable s T requests pointVariables = some T') :
    T'.code = T.code ∧ T'.v = T.v ∧ T'.answers = T.answers := by
  unfold sizeRecordedTable at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl, rfl⟩

/-- The code, the row variables and the answers are the lines'. -/
theorem deriveTable_fields {s : Setting} {l : Lines} {T : TableSize}
    (h : deriveTable s l = some T) :
    T.code = { logN := l.tableLogN, ell := l.tableData, r := l.tableRandom } ∧
      T.v = l.tableRowsLog ∧ T.answers = l.answers := by
  unfold deriveTable at h
  dsimp only at h
  split at h
  · cases h
  · exact sizeRecorded_fields h

/-- **The table's caps from the lines' ranges.** -/
theorem tableOk_of_lines {s : Setting} {l : Lines} {T : TableSize} (H : LinesCap l)
    (h : deriveTable s l = some T) : TableOk T := by
  obtain ⟨e1, e2, e3⟩ := deriveTable_fields h
  have hN := H.tLogN
  have hp : 2 ^ l.tableLogN ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hN
  have hf := H.tFit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]
    show l.tableLogN ≤ 64
    omega
  · rw [e2]
    have := H.tRows
    omega
  · rw [e1]
    show clog2 l.tableData ≤ 2 ^ 32
    have h32 : clog2 l.tableData ≤ 32 := clog2_le (by omega)
    omega
  · rw [e3]
    exact H.answers.2

end OnBytes.Params

#print axioms OnBytes.Params.clog2_le
#print axioms OnBytes.Params.deriveTable_fields
#print axioms OnBytes.Params.tableOk_of_lines
