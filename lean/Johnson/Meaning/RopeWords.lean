-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/RopeWords.lean: the list recursion of Johnson/Meaning/RopeLists.lean at the stored
example's numbers (cs 12, theta0 500000, 64 pairs, 1024 tokens) gives, word for word, the entries of
the library's stored tables Data.cos and Data.sin; and no stored word passes 8192.

By the 512 evaluations in Lean's kernel beneath Johnson/Meaning/RopeFineWords.lean (rows_ok_fine).
What it does not say by itself: anything on ropeTable (the bridge is table_spec,
Johnson/Meaning/RopeSpec.lean) or on the library's refC | refS, which clamp the stored words and
take 4096 off (Johnson/Goal/Meaning/RopeScope.lean joins the three).
-/
import Johnson.Meaning.RopeFineWords

set_option autoImplicit false

namespace Meaning.Rope

open OnBytes.Model.Layer (fxOne)

/-- The test holds at every pair. -/
theorem rows_ok : ∀ i, i < 64 → rowOK i = true := rows_ok_fine

/-- Every pair's list is the stored one. -/
theorem row_eq {i : ℕ} (hi : i < 64) :
    rowOf 12 1024 (xAt (uOf 500000 64) i fxOne) = dataRow i := by
  have h := rows_ok i hi
  unfold rowOK at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

/-- No stored word passes 8192. -/
theorem row_small {i : ℕ} (hi : i < 64) :
    ((dataRow i).all fun w => decide (w.1 ≤ 8192) && decide (w.2 ≤ 8192)) = true := by
  have h := rows_ok i hi
  unfold rowOK at h
  rw [Bool.and_eq_true] at h
  exact h.2

#print axioms rows_ok
#print axioms row_eq
#print axioms row_small

end Meaning.Rope
