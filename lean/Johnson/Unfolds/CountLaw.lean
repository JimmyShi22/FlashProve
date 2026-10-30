-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/CountLaw.lean: an array of counters that a fold of `Array.modify` fills, read at an
index, is a count over the list.

Why. To Lean's kernel an array is a list: a read, a write and the size each walk it. A routine that
counts with an array of n counters and then reads it at every index costs, by our reading of these
texts, of the order of n times n steps there. With this law such a test is restated without an
array.

  `getD_modify_succ`: one counter more at j: the value read at i grows by one just if j = i and i
    lies inside the array.
  **`getD_foldl_modify`**: behind the fold the value read at i is what stood there plus the number
    of members whose key is i; outside the array nothing is counted.

Limits. General laws: no closed fact. The cost named above is by reading, not measured. No import:
Lean's own library alone.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds

universe u

/-- One counter more. -/
theorem getD_modify_succ (A : Array Nat) (j i : Nat) :
    (A.modify j (· + 1)).getD i 0 = A.getD i 0 + (if j = i ∧ i < A.size then 1 else 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : j = i
  · subst h
    by_cases hs : j < A.size
    · simp [hs]
    · simp [hs]
  · simp [h]

/-- **The counters behind the fold.** -/
theorem getD_foldl_modify {α : Type u} (key : α → Nat) : ∀ (ts : List α) (A : Array Nat) (i : Nat),
    (ts.foldl (fun n t => n.modify (key t) (· + 1)) A).getD i 0 =
      A.getD i 0 + (if i < A.size then ts.countP (fun t => key t == i) else 0)
  | [], A, i => by simp
  | t :: ts, A, i => by
    rw [List.foldl_cons, getD_foldl_modify key ts, getD_modify_succ, Array.size_modify,
      List.countP_cons]
    by_cases hs : i < A.size
    · by_cases h : key t = i
      · simp [hs, h]
        omega
      · simp [hs, h]
    · simp [hs]

end Johnson.Unfolds

#print axioms Johnson.Unfolds.getD_modify_succ
#print axioms Johnson.Unfolds.getD_foldl_modify
