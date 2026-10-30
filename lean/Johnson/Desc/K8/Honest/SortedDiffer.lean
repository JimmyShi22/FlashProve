-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SortedDiffer.lean: THE SMALLNESS TEST: WHERE THE TEST "NO TWO NEIGHBOURS OF
THE SORTED LIST ARE EQUAL" (neighboursDiffer, OnBytes/Model/Tail.lean) SAYS NO, TWO ENTRIES OF THE
LIST ARE EQUAL; AND WHERE THE ENTRIES READ AS THE POWERS (x ^ N) ^ R, TWO OF THESE POWERS ARE.
Statements and proofs. On plain lists: no block, no prover. Lemmas; none of the library's goals.

  `differ_of_nodup`, **`sorted_differ`**   a list without doubles passes the test, also when it has
      been sorted, by whatever comparison
  **`two_equal`**   a no of the test on the sorted list: two entries of the list, at two places, are
      equal
  **`powers_of_no`**   the list has m entries, entry R reads as (x ^ N) ^ R: a no of the test gives
      i < j < m with (x ^ N) ^ i = (x ^ N) ^ j: the event that `powers_meet_few`
      (Johnson/Desc/K8/Honest/PowersMeet.lean) counts
Limits. One way alone: that the test says no wherever two entries are equal wants the comparison to
be an order, and is not said. That any row's weights read as such powers is not shown here.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Model.Tail
import OnBytes.Model.HideLaws
import Mathlib.Data.List.Nodup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

theorem differ_of_nodup : ∀ l : List E, l.Nodup → neighboursDiffer l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    have h1 : a ≠ b := fun e => (List.nodup_cons.1 h).1 (e ▸ List.mem_cons_self)
    have h2 := differ_of_nodup (b :: t) (List.nodup_cons.1 h).2
    show (a != b && neighboursDiffer (b :: t)) = true
    rw [h2, Bool.and_true]
    exact bne_iff_ne.2 h1

/-- **A list without doubles passes the test when it has been sorted.** -/
theorem sorted_differ (l : List E) (le : E → E → Bool) (h : l.Nodup) :
    neighboursDiffer (l.mergeSort le) = true :=
  differ_of_nodup _ ((List.mergeSort_perm l le).nodup_iff.2 h)

/-- **A no of the test: two entries are equal.** -/
theorem two_equal (l : List E) (le : E → E → Bool)
    (h : neighboursDiffer (l.mergeSort le) = false) :
    ∃ i j, i < j ∧ j < l.length ∧ l[i]? = l[j]? := by
  by_contra hc
  have hn : l.Nodup := by
    rw [List.nodup_iff_getElem?_ne_getElem?]
    intro i j hij hj he
    exact hc ⟨i, j, hij, hj, he⟩
  rw [sorted_differ l le hn] at h
  cases h

/-- **Where the entries read as powers, two of the powers are equal.** -/
theorem powers_of_no (l : List E) (le : E → E → Bool) (x : Cb.Gl.E) (N m : ℕ)
    (hl : l.length = m) (hv : ∀ R, R < m → Reading.gl.val (l.getD R zeroE) = (x ^ N) ^ R)
    (h : neighboursDiffer (l.mergeSort le) = false) :
    ∃ i j, i < j ∧ j < m ∧ (x ^ N) ^ i = (x ^ N) ^ j := by
  obtain ⟨i, j, hij, hj, he⟩ := two_equal l le h
  rw [hl] at hj
  refine ⟨i, j, hij, hj, ?_⟩
  rw [← hv i (by omega), ← hv j hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, he]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.sorted_differ
#print axioms VerifiableInference.Desc.First.K8.Honest.two_equal
#print axioms VerifiableInference.Desc.First.K8.Honest.powers_of_no
