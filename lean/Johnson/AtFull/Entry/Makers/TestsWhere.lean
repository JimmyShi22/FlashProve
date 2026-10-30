-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/Makers/TestsWhere.lean: AT WHICH LINKS THE TESTS BEHIND THE ADDING HAVE A
PLACE, AS A GENERAL LAW. Nothing is evaluated here.

Why. The row of the batching's lot in the proof file's first chain
(Johnson/AtFull/Desc/Lots/K9RowWritten.lean) stands under the hypothesis that
`K9.testsWhere X l 0` returns exactly at the links below 25. That function
(Johnson/Desc/First/Batch/TestsAtS.lean) reads four things of the public part X to decide whether it
returns: the switch for attention, the number of groups, and how many plans for layers and for
attention there are. So the hypothesis follows from these four.

  `tests_where_all`: where attention is covered, there are twelve groups, twelve plans for layers
    and twelve for attention: at EVERY number l, `(K9.testsWhere X l 0).isSome` is `twW l`, that is
    "l is below 25".

Limits. The four facts are premises; no public part is shown to meet them here. It says whether the
function returns, and nothing of the value that it returns. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.TestsAtS
import Johnson.AtFull.Desc.Lots.K9RowWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry

open OnBytes OnBytes.Model

/-- **The place of the tests behind the adding is there exactly at the links below 25.** -/
theorem tests_where_all {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hG : X.G.size = 12) (hA : X.A.size = 12) (l : Nat) :
    (VerifiableInference.Desc.K9.testsWhere X l 0).isSome = Johnson.AtFull.Desc.Lots.twW l := by
  unfold VerifiableInference.Desc.K9.testsWhere Johnson.AtFull.Desc.Lots.twW
  rw [h4, hN]
  simp only [if_true]
  by_cases e24 : l = 24
  · subst e24
    rfl
  · have c1 : (l == 2 * 12) = false := by simpa using e24
    rw [c1]
    simp only [Bool.false_eq_true, if_false]
    by_cases he : l % 2 = 0
    · have c2 : (l % 2 == 0) = true := by simpa using he
      rw [c2]
      simp only [if_true]
      by_cases hl : l / 2 < 12
      · rw [Array.getElem?_eq_getElem (show l / 2 < X.G.size by omega)]
        have h25 : l < 25 := by omega
        simp [h25]
      · rw [Array.getElem?_eq_none (show X.G.size ≤ l / 2 by omega)]
        have h25 : ¬ l < 25 := by omega
        simp [h25]
    · have c2 : (l % 2 == 0) = false := by simpa using he
      rw [c2]
      simp only [Bool.false_eq_true, if_false]
      by_cases hl : l / 2 < 12
      · rw [Array.getElem?_eq_getElem (show l / 2 < X.A.size by omega)]
        have h25 : l < 25 := by omega
        simp [h25]
      · rw [Array.getElem?_eq_none (show X.A.size ≤ l / 2 by omega)]
        have h25 : ¬ l < 25 := by omega
        simp [h25]

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.tests_where_all
