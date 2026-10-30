-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Laid/AsksFirstLaw.lean: two facts on `firstNo`, general in the list.

  firstNo_none        no test of a list says no just where every test of it says yes
  asksYes_append      **a yes of a longer list is a yes of the shorter**: appending tests takes no
                      yes of an earlier test away

-/
import Johnson.Desc.Laid.AsksFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD

/-- No test of a list says no just where every test of it says yes. -/
theorem firstNo_none (l : List (String × Bool)) :
    firstNo l = none ↔ ∀ t ∈ l, t.2 = true := by
  unfold firstNo
  simp [List.find?_eq_none]

/-- **A yes of a longer list is a yes of the shorter.** -/
theorem asksYes_append (l m : List (String × Bool)) (h : firstNo (l ++ m) = none) :
    firstNo l = none :=
  (firstNo_none l).2 fun t ht => (firstNo_none (l ++ m)).1 h t (List.mem_append_left m ht)

end LPFD

#print axioms LPFD.firstNo_none
#print axioms LPFD.asksYes_append
