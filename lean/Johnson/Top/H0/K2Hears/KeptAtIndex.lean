-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/KeptAtIndex.lean: the code switch: THE KEPT ROWS OF THE CARRIED ROWS'
SYMBOLS AT A POSITION, BY INDEX: entry number 1 + (the main rows of the kept members in front) + b
of what Johnson/Desc/Own/Symbols.lean's rowsAt returns is main symbol number b of the kept member's
own column.
  flatMap_at     an entry of a list of lists laid flat
  keptNos        the numbers, in the layout's list of members, of the members that it marks as kept
                 rowsAt_kept_at the statement
LIMITS. On lists of symbols alone: no typed word, no decoder. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.KeptAtFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem flatMap_at {α β : Type} (f : α → List β) : ∀ (l : List α) (a : Nat) (x : α) (b : Nat),
    l[a]? = some x → b < (f x).length →
      (l.flatMap f)[((l.take a).map fun y => (f y).length).sum + b]? = (f x)[b]?
  | [], a, x, b, h, _ => by simp at h
  | y :: l, 0, x, b, h, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons]
    exact List.getElem?_append_left hb
  | y :: l, a + 1, x, b, h, hb => by
    have h' : l[a]? = some x := by simpa using h
    have ih := flatMap_at f l a x b h' hb
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons]
    rw [Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact ih

/-- The numbers of the members that the layout marks as kept. -/
def keptNos (L : GroupLayout) : List Nat :=
  (List.range L.members.size).filter fun w => L.kept.getD w false

/-- **The kept rows, by index.** -/
theorem rowsAt_kept_at (s : SingleRows) (hm : s.masks = 2) (opened : Array (Array Column)) (i : Nat)
    (seg : Array E) (h : rowsAt s opened #[] i = some seg) (a w b : Nat)
    (hw : (keptNos s.layout)[a]? = some w) (hb : b < (colAtW opened i w).main.size) :
    seg[1 + ((((keptNos s.layout).take a).map fun y => (colAtW opened i y).main.size).sum + b)]? =
      (colAtW opened i w).main[b]? := by
  obtain ⟨x, y, z, e⟩ := rowsAt_kept s hm opened i seg h
  have e' : seg.toList = x ::
      ((keptNos s.layout).flatMap (fun w => (colAtW opened i w).main.toList) ++ [y, z]) := e
  have hb' : b < (colAtW opened i w).main.toList.length := by simpa using hb
  have e1 := flatMap_at (fun w => (colAtW opened i w).main.toList) (keptNos s.layout) a w b hw hb'
  have hlt : (((keptNos s.layout).take a).map
        fun y => (colAtW opened i y).main.toList.length).sum + b <
      ((keptNos s.layout).flatMap fun w => (colAtW opened i w).main.toList).length := by
    rw [List.getElem?_eq_getElem hb'] at e1
    obtain ⟨h1, -⟩ := List.getElem?_eq_some_iff.1 e1
    exact h1
  rw [← Array.getElem?_toList, e', Nat.add_comm 1, List.getElem?_cons_succ]
  simp only [Array.length_toList] at e1 hlt
  rw [List.getElem?_append_left hlt, e1, Array.getElem?_toList]

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.rowsAt_kept_at
