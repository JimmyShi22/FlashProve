-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ShownAt.lean: WHAT WAS SHOWN UNDER A SLOT (`Fork.shown`,
OnBytes/Model/Hide.lean) AT A SLOT WRITTEN s + i, WITH THE SLOT's MARK READ BEHIND THE FIRST s
MARKS: `shownAt`; AND THE TWO ARE EQUAL AT EVERY LEDGER: `shown_add`. No premise. One definition,
one theorem. It imports OnBytes/Model/Hide.lean alone.

Purpose. Fork.shown F j reads the j-th of the ledger's marks by its index. Lean's kernel walks an
array's list from its head at each such read: some hundred reads far down a ledger of some thousand
slots cost it a minute and gigabytes (seen by trial; not shown here). The reads of one sumcheck's
end values stand side by side, at s + 0, s + 1, …: shownAt drops the first s marks and reads at i:
where many reads have one s, the term `drop s …` is the same in all of them. Whoever has to evaluate
a text that reads so may rewrite by shown_add first.

Main names.
* `shownAt F s i`: Fork.shown's text at s + i, with `(F.gotF.toList.drop s).getD i false` for
  `F.gotF.getD (s + i) false`.
* **`shown_add`**: F.shown (s + i) = shownAt F s i.

Limits. An equality of two functions. Nothing is said on what either costs; nothing is evaluated
here. THAT AN EVALUATOR WALKS THE FIRST s MARKS ONCE FOR ALL READS WITH THAT s IS NO LAW: it hangs
on the evaluator's remembering a term that it has met. The value that is handed out is still read by
its index (`F.vp.getD (s + i) zeroE`). A rewriting finds only slots that are written as a sum.
Nothing on soundness, completeness or hiding.
-/
import OnBytes.Model.Hide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.ShownAt
open OnBytes OnBytes.Model

/-- Fork.shown's text (OnBytes/Model/Hide.lean) at the slot s + i, with the mark read in the list of
marks behind its first s members. -/
def shownAt (F : Fork) (s i : Nat) : Option E :=
  if decide (s + i < F.ns) && (F.gotF.toList.drop s).getD i false then
    some (F.vp.getD (s + i) zeroE)
  else none

/-- **THE LAW: Fork.shown AT s + i IS shownAt AT s AND i**, at every ledger. -/
theorem shown_add (F : Fork) (s i : Nat) : F.shown (s + i) = shownAt F s i := by
  have e : F.gotF.getD (s + i) false = (F.gotF.toList.drop s).getD i false := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_drop]
  unfold Fork.shown shownAt
  rw [e]

end Johnson.AtFull.Shape.ShownAt

#print axioms Johnson.AtFull.Shape.ShownAt.shown_add
#print axioms Johnson.AtFull.Shape.ShownAt.shownAt
