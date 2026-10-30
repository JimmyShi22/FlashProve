-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/MsgsLeFull.lean: AT THE WRITTEN VALUES: THE TABLE's COUNT OF MESSAGES AT EVERY BORDER
OF THE CLOSED LIST OF PLACES `P5J.At.ps` IS AT MOST THE NUMBER OF THE WRITTEN SENDINGS' MESSAGES: BY
LEAN's KERNEL. Five theorems. No public file is read.
  `ps_len_358`: the list of places `P5J.At.ps` has 358 members.
  `msgs_counts`: the written sendings have 199 messages; the count behind the last place is 199:
  SO THE INEQUALITY IS TIGHT THERE; with 198 in the place of 199 it holds at 357 of the 359
  borders alone.
  `msgs_le_full`: **by the kernel: at the borders 0 to 358.**
  `msgs_le_every`: so at every number k (beyond the list there is no place, as at 358).
  `msgs_at_batch`: a by-product: two borders behind each segment's batching the counts are 7, 14,
  22, …, 179, 185.
Every number here was printed by the evaluator before it was typed. (One forecast for that print
failed: 185 messages were expected; 14 more stand behind the last segment.)
Limits. The written values alone: that they are a verifier's is another file's
(Johnson/P5T/MsgsLeAtMg.lean). The full size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.FenceFull
import Johnson.Top.H0.K2Hands.FrontsFull
import Johnson.P5J.LettersAt
import Johnson.Desc.First.Link.Law.K9KindTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc.First.K2Hands (MList)
open VerifiableInference.Desc.LinkJoin (batchAt)

set_option maxRecDepth 1000000 in
/-- By the kernel: the list of places `P5J.At.ps` has 358 members. -/
theorem ps_len_358 : P5J.At.ps.length = 358 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: what the inequality ranges over; a negative test. -/
theorem msgs_counts :
    (MList.length, NFull.msgsAt none,
      ((List.range 359).filter fun k => decide (NFull.msgsAt P5J.At.ps[k]? ≤ 198)).length) =
      (199, 199, 357) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **By the kernel: at the borders 0 to 358.** -/
theorem msgs_le_full :
    ((List.range 359).all fun k => decide (NFull.msgsAt P5J.At.ps[k]? ≤ MList.length)) = true := by
  decide +kernel

/-- **So at every number.** -/
theorem msgs_le_every (k : ℕ) : NFull.msgsAt P5J.At.ps[k]? ≤ MList.length := by
  by_cases hk : k < 359
  · exact of_decide_eq_true (List.all_eq_true.1 msgs_le_full k (List.mem_range.2 hk))
  · have e : P5J.At.ps[k]? = P5J.At.ps[358]? := by
      rw [List.getElem?_eq_none (by rw [ps_len_358]; omega),
        List.getElem?_eq_none (by rw [ps_len_358])]
    rw [e]
    exact of_decide_eq_true (List.all_eq_true.1 msgs_le_full 358 (List.mem_range.2 (by decide)))

set_option maxRecDepth 1000000 in
/-- By the kernel: the counts two borders behind each segment's batching. -/
theorem msgs_at_batch :
    ((List.range 25).map fun m =>
      NFull.msgsAt P5J.At.ps[batchAt P5J.fullLinks P5J.At.ps m + 1 + 1]?) =
      [7, 14, 22, 29, 37, 44, 52, 59, 67, 74, 82, 89, 97, 104, 112, 119, 127, 134, 142, 149, 157,
        164, 172, 179, 185] := by decide +kernel

end P5T

#print axioms P5T.ps_len_358
#print axioms P5T.msgs_counts
#print axioms P5T.msgs_le_full
#print axioms P5T.msgs_le_every
#print axioms P5T.msgs_at_batch
