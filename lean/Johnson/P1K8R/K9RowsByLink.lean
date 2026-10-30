-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/K9RowsByLink.lean: the proofs of the four statements of
Johnson/P1K8R/K9RowsByLinkStatement.lean, to the letter. Lemmas; none of the library's goals.

How. `k9Rows_closed`, `k9Rows_bites`: BY LEAN's KERNEL, over the term `xsW`
(Johnson/AtFull/Desc/Lots/K9RowWritten.lean), whose walk hands the kernel a tail of the written list
and a numeral at each step. THE SAME 25 NUMBERS STAND IN `full_rows`
(Johnson/Desc/First/Batch/Law/Condition.lean). `k9Rows_of_written`: `IM.k9At Z l` is `k9Where` at
`k9Stretches Z`, by its text; `k9Where_eq` (K9RowAt.lean); `k9_stretches_at`
(Johnson/AtFull/Rounds/K9.lean) under `spots_written` (Johnson/AtFull/Desc/SpotsWritten.lean);
`walk_eq` (K9RowWritten.lean). `k9Rows_at_head`: `AtMg.plans_written`
(Johnson/P5J/NumbersAtHead.lean); `cuts_of_plans`, `entries_of_plans`
(Johnson/Desc/First/Att/Row/K5FrontOne.lean); the written entries have two names, `esW` and
`P5T.esFull.1`, with one text.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.K9RowsByLinkStatement
import Johnson.AtFull.Rounds.K9
import Johnson.Desc.First.Att.Row.K5FrontOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open Johnson.AtFull.Desc.Lots (k9WhereE xsW esW k9Where_eq walk_eq)
open Johnson.AtFull.Desc (spotsWritten spots_written)
open Johnson.AtFull.Cut (cutWritten)

/-- **By the kernel: the 25 numbers, by the segment's number.** -/
theorem k9Rows_closed : K9RowsClosed := by
  show rowsClosedB rowsAtLink = true
  decide +kernel

/-- **By the kernel: the test can fail.** -/
theorem k9Rows_bites : K9RowsBites := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **At the written values.** -/
theorem k9Rows_of_written : K9RowsOfWritten := by
  intro Z hc he l hl
  have hs : ProofFile.spotsOf Z.cuts = some spotsWritten := by
    rw [hc]
    exact spots_written
  have e2 : IM.k9At Z l = k9WhereE xsW l :=
    (k9Where_eq (ProofFile.k9Stretches Z) l).trans
      (congrArg (fun xs => k9WhereE xs l)
        ((Johnson.AtFull.Rounds.k9_stretches_at Z hs he).trans (walk_eq spotsWritten esW 0)))
  have c := of_decide_eq_true (List.all_eq_true.1 k9Rows_closed l (List.mem_range.2 hl))
  rw [← e2] at c
  obtain ⟨p, hp, hr⟩ := Option.map_eq_some_iff.1 c
  exact ⟨p, hp, hr⟩

/-- **Under the head.** -/
theorem k9Rows_at_head : K9RowsAtHead := by
  intro o Z D r Zp Np cF h l hl
  have h1 : Zp.plans.1 = P5T.esFull.1 := congrArg Prod.fst h.plans_written
  have hZ := H2K5.Row.asBy h.laid.pub
  exact k9Rows_of_written Zp (H2K5.Row.cuts_of_plans hZ h1) (H2K5.Row.entries_of_plans hZ h1) l hl

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.k9Rows_closed
#print axioms P1K8.k9Rows_bites
#print axioms P1K8.k9Rows_of_written
#print axioms P1K8.k9Rows_at_head
