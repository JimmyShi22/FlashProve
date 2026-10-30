-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/KeyBack/BoundsCanFail.lean: negative tests for four closed facts on the written
full-size values. Each fact says that a number is below a bound or that a list has at most so many
entries; here the same number or list is shown not to pass a lower bound. So the decisions read
their values and can say no.

The four facts are `reqItem_full` and `small_full` (Johnson/AtFull/KeyBack/WrittenItems.lean) and
`few_proof2` and `few_proof3` (Johnson/AtFull/KeyBack/WrittenFew.lean). The row on the lengths of
the seven strings of parameter bytes spends them (Johnson/AtFull/KeyBack/BytesShort.lean). Each
statement here is that fact's own statement with the bound alone changed. Every statement here is
true: nothing false is stated or assumed.

That the left sides here are those facts' own is checked by Lean: behind each negative test stands
an `example` without a name that states the fact with its own bound, in this file's spelling, and is
closed by the fact itself. It compiles only if the two statements are the same up to definitional
equality; it is no comparison of texts.

`reqItem_big`: the spelling of the request's shape does not have fewer than 2 ^ 12 bytes.
`small_big`: the sum of eighteen small numbers is not below 2 ^ 7. `few_proof2_fails`,
`few_proof3_fails`: the test `fewB` says no at 67 and at 29 entries. `few_proof2_edge`,
`few_proof3_edge`: it says yes at 68 and at 30. `fewB n` asks for at most n entries, each with a
name of at most 32 bytes; since it says yes at one more, its no is for the number of entries, and
the two lists have 68 and 30.

Limits. The first two bounds are not sharp: they lie well below the numbers. The full size alone.
Closed facts by Lean's kernel; they say nothing of any files. Nothing on soundness.
-/
import Johnson.AtFull.KeyBack.WrittenFew
import Johnson.AtFull.KeyBack.WrittenItems

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

open AtFull.KeyBack (fewB stagesOf)

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (writtenLink proofThree)
open Lk6.AtPlan (keyFull)

/-- `reqItem_full` with 2 ^ 12 for 2 ^ 16: it fails. -/
theorem reqItem_big : ¬ (spellReq proofSizedFull.request).size < 2 ^ 12 := by
  rw [size_spellReq]
  decide +kernel

-- The left side as spelled here is that of `reqItem_full`.
example : (spellReq proofSizedFull.request).size < 2 ^ 16 := _root_.AtFull.KeyBack.reqItem_full

/-- `small_full` with 2 ^ 7 for 2 ^ 10: it fails. -/
theorem small_big :
    ¬ keyFull.codes.base.size + keyFull.codes.mask.size + proofSizedFull.codes.base.size +
      proofSizedFull.codes.mask.size + recordCodes.base.size + recordCodes.mask.size +
      stagesOf keyFull.once.shape + stagesOf proofSizedFull.batch.shape +
      writtenLink.shape.later.length + proofSizedFull.request.link.length +
      (Fmt.ascii "codes").size + (Fmt.ascii "the test on the table").size +
      (Fmt.ascii "the link").size + (Fmt.ascii "request's shape").size + (Fmt.ascii "layout").size +
      (Fmt.ascii "links' identifiers").size + (Fmt.ascii "pending rows").size +
      (Fmt.ascii "binding tree").size < 2 ^ 7 := by
  decide +kernel

-- The sum as spelled here is that of `small_full`.
example :
    keyFull.codes.base.size + keyFull.codes.mask.size + proofSizedFull.codes.base.size +
      proofSizedFull.codes.mask.size + recordCodes.base.size + recordCodes.mask.size +
      stagesOf keyFull.once.shape + stagesOf proofSizedFull.batch.shape +
      writtenLink.shape.later.length + proofSizedFull.request.link.length +
      (Fmt.ascii "codes").size + (Fmt.ascii "the test on the table").size +
      (Fmt.ascii "the link").size + (Fmt.ascii "request's shape").size + (Fmt.ascii "layout").size +
      (Fmt.ascii "links' identifiers").size + (Fmt.ascii "pending rows").size +
      (Fmt.ascii "binding tree").size < 2 ^ 10 :=
  _root_.AtFull.KeyBack.small_full

/-- `few_proof2` with 67 for 65536: it fails. -/
theorem few_proof2_fails : fewB 67 proofThree.B.plan.plan.entries = false := by decide +kernel

/-- At 68 it holds. -/
theorem few_proof2_edge : fewB 68 proofThree.B.plan.plan.entries = true := by decide +kernel

-- The test and the list as spelled here are those of `few_proof2`.
example : fewB 65536 proofThree.B.plan.plan.entries = true := _root_.AtFull.KeyBack.few_proof2

/-- `few_proof3` with 29 for 65536: it fails. -/
theorem few_proof3_fails : fewB 29 proofThree.C.plan.plan.entries = false := by decide +kernel

/-- At 30 it holds. -/
theorem few_proof3_edge : fewB 30 proofThree.C.plan.plan.entries = true := by decide +kernel

-- The test and the list as spelled here are those of `few_proof3`.
example : fewB 65536 proofThree.C.plan.plan.entries = true := _root_.AtFull.KeyBack.few_proof3

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.reqItem_big
#print axioms Johnson.AtFull.KeyBack.small_big
#print axioms Johnson.AtFull.KeyBack.few_proof2_fails
#print axioms Johnson.AtFull.KeyBack.few_proof2_edge
#print axioms Johnson.AtFull.KeyBack.few_proof3_fails
#print axioms Johnson.AtFull.KeyBack.few_proof3_edge
