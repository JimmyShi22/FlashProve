-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/Makers/FirstShape.lean: TWO HYPOTHESES OF THE FIRST CHAIN'S ROWS THAT READ THE
REQUEST'S SHAPE ALONE, from "the shape is the written one".

Why. The row of the links' frames (Johnson/AtFull/Desc/Lots/FramesRow.lean) asks that the first 24
links have no plain scalar; a row of the weights' opening asks that the chain's own group of trees
has the number 31 (`K1.ownGroup`, Johnson/Desc/K1/Places.lean: the number of links and of last
entries in the shape). Both read the field `shape` of the first chain's parameters and nothing
else. Other rows already ask that this field is the written shape `proofSizedFull.request`
(Johnson/Desc/Ok/PlanWritten/SizedLit.lean). So the two follow from that one equation and a closed
fact each on the written shape.

  `plain_of_shape`: from the equation and `P1L20.Row.plain_written`.
  `request_groups`: [proved by evaluation in Lean's kernel; no free letter] the written shape has 31
    links and last entries in all. `request_groups_parts`: 25 and 6.
  `request_groups_no`: with one link dropped the count is not 31. No negative test: it follows from
    `request_groups_parts` by arithmetic.
  `ownGroup_of_shape`: from the equation and `request_groups`.
  `request_answers`: [Lean's kernel; no free letter] the written shape asks one answer to a sample.

Limits. The equation is a premise. The written shape is a literal of the library: whence it comes is
its own file's to say. The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.FramesRow
import Johnson.Desc.K1.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Entry

open OnBytes
open VerifiableInference.PlanWritten (proofSizedFull)

/-- The first 24 links have no plain scalar, where the shape is the written one. -/
theorem plain_of_shape {q : Params.First} (u1 : proofSizedFull.request = q.shape) :
    (q.shape.link.map (·.plain)).take 24 = P1L20.Row.plainW := by
  rw [← u1]
  exact P1L20.Row.plain_written

/-- The written shape: 25 links and 6 last entries. -/
theorem request_groups_parts :
    proofSizedFull.request.link.length = 25 ∧ proofSizedFull.request.last.length = 6 := by
  decide +kernel

/-- The written shape has 31 links and last entries in all. -/
theorem request_groups :
    proofSizedFull.request.link.length + proofSizedFull.request.last.length = 31 := by
  decide +kernel

/-- With one link dropped the count is another. No negative test: it follows from
`request_groups_parts` by arithmetic. -/
theorem request_groups_no :
    (proofSizedFull.request.link.drop 1).length + proofSizedFull.request.last.length ≠ 31 := by
  decide +kernel

/-- The written shape asks one answer to a sample. -/
theorem request_answers : proofSizedFull.request.answers = 1 := by decide +kernel

/-- The chain's own group of trees has the number 31, where the shape is the written one. -/
theorem ownGroup_of_shape {q : Params.First} (u1 : proofSizedFull.request = q.shape) :
    VerifiableInference.Desc.K1.ownGroup q = 31 := by
  unfold VerifiableInference.Desc.K1.ownGroup
  rw [← u1]
  exact request_groups

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.plain_of_shape
#print axioms Johnson.AtFull.Entry.request_groups_parts
#print axioms Johnson.AtFull.Entry.request_groups
#print axioms Johnson.AtFull.Entry.request_groups_no
#print axioms Johnson.AtFull.Entry.request_answers
#print axioms Johnson.AtFull.Entry.ownGroup_of_shape
