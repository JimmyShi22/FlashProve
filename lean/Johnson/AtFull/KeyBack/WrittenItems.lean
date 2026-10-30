-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/WrittenItems.lean: THE ITEMS' SIZES AT THE WRITTEN SIZES OF THE FULL SIZE AND
AT THE WRITTEN LAYOUT, AS SUMS OF NUMBERS: BY LEAN's KERNEL; no bytes are laid in a row. Closed
facts alone, in a file of their own. NO SUB-PROTOCOL IMPORTS THIS FILE.
  reqItem_full      the item "request's shape" at proofSizedFull.request: fewer than 2 ^ 16 bytes
  layoutItem_full   the item "layout" at layoutFull (Johnson/G/LayoutLit.lean): fewer than 2 ^ 20
  layoutItem_big    a negative test: not fewer than 2 ^ 18
  small_full        the numbers of codes, of stages and of segments, and the items' names
LIMITS. On the written values alone. No soundness is claimed.
-/
import Johnson.AtFull.KeyBack.ItemsSums
import Johnson.Goal.Written.Made
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (layoutFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (writtenLink)
open Lk6.AtPlan (keyFull)

theorem reqItem_full : (spellReq proofSizedFull.request).size < 2 ^ 16 := by
  rw [size_spellReq]
  decide +kernel

theorem layoutItem_full : (spellLayout layoutFull).size < 2 ^ 20 := by
  rw [size_spellLayout]
  decide +kernel

/-- A negative test. -/
theorem layoutItem_big : ¬ (spellLayout layoutFull).size < 2 ^ 18 := by
  rw [size_spellLayout]
  decide +kernel

theorem small_full :
    keyFull.codes.base.size + keyFull.codes.mask.size + proofSizedFull.codes.base.size +
      proofSizedFull.codes.mask.size + recordCodes.base.size + recordCodes.mask.size +
      stagesOf keyFull.once.shape + stagesOf proofSizedFull.batch.shape +
      writtenLink.shape.later.length + proofSizedFull.request.link.length +
      (Fmt.ascii "codes").size + (Fmt.ascii "the test on the table").size +
      (Fmt.ascii "the link").size + (Fmt.ascii "request's shape").size +
      (Fmt.ascii "layout").size + (Fmt.ascii "links' identifiers").size +
      (Fmt.ascii "pending rows").size + (Fmt.ascii "binding tree").size < 2 ^ 10 := by
  decide +kernel

end AtFull.KeyBack

#print axioms AtFull.KeyBack.reqItem_full
#print axioms AtFull.KeyBack.layoutItem_full
#print axioms AtFull.KeyBack.layoutItem_big
#print axioms AtFull.KeyBack.small_full
