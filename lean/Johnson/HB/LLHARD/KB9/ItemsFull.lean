-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/ItemsFull.lean: THE WRITTEN SIZES OF A KEY OF FULL SIZE (`keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean) ARE VALUES THAT ARE READ BACK AS THEY ARE SPELT: they
pass the tests of Johnson/HB/LLHARD/KB9/ItemsOk.lean. Closed facts, by Lean's kernel (`decide
+kernel`). No byte is laid: the tests read numbers.

  **`itemsB_full`**: `itemsB keyFull = true`.
  `itemsB_rejects`: the negative tests, eight bent twins, each rejected: (1) in the codes: the
    logarithm of a code's length is 2 ^ 64 · (2) the index masks' notice: the degree is 2 · (3) it
    has no main rows and the code 0 · (4) THE CASE IN WHICH THE ROUND TRIP IS NOT THE IDENTITY: W's
    shape in the test on the table without mask rows and with the mask code 0, which is the
    structure's own default · (5) in the ranges: the message's number is 2 ^ 64 · (6) in the test on
    the table: the number of the matrix's rows is 2 ^ 64 · (7) the binding tree: the depth is 2 ^ 64
    · (8) an element of the field: the modulus itself.

Limits. Two closed facts. Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB9.ItemsOk
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params OnBytes.Plan
open Lk6.AtPlan (keyFull)

set_option maxRecDepth 1000000 in
/-- **The written sizes of a key of full size pass.** -/
theorem itemsB_full : itemsB keyFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative tests: eight bent twins. -/
theorem itemsB_rejects :
    [itemsB { keyFull with codes := ⟨#[⟨2 ^ 64, 0, 0⟩], #[]⟩ },
      noticeB ⟨{ keyFull.once.input.shape with mainDeg := 2 }, 0⟩,
      noticeB ⟨{ keyFull.once.input.shape with mainRows := 0, code := 0 }, 0⟩,
      linB { keyFull.once.shape with
        w := { keyFull.once.shape.w with maskRows := 0, maskCode := 0 } },
      rangesB { keyFull.ranges.x with messageId := 2 ^ 64 },
      linB { keyFull.once.shape with matrixRows := 2 ^ 64 },
      bindingB ⟨2 ^ 64, 0⟩,
      eltB (UInt64.ofNat Fmt.Fld.two.p)] = List.replicate 8 false := by decide +kernel

end Johnson.KB9

#print axioms Johnson.KB9.itemsB_full
#print axioms Johnson.KB9.itemsB_rejects
