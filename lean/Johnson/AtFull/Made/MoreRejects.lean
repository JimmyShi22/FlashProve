-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/MoreRejects.lean: two tests with code can say no: `wordsB`
(Johnson/AtFull/Made/ItemTests.lean) and `sameWords` (Johnson/AtFull/Made/ReadsOfConfigure.lean).
Closed facts, by Lean's kernel (`decide +kernel`).

`wordsB_small`, `wordsB_rejects`: a list of three numbers passes; with 2 ^ 64 as its second member
it fails. `sameWords_self`, `sameWords_rejects`: the written first plan of a key file of full size
has its own six settings; with one of the six changed it has not: one negative test for each
setting.

Limits. The clause of `wordsB` on the list's length is not shown to say no: a list of 2 ^ 64 members
cannot be written. These facts serve no law. Nothing on soundness.
-/
import Johnson.AtFull.Made.ReadsOfConfigure
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.Number.ByRuns (keyThree)

/-- A list of three small numbers passes. -/
theorem wordsB_small : wordsB [3, 1, 2] = true := by decide +kernel

/-- With 2 ^ 64 as its second member it fails. -/
theorem wordsB_rejects : wordsB [3, 2 ^ 64, 2] = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test says yes of the written first plan of a key file against itself. -/
theorem sameWords_self : sameWords keyThree.A.plan.plan keyThree.A.plan.plan = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Against itself with one of the six settings changed, the test says no: the field; the bytes of a
leaf's salt, of a nonce, of a listed position; the answers to each out-of-domain sample; the word
that says whether a sum-check's message leaves out a coefficient. -/
theorem sameWords_rejects :
    (sameWords keyThree.A.plan.plan { keyThree.A.plan.plan with field := .one },
      sameWords keyThree.A.plan.plan
        { keyThree.A.plan.plan with salt := keyThree.A.plan.plan.salt + 1 },
      sameWords keyThree.A.plan.plan
        { keyThree.A.plan.plan with nonce := keyThree.A.plan.plan.nonce + 1 },
      sameWords keyThree.A.plan.plan
        { keyThree.A.plan.plan with posB := keyThree.A.plan.plan.posB + 1 },
      sameWords keyThree.A.plan.plan
        { keyThree.A.plan.plan with samples := keyThree.A.plan.plan.samples + 1 },
      sameWords keyThree.A.plan.plan
        { keyThree.A.plan.plan with saved := keyThree.A.plan.plan.saved + 1 }) =
      (false, false, false, false, false, false) := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.wordsB_small
#print axioms Johnson.AtFull.Made.wordsB_rejects
#print axioms Johnson.AtFull.Made.sameWords_self
#print axioms Johnson.AtFull.Made.sameWords_rejects
