-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/WrittenFew.lean: THE SEVEN WRITTEN LISTS OF ROUNDS OF THE FULL SIZE ARE FEW:
the test fewB 65536 (Johnson/AtFull/KeyBack/ShortOfBounds.lean) accepts at each: BY LEAN's KERNEL.
Closed facts alone; they ride in a file of their own, since a kernel's walk may run away. NO
SUB-PROTOCOL IMPORTS THIS FILE.
  few_key1 | few_key2 | few_key3 · few_entry · few_proof1 | few_proof2 | few_proof3
  few_can_fail      a negative test: at 32768 the proof file's first list is rejected
LIMITS. On the written values alone (keyThree · pricedEntryFull · proofThree). No soundness is
claimed.
-/
import Johnson.AtFull.KeyBack.ShortOfBounds
import Johnson.Goal.Written.Made

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtFull.KeyBack
open Johnson.G (pricedEntryFull)
open VerifiableInference.Number.ByRuns (keyThree proofThree)

theorem few_key1 : fewB 65536 keyThree.A.plan.plan.entries = true := by decide +kernel
theorem few_key2 : fewB 65536 keyThree.B.plan.plan.entries = true := by decide +kernel
theorem few_key3 : fewB 65536 keyThree.C.plan.plan.entries = true := by decide +kernel
theorem few_entry : fewB 65536 pricedEntryFull.plan.entries = true := by decide +kernel
theorem few_proof1 : fewB 65536 proofThree.A.plan.plan.entries = true := by decide +kernel
theorem few_proof2 : fewB 65536 proofThree.B.plan.plan.entries = true := by decide +kernel
theorem few_proof3 : fewB 65536 proofThree.C.plan.plan.entries = true := by decide +kernel

/-- A negative test. -/
theorem few_can_fail : fewB 32768 proofThree.A.plan.plan.entries = false := by decide +kernel

end AtFull.KeyBack

#print axioms AtFull.KeyBack.few_key1
#print axioms AtFull.KeyBack.few_key2
#print axioms AtFull.KeyBack.few_key3
#print axioms AtFull.KeyBack.few_entry
#print axioms AtFull.KeyBack.few_proof1
#print axioms AtFull.KeyBack.few_proof2
#print axioms AtFull.KeyBack.few_proof3
#print axioms AtFull.KeyBack.few_can_fail
