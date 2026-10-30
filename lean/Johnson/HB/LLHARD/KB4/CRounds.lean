-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/CRounds.lean: the written declared rounds' entries are the rounds of the three
written plans: three closed equations, by the test == in Lean's kernel; three negative tests, which
stand beside equations between written values: they show only that the test == can say no at these
lists.

Why. The test on the file asks this twice: as the clause "rounds", by ==, and as the clause
"declared", by a decision of the equation. At the first chain's 18,851 rounds the kernel runs out of
stack on the second form and gets through the first. So the equations are had from the first form,
and the second follows by a law.
Limits. At written values alone. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.SourceW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Number.ByRuns (keyThree)
open Johnson.KB8 (declKeyFull)

set_option maxRecDepth 1000000 in
theorem rounds₁ : declKeyFull.1.map (·.entry) = keyThree.A.plan.plan.rounds :=
  eq_of_beq (by decide +kernel)

theorem rounds₂ : declKeyFull.2.1.map (·.entry) = keyThree.B.plan.plan.rounds :=
  eq_of_beq (by decide +kernel)

theorem rounds₃ : declKeyFull.2.2.map (·.entry) = keyThree.C.plan.plan.rounds :=
  eq_of_beq (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem rounds₁_no :
    (declKeyFull.1.dropLast.map (·.entry) == keyThree.A.plan.plan.rounds) = false := by
  decide +kernel

theorem rounds₂_no : (declKeyFull.2.1.map (·.entry) == keyThree.C.plan.plan.rounds) = false := by
  decide +kernel

theorem rounds₃_no : (declKeyFull.2.2.map (·.entry) == keyThree.B.plan.plan.rounds) = false := by
  decide +kernel

end Johnson.KB4

#print axioms Johnson.KB4.rounds₁
#print axioms Johnson.KB4.rounds₂
#print axioms Johnson.KB4.rounds₃
#print axioms Johnson.KB4.rounds₁_no
#print axioms Johnson.KB4.rounds₂_no
#print axioms Johnson.KB4.rounds₃_no
