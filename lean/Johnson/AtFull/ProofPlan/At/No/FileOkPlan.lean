-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/FileOkPlan.lean: a negative line: the tests on the plan
(`FileDescription.planOk`, Johnson/Desc/Block.lean) say no at `wpFile`
(Johnson/AtFull/ProofPlan/At/Bent2.lean: the written description with its field fileOk set to
false).

Why. The line beside it, `wp_fileOk_no` (Johnson/AtFull/ProofPlan/At/No/FileOk.lean), reads the
field back that the bent value sets: it names no routine and could not have failed. This one asks
the routine: it would fail if `planOk` did not read the field.

One closed fact, by an evaluation in Lean's kernel (`decide +kernel`). The field is the first
conjunct of `planOkCore`, so the kernel need not evaluate the other tests.

Limits. A fact on a made-up value. It shows that `planOk` reads fileOk at this value, and no more.
Nothing on soundness.
-/
import Johnson.AtFull.ProofPlan.At.Bent2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc

/-- The tests on the plan say no where the field fileOk is false. -/
theorem wp_planOk_no_file : wpFile.planOk = false := by
  decide +kernel

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_planOk_no_file
