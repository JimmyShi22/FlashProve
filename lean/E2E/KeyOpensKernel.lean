-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyOpensKernel.lean

What the rounds of the key file's shared chain open against what is in hand, at borders 10, 11, 12,
BY THE KERNEL's OWN EVALUATION. It imports KeyOpensGuards.lean, where the evaluator says the same
first.

  `opens_ten`, `opens_eleven`, `opens_twelve`   the test says yes
  `opens_bent_hand`, `opens_bent_trees`   controls: a round that opens what the hand lacks; member 9
                 with no tree: no

Limits. Closed numbers at `QK`, `PF`. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyOpensGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyOpens

theorem opens_ten : opensR keyR 10 = true := by decide +kernel

theorem opens_eleven : opensR keyR 11 = true := by decide +kernel

theorem opens_twelve : opensR keyR 12 = true := by decide +kernel

theorem opens_bent_hand : opensR bentHand 10 = false := by decide +kernel

theorem opens_bent_trees : opensR bentTrees 10 = false := by decide +kernel

end AtPublicFiles.KeyOpens

#print axioms AtPublicFiles.KeyOpens.opens_ten
#print axioms AtPublicFiles.KeyOpens.opens_eleven
#print axioms AtPublicFiles.KeyOpens.opens_twelve
#print axioms AtPublicFiles.KeyOpens.opens_bent_hand
#print axioms AtPublicFiles.KeyOpens.opens_bent_trees
