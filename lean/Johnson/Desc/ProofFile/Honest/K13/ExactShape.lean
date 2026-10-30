-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/ExactShape.lean: beside Exact.lean of this folder: the hypothesis
on the call's shape (hk : `shapeOk (k13Shape kCol) = true`) at the two sizes. Statements with their
proofs. It is a file of its own so that Exact.lean does not import the library's files on the goals'
scope.

  `shape_at_11`, `shape_at_18`   at the two sizes' numbers of column bits, by Lean's kernel
  `shape_in_scope`   in the goals' scope, at the place's own public data

Limits.
  * `shape_at_11` is at the number alone: that the small size's public data have 11 column bits is
    not shown here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.Exact
import Johnson.Desc.Sound.K11Tests.PendAllNoPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)

/-- At 11 variables, the small size's number, the shape passes. -/
theorem shape_at_11 : shapeOk (k13Shape 11) = true := by decide

/-- At 18 variables, the full size's number, the shape passes. -/
theorem shape_at_18 : shapeOk (k13Shape 18) = true := by decide

/-- **In the goals' scope the shape at the place's own public data passes**: there the matrix has 18
column bits (`lin_in_scope`, Johnson/Desc/Sound/K11Tests/PendAllNoPin.lean). -/
theorem shape_in_scope {Q : VerifierAndGoals.PublicFiles} {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}
    (hS : VerifierAndGoals.InScope Q = true) (h : ProofFile.pureRoad.pub o Q.pol Q.lay Q.KL = .ok Z) :
    shapeOk (k13Shape (whereOf Z).lin.kCol) = true := by
  have e : (whereOf Z).lin.kCol = 18 := (LT28.K11Tests.lin_in_scope hS h).2
  rw [e]
  exact shape_at_18

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.shape_at_11
#print axioms ProofFile.Honest.K13.shape_at_18
#print axioms ProofFile.Honest.K13.shape_in_scope
