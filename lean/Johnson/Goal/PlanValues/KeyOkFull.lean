-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/PlanValues/KeyOkFull.lean: the test on a key's values together (Plan.keyOk, which is
Key.fixedOk, OnBytes/Key/Fixed.lean) says yes at the typed sizes of a key of full size (keyFull,
Johnson/Goal/PlanValues/KeySizedReturns.lean).

The planner refuses unless that test says yes, and the check of a key file asks the same test of the
parameters that it has read (Key.admitted). Its nine clauses are evaluated here by Lean's kernel,
but for the second (Wf.admitted), which is admitted_full of KeySizedReturns.lean.

Main names.
  keyOk_rest    the eight other clauses.
  keyOk_full    Plan.keyOk keyFull = true.
  adm_full_road so the two lookups' records are admissible by the road through the test
                (Lk6.adm_at_keyOk), with no premise left.

Limits. The typed sizes alone. That the three plans of a key's chains are made is not shown. Nothing
on soundness.
-/
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Params OnBytes.Plan
open Johnson.Top.H (csKey)

set_option maxRecDepth 1000000 in
/-- The clauses of the test beside Wf.admitted. -/
theorem keyOk_rest : (linOk csKey keyOnceRec.shape && keyFull.binding.logLeaves == 0 &&
    keyX.messageId == 1 && keyOnceRec.input.shape.mainRows == 0 &&
    keyOnceRec.input.shape.maskRows != 0 && decide (1 ≤ keyOnceRec.input.shape.answers) &&
    decide (keyOnceRec.input.shape.maskCode < csKey.mask.size) &&
    decide (Wf.indexMaskEntries keyX (Wf.matrixOf keyOnceRec.shape) ≤
      Send.freeMaskEntries keyOnceRec.input.shape.maskRows
        (csKey.mask.getD keyOnceRec.input.shape.maskCode default).ell
        keyOnceRec.input.shape.answers)) = true := by decide +kernel

/-- **The test on a key's values together says yes at the typed sizes.** -/
theorem keyOk_full : keyOk keyFull = true := by
  have r := keyOk_rest
  have a : Wf.admitted csKey keyX (Wf.matrixOf keyOnceRec.shape) = true := admitted_full
  simp only [Bool.and_eq_true] at r
  unfold keyOk Key.fixedOk
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨r.1.1.1.1.1.1.1, a⟩, r.1.1.1.1.1.1.2⟩, r.1.1.1.1.1.2⟩, r.1.1.1.1.2⟩, r.1.1.1.2⟩,
    r.1.1.2⟩, r.1.2⟩, r.2⟩

/-- So the records of the two lookups are admissible by the road through the test: no premise. -/
theorem adm_full_road :
    ∀ S ∈ Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape), (pubOf S).Adm Cb.Gl.p :=
  adm_at_keyOk keyOk_full

end Lk6.AtPlan

#print axioms Lk6.AtPlan.keyOk_full
#print axioms Lk6.AtPlan.adm_full_road
