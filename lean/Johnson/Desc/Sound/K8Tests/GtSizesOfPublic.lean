-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K8Tests/GtSizesOfPublic.lean: THE TEST WITH CODE Second.K08.gtSizesAllB
(Johnson/Second/K08/GtSizesAt.lean: at every planned value of the approximate range proof there are
just as many numbers of symbol arrays as matrices) SAYS YES AT EVERYTHING THAT THE VERIFIER's OWN
publicOf RETURNS: at all public files, in the goals' scope or not. One statement with its proof;
nothing is evaluated at particular files.

  gtSizesAllB_of_public   publicOf pol KL lay = .ok X → Second.K08.gtSizesAllB X = true

How. The equation gtTree.size = NM is the first half of GtU
(Johnson/Desc/Sound/K8Tests/PlanFitsOfPublic.lean): made by HTailF2.shapeF's third loop, kept by
what follows it in the three plans.

Limits. The premise is that publicOf returns: that it does at any file is not said here. Nothing on
soundness.

-/
import Johnson.Desc.Sound.K8Tests.PlanFitsOfPublic
import Johnson.Second.K08.GtSizesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LT28.K8Tests

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)

/-- **THE TEST SAYS YES AT EVERYTHING THAT publicOf RETURNS.** -/
theorem gtSizesAllB_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : publicOf pol KL lay = .ok X) : Second.K08.gtSizesAllB X = true := by
  unfold Second.K08.gtSizesAllB
  simp only [Bool.and_eq_true, Array.all_eq_true, beq_iff_eq]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, (both_head h).2.1⟩
  · exact (both_layers h (Array.getElem?_eq_getElem hi)).2.1
  · exact (both_attention h (Array.getElem?_eq_getElem hi)).2.1

end LT28.K8Tests

#print axioms LT28.K8Tests.gtSizesAllB_of_public
