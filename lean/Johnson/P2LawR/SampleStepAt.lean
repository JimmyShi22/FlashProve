-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SampleStepAt.lean: THE LAST STEP OF THE EARNING OF sampleAtB (`P2Law.SampleStep`,
Johnson/P2LawR/SampleBehind.lean) AT THE LAST TABLE's TWO SHAPES, UNDER `madeRow Z`. Two theorems:
each is one call.

  `sampleStep_at_W`: `∀ o, SampleStep (p14At Z).codes (p14At Z).S.w o`: `IM.sampleL_at_W`
    (Johnson/IMR/SampleAtW.lean).
  `sampleStep_at_index`: the like at the shape of the request's first message at the start:
    `IM.sampleL_at_index`.
They are the premises hL₂ and hL₁ of `sampleTwoB_h4_paid` (Johnson/ToldDescR/SampleTwoOpen.lean) at
cs := `(p14At Z).codes` and at these two shapes.

Limits. `madeRow Z = true` is a premise. That `(LLT25.vAt Z N₁).wShape` and `.indexShape` are
these two shapes is by that definition's text; it is not imported here. Nothing on soundness.

-/
import Johnson.P2LawR.SampleBehind
import Johnson.IMR.SampleAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law
open VerifiableInference.PlanWritten (madeRow)
open ToldDesc (p14At)

/-- **The last step at W.** -/
theorem sampleStep_at_W {Z : ProofFile.Pub} (hy : madeRow Z = true) :
    ∀ o, SampleStep (p14At Z).codes (p14At Z).S.w o :=
  fun o x seed row0 tt β hs hf hr hl hb => IM.sampleL_at_W hy o x seed row0 tt β hs hf hr hl hb

/-- **The last step at the index masks' message.** -/
theorem sampleStep_at_index {Z : ProofFile.Pub} (hy : madeRow Z = true) :
    ∀ o, SampleStep (p14At Z).codes
      ((Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) o :=
  fun o x seed row0 tt β hs hf hr hl hb => IM.sampleL_at_index hy o x seed row0 tt β hs hf hr hl hb

end P2Law

#print axioms P2Law.sampleStep_at_W
#print axioms P2Law.sampleStep_at_index
