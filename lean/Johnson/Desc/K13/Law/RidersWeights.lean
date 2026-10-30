-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/RidersWeights.lean: THE TEST ON THE WEIGHTS RIDES PAST KIND K13's TWO BLOCKS:
`OwedKeeps` (Johnson/Desc/K13/Law/OwedSig.lean: a statement that kind K13's files write as
owed) at `First.weightsB` (Johnson/Desc/First/Pend/WeightsB.lean: the Bool behind the first table's
named item "K13.weightsOk"). One statement and its proof; no definition.

Main name (namespace `VerifiableInference.Desc.K13.Law`).
  **`weightsKeeps`** : `OwedKeeps First.weightsB`: over a step of the batching's block (`StepM3`)
    and over a step of W's commitment with the kind's block behind it (`StepM4`; both:
    Johnson/Desc/K13/Law/AtRecord.lean): if every weight vector of every row on the table passes
    `Tensor.ok` in front, so behind.

HOW. AT M:3 IT IS NOT CARRIED BUT MADE ANEW OUT OF ITSELF: the rows on the table turn there (the
pile in front; behind it the one row that the batching hands on): that row's vectors are the pile's,
each times a scalar (`Last.weights_atM3`, Johnson/Desc/K13/Law/WeightsKept.lean, by `atM3_ok`,
`batt_ok` and `scale_ok`): so it needs in front just itself. AT M:4 the rows on the table
are as they were (`atM4_rec`).
Limits. It speaks of the two steps as AtRecord.lean states them: that a chain holds these blocks is
not said here. The test is true for nothing where no row lies. That it holds in front of M:3 is owed
by the blocks in front. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.OwedSig
import Johnson.Desc.K13.Law.WeightsKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law

/-- **The test on the weights rides over both steps.** -/
theorem weightsKeeps : OwedKeeps First.weightsB := by
  refine ⟨fun P x x' h hw => ?_, fun P P' x x' h hw => ?_⟩
  · obtain ⟨rs, gs, hd⟩ := h.2
    exact Last.weights_atM3 hd hw
  · obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
    rw [First.weightsB_same (atM4_rec hd).2.2.2.2]
    exact hw

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.weightsKeeps
