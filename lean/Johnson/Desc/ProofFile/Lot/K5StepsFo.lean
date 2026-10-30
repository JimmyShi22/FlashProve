-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Lot/K5StepsFo.lean: kind K5's lot (Johnson/Desc/ProofFile/Lot/K5.lean: H2K5.lotN): EVERY BLOCK OF IT STEPS: where its decision says yes, what the lookup on the calls was heard to return stands, and
the segment's ledger is a later one with its sizes. By Johnson/Desc/First/Att/K05StepsFo.lean's k5AtN_stepsFo: the lot's one more test on the plan leaves the decision.

Main names: k5OwnN_stepsFo · lotN_stepsFo.
IS IT EMPTY HERE? Where the lot has no block, or a decision refuses, nothing is said. planOk = true is not spent.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Lot.K5
import Johnson.Desc.First.Att.K05StepsFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5
open ProofFile
open VerifiableInference.Desc (Block CarriesFo)
open VerifiableInference.Desc.First

theorem k5OwnN_stepsFo {Z : Pub} {G : Ground} {b₁ : Block S Cl} (h : b₁ ∈ k5OwnN Z G) :
    b₁.planOk = true → b₁.Steps (CarriesFo S.fork? S.lookHeard?) := by
  intro _
  unfold k5OwnN at h
  obtain ⟨x, _, e⟩ := List.mem_filterMap.1 h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 e
  unfold Att.P.k5AtN at hb
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact fun s rs _ s' hd => Att.P.k5_decide_stepsFo _ hd

/-- **Every block of K5's lot steps.** -/
theorem lotN_stepsFo {Z : Pub} {G : Ground} {b₁ : Block S Cl} (h : b₁ ∈ (lotN Z).blocks G) :
    b₁.planOk = true → b₁.Steps (CarriesFo S.fork? S.lookHeard?) :=
  k5OwnN_stepsFo (by simpa [Lot.blocks, lotN, asCl] using h)

end H2K5

#print axioms H2K5.k5OwnN_stepsFo
#print axioms H2K5.lotN_stepsFo
