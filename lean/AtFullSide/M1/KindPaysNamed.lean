-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what the kind K1 pays at the files that ship.
/-
AtFullSide/M1/KindPaysNamed.lean: `K1PaysAtFiles` at the two named sets of files, with no premise. Left
inside it, as hypotheses: `hG`, `hk`, `book`, `rows`. `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` are three terms
each, with synthetic weights. No property of the protocol is claimed here.
-/
import AtFullSide.M1.KindPaysK1
import AtFullSide.Bind.LiveAtNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.M1

/-- **At the named files.** -/
theorem kindPays_K1_named (Z : VerifierAndGoals.PublicFiles) (hN : VerifierAndGoals.NamedFiles Z) : K1PaysAtFiles Z := by
  rcases hN with rfl | rfl
  · obtain ⟨sc, ⟨pp, hr⟩, hl⟩ := AtFullSide.Tie.premises_zFull
    exact kindPays_K1_live _ sc hr hl
  · obtain ⟨sc, ⟨pp, hr⟩, hl⟩ := AtFullSide.Tie.premises_zGap
    exact kindPays_K1_live _ sc hr hl

end AtFullSide.M1

#print axioms AtFullSide.M1.kindPays_K1_named
