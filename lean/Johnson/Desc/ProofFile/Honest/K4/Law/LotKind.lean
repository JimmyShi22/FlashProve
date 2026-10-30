-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/LotKind.lean

What is here. Every half that the honest side of the lot of the layers' own rounds (`k4HLot`,
Honest/K4/Part.lean) lays stands at a place of the kind K4: at every public part, all segments'
data, and all of the lot's parameters. So this lot has no half at a place of another kind; with the
like statement of each other lot it serves to show, for all lots of a filling at once, that none but
this one has a half at a place of this kind. One statement with its proof: membership in the lot's
list written out; the place of a half is `k4Place Q`, whose kind is written there.

  `k4HLot_kind`: for every x among (k4HLot cells weights look).halves Z G: x.place.kind = .K4.

Limits. It says nothing on WHICH places have a half, on how many there are, or on what a half
holds: where the lot's list is empty it holds of nothing. It says nothing of any other lot.
Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest

variable {W₀ Rc Tr X : Type}

/-- **Each half of K4's lot stands at a place of the kind K4.** -/
theorem k4HLot_kind (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Z : Pub)
    (G : Ground) :
    ∀ x ∈ (k4HLot (Rc := Rc) (X := X) cells weights look).halves Z G, x.place.kind = .K4 := by
  intro x hx
  simp only [k4HLot, List.mem_filterMap, Option.map_eq_some_iff] at hx
  obtain ⟨_, _, Q, _, rfl⟩ := hx
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4HLot_kind
