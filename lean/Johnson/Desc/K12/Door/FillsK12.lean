-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/FillsK12.lean: **THE PROXIMITY TEST's FILES' PREMISES ON A LETTER Mg, IN ONE
STRUCTURE.** One structure, one theorem; no Mathlib. A light file of its own, over the layer alone,
so that "these premises hold at the composed meaning"
need not import the laws that spend them (Johnson/Desc/K12/Coin/HandsOnBools.lean).
  `FillsK12 Mg d`: at the layer's four names `Mg.pub` is the layer's Bool at the data d (ft · L ·
    M).
  `fillsK12_at`: it holds at `fillK12 d Mg`, whatever Mg: four times by definition.
Nothing on soundness.

-/
import Johnson.Desc.K12.Door.FillK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open VerifiableInference.Desc.First (Meaning)

/-- **The premises on Mg.** -/
structure FillsK12 {P W : Type} (Mg : Meaning P W) (d : K12Data) : Prop where
  book : ∀ a, Mg.pub (First.moreItem nBook) a = atFirstBook d.ft a.2
  seats : ∀ a, Mg.pub (First.moreItem nSeats) a = atFirstSeats d.L a.2
  shapes : ∀ a, Mg.pub (First.moreItem nShapes) a = atFirstShapes d.M a.2
  fits : ∀ a, Mg.pub (First.moreItem nFits) a = atFirstFits a.2

theorem fillsK12_at {P W : Type} (d : K12Data) (Mg : Meaning P W) : FillsK12 (fillK12 d Mg) d :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end VerifiableInference.Desc.K12.Door

#print axioms VerifiableInference.Desc.K12.Door.fillsK12_at
