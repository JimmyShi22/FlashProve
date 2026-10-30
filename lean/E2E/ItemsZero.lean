-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/ItemsZero.lean: `ItemsZero F`: every stored table that a round of the description F declares
stands under the item 0. It holds wherever the description has data.

  `ItemsZero F`: a definition: the hypothesis hz of `ProofFile.Honest.tied_atItem`
    (Johnson/Desc/ProofFile/Honest/Law/Rule/TiedAtItem.lean) at the item 0, to the letter
  `itemsZero_of_data`: it holds wherever `F.data` returns

By what. `OnBytes.FrontRoad.declared_stored` (Johnson/FrontRoad/StoredItemZeroDeclared.lean): where
`F.data` returns, the first and the last chain declare no stored table, and each that the shared
chain declares stands under the item 0.

Limits. A sentence on public declarations. That `F.data` returns is a hypothesis. No property of a
protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.FrontRoad.StoredItemZeroDeclared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtZero
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (WholeD)

/-- Every stored table that a round of the description declares stands under the item 0. -/
def ItemsZero {Xi : Type} (F : FileDescription Xi) : Prop :=
  ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, s.item = 0

/-- It holds wherever the description has data. -/
theorem itemsZero_of_data {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) : ItemsZero F := by
  obtain ⟨h1, h2, h3⟩ := OnBytes.FrontRoad.declared_stored h
  intro d hd s hs
  rcases List.mem_append.1 hd with hd | hd
  · rcases List.mem_append.1 hd with hd | hd
    · rw [h1 d hd] at hs
      exact absurd hs List.not_mem_nil
    · exact h2 d hd s hs
  · rw [h3 d hd] at hs
    exact absurd hs List.not_mem_nil

end AtPublicFiles.AtZero

#print axioms AtPublicFiles.AtZero.ItemsZero
#print axioms AtPublicFiles.AtZero.itemsZero_of_data
