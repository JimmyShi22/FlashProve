-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/NuOfPlace.lean: AT A STATE
WHOSE BOOK OF TREES IS IN ORDER, THE PROXIMITY TEST'S NUMBERING BY LABEL IS THE BOOK'S PLACE: nuOf
(Johnson/Desc/K12/Coin/GameLabels.lean) sends a place z of the book to the number, through the file,
of the tree whose label stands there; where the test's mask is there already (so that the test's own
book is the state's), the chain's trees begin at 0, and the book is in order from 0 (bookStepB,
Johnson/Desc/Sound/BookOrder.lean), that number is z itself.

Main names:
  nuOf_is_place.

Object: nuOf at nl := nlAt π 0 (Johnson/Desc/K12/Coin/GameLabelsO.lean). User: Word15.lean calls
nuOf_is_place (for the field r1_15).
Letters: π, the test's place · t, its state · a, rest, G0, Ly, D: what Fixes binds. Premises: Fixes
π t a rest G0 Ly D · the mask is there · π.nums.firstTree = 0 · bookStepB 0 t.book t.roots = true ·
z is a place of the book.

Limits. One equation. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.GameLabelsO
import Johnson.Desc.K12.Coin.FirstBook
import Johnson.Desc.Sound.BookInOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.NuOfPlace
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin
open H2K.First (Plain)

/-- **The numbering by label is the book's place.** -/
theorem nuOf_is_place (π : P12) (t : T12) {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
    {Ly : GroupLayout} {D : Plain} (hf : Fixes π t a rest G0 Ly D) (hmk : t.mask.isSome = true)
    (hft : π.nums.firstTree = 0) (hb : bookStepB 0 t.book t.roots = true) (z : ℕ)
    (hz : z < t.book.trees.size) : nuOf π (nlAt π 0) t z = z := by
  rw [nuOf_of_fixes hf, book_of_fixes π t hmk a rest G0 Ly D hf]
  unfold nlAt H2K.First.numAt
  have hB := ((bookStep_iff 0 t.book t.roots).1 hb).2
  have hT : t.book.trees[z]? = some t.book.trees[z] := Array.getElem?_eq_getElem hz
  rw [hft, hT, Option.map_some, Option.getD_some, hB z _ hT]
  omega

end Johnson.RunOne.Law.NuOfPlace

#print axioms Johnson.RunOne.Law.NuOfPlace.nuOf_is_place
