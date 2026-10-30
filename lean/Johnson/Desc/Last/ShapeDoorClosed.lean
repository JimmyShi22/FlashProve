-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorClosed.lean: TWO OF THE SEVEN PREMISES OF `DoorStays`
(Johnson/Desc/Last/ShapeDoorFold.lean), AT THE FULL SIZE'S WRITTEN LISTS, GENERAL IN THE NUMBERS:
the index masks' message's seat and W's seat are among the sampled tenants of the items that are
open at the first chain's last border. Statements with their proofs; one test with code.

Main names (namespace `VerifiableInference.Desc.Last`).
  `lastPinsB links ps`: the test: `pinI` and `pinV` are among the items open at border `ps.length`.
    `lastPinsB_full`: it accepts at `Sound.linksFull` and its written list of places: BY LEAN'S
    KERNEL. `last_pins_full`: the two memberships.
  **`index_sampled_full`**, **`w_sampled_full`**: for every N: `N.index` and `N.w` are in `sampledIn
    N` of these items: `DoorStays`' fields indexIn and wIn at V.index := N.index, V.w := N.w.

Every "there is": none.
Limits. A closed fact on the table's rows at the full size's list of segments; it says nothing of a
run. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First (ModelPart Item Numbers openSets sampledIn flatPlacesOf)

/-- The test: the two last pins are among the items open at the chain's last border. -/
def lastPinsB (links : List ModelPart) (ps : List Place) : Bool :=
  decide (Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD []) &&
    decide (Item.pinV ∈ (openSets links ps (First.start links))[ps.length]?.getD [])

theorem lastPinsB_full : lastPinsB linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

theorem last_pins_full :
    Item.pinI ∈ (openSets linksFull (flatPlacesOf linksFull true)
        (First.start linksFull))[(flatPlacesOf linksFull true).length]?.getD [] ∧
      Item.pinV ∈ (openSets linksFull (flatPlacesOf linksFull true)
        (First.start linksFull))[(flatPlacesOf linksFull true).length]?.getD [] := by
  have h := lastPinsB_full
  unfold lastPinsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- **The index masks' message's seat is sampled at the last border.** -/
theorem index_sampled_full (N : Numbers) :
    N.index ∈ sampledIn N ((openSets linksFull (flatPlacesOf linksFull true)
      (First.start linksFull))[(flatPlacesOf linksFull true).length]?.getD []) :=
  List.mem_flatMap.2 ⟨_, last_pins_full.1, List.mem_singleton.2 rfl⟩

/-- **W's seat is sampled at the last border.** -/
theorem w_sampled_full (N : Numbers) :
    N.w ∈ sampledIn N ((openSets linksFull (flatPlacesOf linksFull true)
      (First.start linksFull))[(flatPlacesOf linksFull true).length]?.getD []) :=
  List.mem_flatMap.2 ⟨_, last_pins_full.2, List.mem_singleton.2 rfl⟩

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.lastPinsB_full
#print axioms VerifiableInference.Desc.Last.last_pins_full
#print axioms VerifiableInference.Desc.Last.index_sampled_full
#print axioms VerifiableInference.Desc.Last.w_sampled_full
