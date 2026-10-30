-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/Full.lean: THE KERNEL's WORD AT THE FULL SIZE's LISTS: the three tests under
which `riders_are` (Riders/Proofs.lean) says which sorts of item ride at K4's row ARE TRUE at the
full size's list of segments and its written list of places (`linksFull`,
Johnson/Desc/Sound/AtDriver.lean; `flatPlacesOf`, Johnson/Desc/First/Driver/Chain.lean). Then the
sorts, at these lists, under no test. Statements and proofs: evaluation by Lean's kernel; one call.

  `k4_riders_full` · `reads_open_full` · `rows_apart_full`: the three tests say yes.
  **`riders_full`**: at the full lists: an item that is open in front of K4's sub-protocol at piece
    3 of a feed-forward segment m, and that its row neither closes nor reads, is pile, or constr j p
    at a later segment j > m, or row m c at the classes carried | position | sample 0, or formsT m 2
    "objects".

Limits. AT THE TABLE OF JOINTS' ROWS AS THIS FILE IMPORTS THEM: a turn of a row turns the
evaluation. The full size alone. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Road.K4.Riders.Proofs
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (Item start readsOpen flatPlacesOf)
open VerifiableInference.Desc.Sound (insQ outsQ openAfter rowsApart linksFull)

set_option maxRecDepth 1000000 in
theorem k4_riders_full : k4RidersFit linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem reads_open_full :
    readsOpen linksFull (flatPlacesOf linksFull true) (start linksFull) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rows_apart_full : rowsApart linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

/-- **Which sorts ride at K4's row, at the full lists.** -/
theorem riders_full {k m : ℕ} {pl : Place}
    (H : AtK4 linksFull (flatPlacesOf linksFull true) k m pl) (i : Item)
    (ho : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) k i)
    (hi : ¬ insQ linksFull (flatPlacesOf linksFull true) k i) : riderSort m i = true :=
  riders_are linksFull (flatPlacesOf linksFull true) k m pl H k4_riders_full reads_open_full
    rows_apart_full i ho hi

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.k4_riders_full
#print axioms OnBytes.Road.K4.Riders.riders_full
