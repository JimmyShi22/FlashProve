-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3CallsTests.lean: THE LOOKUP ON A LINK's CALLS: FIVE OF THE TESTS ON THE
TABLE OF JOINTS THAT CallsLeftR, AttRestR, LayRestR (Johnson/Desc/Sound/MgAt/K3CallsLeftR.lean,
K3CallsRestR.lean) ASK, AT THE FULL SIZE's WRITTEN LIST AND THE COMPOSED MEANING's CLOSED LIST OF
EXTRA PUBLIC TESTS (mgMore): the place at the border, the place behind (next), the two stand alike
(stand), the pin of moment 0 is open in front (pin), linkFresh is open in front (fresh). The first,
second, fourth and fifth are calls of other files' lemmas (places_are_k3, next_place,
pin_open_calls, k3_open_calls: Johnson/Desc/Sound/MgAt/K3Open.lean, K3Pins.lean); stand is stand_at
(MgAt/K3CallsStand.lean). It reads no state of the verifier. NO SOUNDNESS IS CLAIMED.

OBJECT: the table of joints: no sub-protocol's text.
Used by K03MaskSeatAt.lean, K03MergeIdleAt.lean, K03OthersPAt.lean (Johnson/P5J/) and 1 more.
LETTERS: l: a segment below 25.

Main names: `kOfCalls_border` · `calls_tests`.

Limits. The full size's list and mgMore alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsTable
import Johnson.Desc.Sound.MgAt.K3CallsStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound.MgAt (borderOf ixOf placeOf nextOf places_are_k3 next_place
  pin_open_calls k3_open_calls itemsAt openAt)
open VerifiableInference.Desc.First (Item Pub flatPlacesOf pubSets openSets start sameStand)

/-- The border's number is `borderOf`'s (Johnson/Desc/Sound/MgAt/K3Open.lean). -/
theorem kOfCalls_border (l : ℕ) : kOfCalls l = borderOf l false := by
  unfold kOfCalls borderOf ixOf
  by_cases h : l = 24
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- **The five, at a segment.** -/
theorem calls_tests {l : ℕ} (hl : l < 25) :
    (flatPlacesOf linksFull true)[kOfCalls l]? = some (placeOf l false) ∧
      (flatPlacesOf linksFull true)[kOfCalls l + 1]? = some (nextOf l false) ∧
      sameStand linksFull (placeOf l false) (nextOf l false) = true ∧
      Item.pin l 0 ∈ (openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[kOfCalls l]?.getD [] ∧
      Pub.linkFresh l ∈
        (pubSets mgMore linksFull (flatPlacesOf linksFull true))[kOfCalls l]?.getD [] := by
  rw [kOfCalls_border]
  exact ⟨places_are_k3 hl false, next_place hl false,
    stand_at hl, pin_open_calls hl,
    (k3_open_calls hl).2.2⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.kOfCalls_border
#print axioms VerifiableInference.OnPublicFiles.calls_tests
