-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/OfPins.lean: r2 AND r3 OF THE KEY FILE's BACK AT THE WRITTEN VALUES, FROM THE
PINS AND FOUR CLOSED FACTS ON THE TREES. Calls alone: AtPins.lean and `treesK_at_pins`
(TreesKAtPins.lean), which pays `treesSent`'s three returns from the pins.

What stays as premises:
  `KeyPins m` (Pins.lean): what the routines read of m is the full size's written value. SHOWN AT NO
    m HERE.
  `FirstA`, `FoldedB`, `OmegaB`, `OwnAB` (TreeProps.lean): four closed propositions on the trees of
    the written sendings. NOT SHOWN HERE.
  `treesOf_length`, `six_A`: the first chain sends six trees: paid, by the list of its trees' rounds
    (`rounds_A`, RoundsA.lean).
  `rangesNumbers_of_pins`: `Key.rangesNumbers m = .ok Johnson.KB8.rangesNumsFull`, from the pins and
    `FirstA`.
  `laterPlaces_of_pins`: `Key.laterPlaces m = .ok Johnson.KB8.laterPlacesFull`, from the pins and
    the other three.
Limits. No m is shown at which `KeyPins` holds. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.AtPins
import Johnson.AtFull.KeyBack.TreeProps
import Johnson.AtFull.KeyBack.TreesKAtPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends keySends0 keySends1 keySends2)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)
open Johnson.Unfolds (ok_of_isOk)

/-- A chain has as many trees as the list of its trees' rounds has members. -/
theorem treesOf_length {c : ChainSends} {P : Fmt.Plan} {e : List Sent} {off : Nat}
    (h : ChainFits c P e off) : (treesOf c off e).length = (roundsOfChain c off e).length := by
  rw [← sortedW_rounds e (ok_of_isOk [] h.sent), List.length_map]
  exact List.length_zipIdx

/-- The first chain sends six trees. -/
theorem six_A : treesA.length = 6 := by
  rw [treesOf_length fits_A, rounds_A]
  rfl

/-- **r2 at the written value, from the pins and one closed fact.** -/
theorem rangesNumbers_of_pins (m : Made) (h : KeyPins m) (hfirst : FirstA) :
    rangesNumbers m = .ok Johnson.KB8.rangesNumsFull :=
  rangesNumbers_at_pins m treesA h ((treesK_at_pins m h).first _) hfirst

/-- **r3 at the written value, from the pins and three closed facts.** -/
theorem laterPlaces_of_pins (m : Made) (h : KeyPins m) (hfU : FoldedB) (hfO : OmegaB)
    (hfW : OwnAB) : laterPlaces m = .ok Johnson.KB8.laterPlacesFull :=
  laterPlaces_at_pins m treesA treesB treesC h ((treesK_at_pins m h).first _)
    ((treesK_at_pins m h).shared _) ((treesK_at_pins m h).second _) hfU hfO hfW six_A

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.treesOf_length
#print axioms Johnson.AtFull.KeyBack.six_A
#print axioms Johnson.AtFull.KeyBack.rangesNumbers_of_pins
#print axioms Johnson.AtFull.KeyBack.laterPlaces_of_pins
