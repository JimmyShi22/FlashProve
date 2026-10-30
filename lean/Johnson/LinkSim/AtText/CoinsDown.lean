-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/CoinsDown.lean: a shift of the coins that can be undone carries over from the
coins that the prover's algorithm reads to the finite type of the link prover's random values.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. The theorem downToCoins moves the property "agree up to a shift of the coins
that can be undone" (UpToShift, defined in Johnson/LinkSim/UpTo.lean) from the coins (LCoins) to the
finite type of random values (LinkK).
  downToCoins  Let P be the link proof's public parameters (P15), with a list of stages that is
               not empty, S sizes (Sz), and f, g any two functions on LCoins. Suppose f and g
               agree up to a shift that can be undone, at every c that is 0 outside the places,
               with a shift that is also 0 outside the places
               (UpToShiftOn addC (InPlaces P S) (InPlaces P S) f g). Then f and g composed with
               coinsOf agree up to a shift that can be undone, for the sum addLink on LinkK.
The places are defined in Places.lean (InPlaces).

How it fits. The proof applies UpToShiftOn.comap (Johnson/LinkSim/UpToOn.lean) to coinsOf, with four
of its properties: coinsInj and coinsAdd (CoinsAdd.lean), coinsIn and coinsOnto (CoinsPlaces.lean).
Johnson/LinkSim/AtHome/RoadCloses.lean applies downToCoins at the full-size parameters.

Limits.
- The theorem is an implication, and nothing here says when its premise holds.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.CoinsPlaces
import Johnson.LinkSim.UpToOn

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice
open _root_.Desc.K15 (P15 p12Of)
open Johnson.Prover.Link

/-- From LCoins down to LinkK: a shift of the coins that can be undone, within the places, gives one
on LinkK for f and g composed with coinsOf. -/
theorem downToCoins {V : Type} (P : P15) (S : Sz) (hne : (p12Of P).nums.stages ≠ [])
    (f g : LCoins → V) (h : UpToShiftOn addC (InPlaces P S) (InPlaces P S) f g) :
    UpToShift (addLink S (p12Of P).nums.stages)
      (fun k => f (coinsOf S (p12Of P).nums.stages k))
      (fun k => g (coinsOf S (p12Of P).nums.stages k)) :=
  haveI : Nonempty (LinkK GE S (p12Of P).nums.stages) := LinkK.nonempty 0 S _
  UpToShiftOn.comap (coinsOf S (p12Of P).nums.stages) (coinsInj S _) (coinsAdd S _) (coinsIn P S)
    (fun c hc => coinsOnto P S c hne hc) h

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.downToCoins
