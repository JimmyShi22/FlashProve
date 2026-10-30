-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/FromPremises.lean: proofs of the two implications of
Johnson/FrontRoad/FromPremisesSpec.lean, which put this folder's theorems together at a variable
honest side.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
roadPrivate_of_premAll proves Spec.roadPrivate_of_premAll, and completeOn_of_honAll proves
Spec.completeOn_of_honAll. What the statements say, what they are not, and their limits, is in the
head of Johnson/FrontRoad/FromPremisesSpec.lean.

How it fits. roadPrivate_of_premAll calls threeOfId_of_laws (Johnson/FrontRoad/IdAlone.lean),
shown_privacy and shown_zeroKnowledgeOn (Johnson/FrontRoad/SlotShown.lean). completeOn_of_honAll
calls frontIdComplete_hon (Johnson/FrontRoad/CompleteK.lean) and shown_completeOn. Not among the
release's goal statements.

Limits. Those of Johnson/FrontRoad/FromPremisesSpec.lean.
-/
import Johnson.FrontRoad.FromPremisesSpec

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad

/-- **An implication: from the premises of index privacy at every value of the public reading.** The
only parameters that are known to satisfy them have two placeholder provers, which send fixed
messages. Proves Spec.roadPrivate_of_premAll. -/
theorem roadPrivate_of_premAll : Spec.roadPrivate_of_premAll :=
  fun D Z c₀ m₀ T pair F s idx x₀ back Form parse encF domain Yes ok ζ NC NP bound hL hP hζ hok htie
      hNC hNP hr =>
    have three := threeOfId_of_laws D Z c₀ m₀ T F s idx x₀ back Form parse encF
      (shownRel D s domain) pair hL Yes ok ζ NC NP hP hζ hok
      (fun w x' h => htie w x'.1 x'.2 h.1 h.2) hNC hNP
    ⟨three,
      shown_privacy D Z c₀ m₀ T F.side s idx x₀ Form parse encF bound (shownRel D s domain) _ _
        hL.noCoin hr three.privacy,
      shown_zeroKnowledgeOn D Z c₀ m₀ T F.side s idx x₀ Form parse encF bound domain _ _ hL.noCoin
        hr three.privacy⟩

/-- **An implication: from the premises of completeness at every value of the public reading.** No
parameters with content are known to satisfy them. Proves Spec.completeOn_of_honAll. -/
theorem completeOn_of_honAll : Spec.completeOn_of_honAll :=
  fun D Z c₀ m₀ T pair F G s idx x₀ back Form parse encF domain Yes α bound hL scope hH hα hU htie
      hr =>
    shown_completeOn D Z c₀ m₀ T F.side s idx x₀ Form parse encF bound domain α hL.noCoin hr
      (frontIdComplete_hon D Z c₀ m₀ T F G Yes α s idx x₀ Form parse encF pair D.Shown
        (shownRel D s domain) hL.noCoin hL.asks hL.once hL.spare
        (fits_of_eq D Z c₀ m₀ T pair hL.eq) hL.reads scope hU hL.total hH hα fun w x' h => by
          obtain ⟨x, hb, hy, -⟩ := htie w x'.1 x'.2 h.1 h.2
          exact ⟨x, hb, hy⟩)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.roadPrivate_of_premAll
#print axioms OnBytes.FrontRoad.completeOn_of_honAll
