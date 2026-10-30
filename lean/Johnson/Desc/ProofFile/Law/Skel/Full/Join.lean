-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Join.lean: THE JOIN AT THE FULL SIZE: four of the seven steps
of `ProofFile.onlineDescriptionFromPublicPart`'s back (no fault; nothing lacking; the blocks at the places; the first chain), WITH
THE VALUES' SKELETONS, from rows on the public part and the lots. A statement and its proof.
  `back_at_full`: `back_of_written` (SkelWritten.lean) at the written data, its four closed facts
    paid by Full/Fact2.lean … Fact5.lean
WHAT STAYS A PREMISE, each by name: h₁ the places, h₂ the shape, h₃ the batchings' places, h₄ the
segments' sorts are the written ones; hB the base's blocks are the lots' (`baseOf`'s own text); hL
the lots are Ls; hR A ROW A LOT, in the lots' order (`RowAt`, Full/Ask.lean); hS `Steady` at every
lot; h₆ h₇ the two later seats' names and stand-ins are the written ones.
Limits. NONE OF THESE IS PAID HERE. A skeleton is blind to a block's decision, to its rounds'
entries and to the guards: the conclusion says that the four steps return, and which skeletons the
values have; not what the chain tests. The full size alone. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Fact2
import Johnson.Desc.ProofFile.Law.Skel.Full.Fact3
import Johnson.Desc.ProofFile.Law.Skel.Full.Fact4
import Johnson.Desc.ProofFile.Law.Skel.Full.Fact5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem back_at_full (Z : Pub) (T : PureSeat) (B : PureBase) (Ls : List Lot)
    (h₁ : B.spots = spotsW) (h₂ : B.shape = shapeW) (h₃ : B.batchAt = batchAtW)
    (h₄ : subsOf Z = subsW)
    (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hL : T.lots = Ls) (hR : List.Forall₂ (RowAt B.G₀) Ls wsW)
    (hS : ∀ L ∈ T.lots, Steady B.G₀ L)
    (h₆ : (T.shared.map fun A => (A.lot, A.standIns)) = sharedW)
    (h₇ : (T.second.map fun A => (A.lot, A.standIns)) = secondW) :
    faultsAt T B = [] ∧ lackingAt T (partsAt T B) = [] ∧
      ∃ base, (partsAt T B).base = .ok base ∧ base.map skel = baseW ∧
        ∃ c, chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c ∧
          c.blocksInOrder.map skel = flatW := by
  refine back_of_written Z T B wsW baseW flatW hB ?_ hS ?_ ?_ ?_ ?_
  · rw [h₁, h₃, h₄, hL]
    exact rows_join B.G₀ hR
  · rw [h₁, h₂, h₃]
    exact List.isEmpty_iff.1 c2_full
  · rw [h₁, h₂, h₃, h₆, h₇]
    exact List.isEmpty_iff.1 c3_full
  · rw [h₁]
    exact okIs_ok c4_full
  · rw [h₁, h₂, h₄]
    exact okIs_ok c5_full

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.back_at_full
