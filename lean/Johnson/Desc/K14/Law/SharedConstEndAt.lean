-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstEndAt.lean: BEHIND ITS LAST SUB-PROTOCOL THE FIRST TABLE LEAVES OPEN
AT MOST "NO MARK", THREE PINS AND THE ONE CLAIM: the premise hEnd of Sh.rel_end_of_zero
(Johnson/Desc/K14/Law/SharedConstZero.lean), which is the field END of the structure
TablesFitR, to the letter. A TEST ON THE TABLE: no state, no key. Three bricks that lie are joined:
the rule's open set is a list (openIsList); where the table's two tests readsOpen and rowsApart
accept, that list has the members of the table's own list openSets (openL_iff_openSets; both
Johnson/Desc/Sound/SpineList.lean); and at the last border that list holds nothing but the five
(endOpenOnly, Johnson/Desc/K13/Law/OpenSetAtEnd.lean).

  Sh.hEnd_of      the join: general in the list of segments, under linksOk, the table's two tests,
                  and "no mark is open at the start".
  Sh.hEnd_full    **hEnd at the written list of the 25 segments** (Sh.linksFull): the four by Lean's
                  kernel.
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstLinksAt
import Johnson.Desc.K14.Law.SharedConstZero
import Johnson.Desc.K13.Law.OpenSetAtEnd
import Johnson.Desc.Sound.SpineList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)
open VerifiableInference.Desc.First (Item flatPlaces readsOpen linksOk)
open VerifiableInference.Desc.K13.Law (endOpenOnly)

namespace Sh

/-- The join, general in the list of segments. -/
theorem hEnd_of (links : List ModelPart) (hlk : linksOk links = true)
    (hr : readsOpen links (flatPlaces true links true) (start links) = true)
    (ha : rowsApart links (flatPlaces true links true) = true)
    (hu : Item.unmarked ∈ start links) :
    ∀ i, openAfter (insQ links (flatPlaces true links true))
      (outsQ links (flatPlaces true links true)) (· ∈ start links)
      (flatPlaces true links true).length i → i ∈ endFirst := by
  intro i hi
  have h1 := (openIsList Item (insL links (flatPlaces true links true))
    (outsL links (flatPlaces true links true)) (start links)
    (flatPlaces true links true).length i).1 hi
  have h2 := (openL_iff_openSets links (flatPlaces true links true) (start links) hr ha hu
    (flatPlaces true links true).length (Nat.le_refl _) i).1 h1
  rcases endOpenOnly links hlk i h2 with e | e | e | e | e <;> subst e <;> decide

/-- **hEnd at the written list of the 25 segments.** -/
theorem hEnd_full :
    ∀ i, openAfter (insQ linksFull (flatPlaces true linksFull true))
      (outsQ linksFull (flatPlaces true linksFull true)) (· ∈ start linksFull)
      (flatPlaces true linksFull true).length i → i ∈ endFirst :=
  hEnd_of linksFull (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.hEnd_of
#print axioms Desc.K14.Law.Sh.hEnd_full
