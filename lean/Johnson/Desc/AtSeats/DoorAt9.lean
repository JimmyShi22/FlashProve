-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.K13LawTop
import Johnson.Desc.K13.Law.BridgeKind
import Johnson.Desc.Sound.MgAllAt
/-
THE KERNEL FACTS ON THE TWO CLOSED DOORS, AT THE COMPOSED MEANING mgAll 𝔇 Mg₀ (Johnson/Desc/Sound/MgAll.lean) (THE SMALL DOOR; the 9 in the names here marks it), over a base whose door is empty. K13's share in the
second form (k13_law_kindR) has four premises that read doors alone: hRowB · hIn · hQ at the WIDER door (the three struck parts laid over mgAll 𝔇 Mg₀ again:
plus13), and hDoors: the test on the two doors at all borders. The narrower door is the closed term mgMore (mgAll_more_closed, Johnson/Desc/Sound/MgAllAt.lean); the wider is wide13 mgMore.
  wide13 M · plus13_more      the wider door, of the narrower: the three struck parts' own «more :=» lines; by rfl.
  rowB_9 · in_9 · q_9 · doors_9   the four at the closed terms: decide +kernel.
  in_narrow_no                a negative test: at the NARROWER door the first item is NOT open in front of 355 (it has left).
  doors_at_mgAll9             the four at mgAll 𝔇 Mg₀, under Mg₀.more = {}.
NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (More Pub pubSets flatPlacesOf)
open VerifiableInference.Desc.Sound (mgAll MgData CellsQ MsgT mgMore mgAll_more_closed)

/-- The wider door, of the narrower. -/
def wide13 (M : More) : More :=
  ((M.merge (K12.Door.k12More.merge K12.Door.shapesMore)).merge First.weightsMore).merge
    (k13Asks.merge (pileMasksMore.merge (pileWithinMore.merge oneRowMore)))

theorem plus13_more {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (d : K12.Door.K12Data)
    (Mg : First.Meaning Pp W) : (plus13 D d Mg).more = wide13 Mg.more := rfl

/-- What is open in front of sub-protocol number 355 at a door. -/
abbrev q355 (M : More) : List Pub :=
  (pubSets M Sound.linksFull (flatPlacesOf Sound.linksFull true))[355]?.getD []

#eval (q355 (wide13 mgMore)).map fun q => toString (repr q)
#eval (q355 mgMore).map fun q => toString (repr q)

set_option maxRecDepth 1000000 in
theorem rowB_9 :
    rowM3B (wide13 mgMore) Sound.linksFull (flatPlacesOf Sound.linksFull true) 355 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem in_9 : bookItem ∈ q355 (wide13 mgMore) ∧ seatsItem ∈ q355 (wide13 mgMore) ∧
    shapesItem ∈ q355 (wide13 mgMore) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem q_9 : ∀ q ∈ q355 (wide13 mgMore), q ∈ knownK13 ∨ q = weightsItem ∨ q = pileWithinItem ∨
    q = oneRowItem ∨ q = bookFitsItem := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem doors_9 : doorsFitAllB mgMore (wide13 mgMore) cA13 Sound.linksFull
    (flatPlacesOf Sound.linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the item has left the narrower door. -/
theorem in_narrow_no : bookItem ∉ q355 mgMore := by decide +kernel

/-- **The four at the composed meaning.** -/
theorem doors_at_mgAll9 {Xi P Tok : Type} {rows cols nR nD : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X)
    (Mg₀ : First.Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT)) (h0 : Mg₀.more = {})
    (D : DataK13 P (Desc.Wit (CellsQ rows cols) Tok MsgT) nD) (d : K12.Door.K12Data) :
    rowM3B (plus13 D d (mgAll 𝔇 Mg₀)).more Sound.linksFull (flatPlacesOf Sound.linksFull true) 355 =
        true ∧
    (bookItem ∈ q355 (plus13 D d (mgAll 𝔇 Mg₀)).more ∧
      seatsItem ∈ q355 (plus13 D d (mgAll 𝔇 Mg₀)).more ∧
      shapesItem ∈ q355 (plus13 D d (mgAll 𝔇 Mg₀)).more) ∧
    (∀ q ∈ q355 (plus13 D d (mgAll 𝔇 Mg₀)).more, q ∈ knownK13 ∨ q = weightsItem ∨
      q = pileWithinItem ∨ q = oneRowItem ∨ q = bookFitsItem) ∧
    doorsFitAllB (mgAll 𝔇 Mg₀).more (plus13 D d (mgAll 𝔇 Mg₀)).more cA13 Sound.linksFull
      (flatPlacesOf Sound.linksFull true) = true := by
  rw [plus13_more, mgAll_more_closed 𝔇 Mg₀ h0]
  exact ⟨rowB_9, in_9, q_9, doors_9⟩

end VerifiableInference.Desc.K13.Law
