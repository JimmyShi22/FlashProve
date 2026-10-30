-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/DoorAt9WG.lean: THE KERNEL's WORD ON THE TWO CLOSED DOORS
AT NUMBERS 356 AND 2: the narrower door: the composed filling's own closed term `mgMore`;
the wider: `wideW mgMore` (defined here). The premises of
`w_tiedR_at` and `first_tiedR_at` (TieWAt9.lean, TieGAt9.lean) that read doors alone.
Definitions, and statements by `decide +kernel`. `qAt9 k`: what is open in front of number k at
  the wider door. `mkG9`: what comes at number 2: open at border 3 and not at 2. `rowW_9`, `qW_9`,
  `inW_9`, `doorsW_9`: at 356. `rowG_9`, `mk_9`, `mG_9`, `qG_9`, `doorsG_9`: at 2. `rowW_narrow_no`: A
  NEGATIVE TEST: at the NARROWER door the items that W's commitment's tie asks as open are not all
  open.
Nothing on soundness.

-/
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.K13.Law.BridgeG
import Johnson.Desc.AtSeats.MoreAtOpening
import Johnson.Desc.K13.Law.FillGPaid
import Johnson.Desc.K13.Law.FillM4Paid6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (More Pub pubSets flatPlacesOf)
open VerifiableInference.Desc.Sound (mgMore doorsFitB)

/-- The wider door, of the narrower: the three struck layers' own lines.
(Johnson/Desc/AtSeats/DoorAt9.lean has the same term as `wide13`; that file stands above files that
cannot be imported beside the exchanges at 356 and 2: so it is written here under a name of its
own.) -/
def wideW (M : More) : More :=
  ((M.merge (K12.Door.k12More.merge K12.Door.shapesMore)).merge First.weightsMore).merge
    (k13Asks.merge (pileMasksMore.merge (pileWithinMore.merge oneRowMore)))

theorem plus13_moreW {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (d : K12.Door.K12Data)
    (Mg : First.Meaning Pp W) : (plus13 D d Mg).more = wideW Mg.more := rfl

/-- What is open in front of sub-protocol number k at the wider door. -/
abbrev qAt9 (k : ℕ) : List Pub :=
  (pubSets (wideW mgMore) Sound.linksFull (flatPlacesOf Sound.linksFull true))[k]?.getD []

/-- What comes at number 2. -/
def mkG9 : List Pub := (qAt9 3).filter fun q => !(qAt9 2).contains q

set_option maxRecDepth 1000000 in
theorem rowW_9 :
    rowM4B (wideW mgMore) Sound.linksFull (flatPlacesOf Sound.linksFull true) 356 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem qW_9 : ∀ q ∈ qAt9 356, q ∈ knownK13 ∨ q = .frontOk ∨ q = weightsItem ∨
    q = pileWithinItem ∨ q = oneRowItem ∨ q = bookFitsItem := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem inW_9 : ∀ q ∈ knownK13, q ∈ qAt9 356 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem doorsW_9 : doorsFitB mgMore (wideW mgMore) cA13 Sound.linksFull
      (flatPlacesOf Sound.linksFull true) 356 = true ∧
    doorsFitB mgMore (wideW mgMore) cA13 Sound.linksFull
      (flatPlacesOf Sound.linksFull true) (356 + 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rowG_9 :
    rowGB (wideW mgMore) Sound.linksFull (flatPlacesOf Sound.linksFull true) 2 mkG9 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- What comes at number 2 is of the five, or one of First.FillSent's two names at segment 0. -/
theorem mk_9 : ∀ i ∈ mkG9, i ∈ madeSix ∨ i = HashBuild.sentItem0 ∨ i = HashBuild.treesItem0 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem mG_9 : Pub.noneSent ∈ qAt9 2 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem qG_9 : ∀ i ∈ qAt9 2, i = .noneSent ∨ i ∈ knownG ∨ i = weightsItem ∨ i = pileWithinItem ∨
    i = oneRowItem ∨ i = bookFitsItem := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem doorsG_9 : doorsFitB mgMore (wideW mgMore) cAG Sound.linksFull
      (flatPlacesOf Sound.linksFull true) 2 = true ∧
    doorsFitB mgMore (wideW mgMore) cAG Sound.linksFull
      (flatPlacesOf Sound.linksFull true) (2 + 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at the narrower door the four are not open in front of 356. -/
theorem rowW_narrow_no : ¬ ∀ q ∈ knownK13,
    q ∈ (pubSets mgMore Sound.linksFull (flatPlacesOf Sound.linksFull true))[356]?.getD [] := by
  decide +kernel

end VerifiableInference.Desc.K13.Law
