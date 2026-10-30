-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/CutWritten.lean: THE FIRST CHAIN's PLACES AND WHAT EACH SUB-PROTOCOL TELLS, AT
THE FULL SIZE, AS TWO CLOSED LISTS off the written cut `cutFirstFull`
(Johnson/Desc/Ok/PlanWritten/CutLit.lean); with the facts on them that the table's tests spend.
Two definitions, four theorems. A file beside the table: it turns nothing of it.
Why. The table's numbers are filled off `blockPlaces bs` and `toldOf bs` (`Numbers.atBlocks`,
Johnson/Desc/First/NumbersAtBlocks.lean). Where the verifier's entry test on the cut accepts,
`cutOf bs` is the written list: so both are the two lists here, and a test on the table's numbers
becomes a closed fact.
  `placesCut`, `toldCut`: the written cut's second field; its rounds that tell a tree, laid flat.
  `told_at_written`: **where `cutOf bs = cutFirstFull`: `blockPlaces bs = placesCut` and `toldOf
  bs = toldCut`**: by `told_at_cut` (Johnson/Desc/First/CutAtNumbers.lean).
  `placesCut_is`: by Lean's kernel: the written places are the table's own list `flatPlacesOf
  linksFull true`.
  `placesCut_nodup`: by the kernel: they are different from each other.
  `toldCut_counts`: by the kernel: 358 places; 358 tellings; 83 trees and 199 tenants told in all.
On the names. `IM.placesW` (the integer model's WrittenList.lean) is another term: `flatPlacesOf
IM.linksW true`, at a row of sorts whose text is not `linksFull`'s. `placesCut` is read off the
written cut, and `placesCut_is` ties it to `flatPlacesOf linksFull true`. THAT `IM.linksW` AND
`linksFull` ARE ONE LIST IS NOT SAID HERE.
Limits. THE WRITTEN CUT RESTS ON PRINTS OF LEAN's EVALUATOR (that file's head): no theorem says
that it is the value's; the entry test compares it at a run. The full size alone. No probability:
no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.CutAtNumbers
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.PlanWritten (cutFirstFull)

/-- The first chain's places at the full size, off the written cut. -/
def placesCut : List Place := cutFirstFull.map (·.2.1)

/-- What each sub-protocol of the first chain tells at the full size, off the written cut. -/
def toldCut : List (List Oracle) := cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)

/-- **Where the cut is the written one, the places and what is told are the two written lists.** -/
theorem told_at_written {St Cl : Type} {bs : List (Block St Cl)}
    (h : PlanWritten.cutOf bs = cutFirstFull) : blockPlaces bs = placesCut ∧ toldOf bs = toldCut :=
  told_at_cut h

set_option maxRecDepth 1000000 in
/-- By the kernel: the written places are the table's own list. -/
theorem placesCut_is : placesCut = flatPlacesOf linksFull true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: the written places are different from each other. -/
theorem placesCut_nodup : placesCut.Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: how many places, tellings, trees and tenants. -/
theorem toldCut_counts :
    (placesCut.length, toldCut.length, treesTold toldCut 358, msgsTold toldCut 358) =
      (358, 358, 83, 199) := by decide +kernel

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.told_at_written
#print axioms VerifiableInference.Desc.First.placesCut_is
#print axioms VerifiableInference.Desc.First.placesCut_nodup
#print axioms VerifiableInference.Desc.First.toldCut_counts
