-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/MaskLaidFull.lean (kind K10): WHAT THE PLAN's LIST OF SEATS AND TREES HOLDS AT THE NUMBER OF THE FRESH MASK OF A LINK's CLOSING: AT THE WRITTEN VALUES OF THE FULL SIZE, AT ALL 25 LINKS. Definitions with code and closed facts by the kernel.

Why. K10's hCar (`hCar_end`, Johnson/Desc/First/Link/Law/HCarEnd.lean) asks of «rows.fresh» behind the closing: the plan's list has a seat (tree, part) at that number; the list has that tree's shape. By MaskAtMg.lean (Johnson/P5J) rows.fresh is `maskNo` (MaskAtFull.lean beside this file). The plan's list at the written values is
`LFull` (Johnson/HB/LLHARD/LaidWritten.lean), with `laid_at`: wherever the codes and the first chain's sendings are the written ones, `laidAtCodes` returns it.

What is said.
  `maskTree l`, `maskPart l`: the two halves of the written plan's seat of link l's fresh mask.
  `maskPlaceB` [BY THE KERNEL]: **at each l < 25: LFull.places[maskNo seatsPlanW P5T.psFull l]? = some (maskTree l, maskPart l).** `maskPlaceB_off`: one number further the list has another seat, at every l < 25.
  `maskShapeB` [BY THE KERNEL]: at each l < 25 the list has that tree's shape.
  `mask_place`, `mask_shape`: the two as statements at a link.
  `maskShape l`, `maskA l`, `maskSkip l`: **THE TERMS FOR `hCar_end`'s LETTERS shF0 · aF · skip** (tree := maskTree l · tnF := maskPart l): the listed shape of that tree; its logN; its main width and the mask symbols of the parts in front. `mask_letters`: **hfL · hfs · hfa · hfskip, in their own texts, at Lp := LFull and
    these terms.** aF and skip are free letters there, which hfa and hfskip define; they stand also in the fresh mask's word (mWRaw … tree skip aF): ONE SPELLING FOR ALL WHO LAY IT.

Limits. CLOSED FACTS: nothing on a state. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.MaskAtFull
import Johnson.HB.LLHARD.LaidWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open VerifiableInference.Desc.K13.Law (LFull)

/-- The tree of the written plan's seat of link l's fresh mask. -/
def maskTree (l : ℕ) : ℕ := (maskSeat P5T.psFull l).1

/-- Its part of that tree. -/
def maskPart (l : ℕ) : ℕ := (maskSeat P5T.psFull l).2

/-- The listed shape of that tree. -/
def maskShape (l : ℕ) : TreeShape := (LFull.shapes[maskTree l]?).getD default

/-- Its number of leaves' logarithm. -/
def maskA (l : ℕ) : ℕ := (maskShape l).logN

/-- The words in front of the fresh mask's own in a leaf of that tree. -/
def maskSkip (l : ℕ) : ℕ :=
  (maskShape l).mainWidth + ((maskShape l).maskSymbols.extract 0 (maskPart l)).foldl (· + ·) 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(W) The plan's list has that seat at that number.** -/
theorem maskPlaceB :
    ((List.range 25).all fun l =>
      decide (LFull.places[maskNo seatsPlanW P5T.psFull l]? = some (maskTree l, maskPart l))) =
      true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(N)** One number further the list has another seat, or none. -/
theorem maskPlaceB_off :
    ((List.range 25).any fun l =>
      decide (LFull.places[maskNo seatsPlanW P5T.psFull l + 1]? =
        some (maskTree l, maskPart l))) = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(W) The list has that tree's shape.** -/
theorem maskShapeB :
    ((List.range 25).all fun l => (LFull.shapes[maskTree l]?).isSome) = true := by decide +kernel

theorem mask_place (l : ℕ) (hl : l < 25) :
    LFull.places[maskNo seatsPlanW P5T.psFull l]? = some (maskTree l, maskPart l) :=
  of_decide_eq_true (List.all_eq_true.1 maskPlaceB l (List.mem_range.2 hl))

theorem mask_shape (l : ℕ) (hl : l < 25) : ∃ sh, LFull.shapes[maskTree l]? = some sh :=
  Option.isSome_iff_exists.1 (List.all_eq_true.1 maskShapeB l (List.mem_range.2 hl))

/-- **hfL · hfs · hfa · hfskip AT THE WRITTEN LIST AND THE NAMED TERMS.** -/
theorem mask_letters (l : ℕ) (hl : l < 25) :
    LFull.places[maskNo seatsPlanW P5T.psFull l]? = some (maskTree l, maskPart l) ∧
      LFull.shapes[maskTree l]? = some (maskShape l) ∧ (maskShape l).logN = maskA l ∧
      (maskShape l).mainWidth + ((maskShape l).maskSymbols.extract 0 (maskPart l)).foldl (· + ·) 0 =
        maskSkip l := by
  obtain ⟨sh, hs⟩ := mask_shape l hl
  refine ⟨mask_place l hl, ?_, rfl, rfl⟩
  unfold maskShape
  rw [hs]
  rfl

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.mask_letters
#print axioms VerifiableInference.Desc.First.Close.maskPlaceB
#print axioms VerifiableInference.Desc.First.Close.maskPlaceB_off
#print axioms VerifiableInference.Desc.First.Close.maskShapeB
#print axioms VerifiableInference.Desc.First.Close.mask_place
#print axioms VerifiableInference.Desc.First.Close.mask_shape
