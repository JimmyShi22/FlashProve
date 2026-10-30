-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/ToldAtClosing.lean: the code switch's law: A CLOSED FACT ON THE WRITTEN CUT
OF THE PROOF FILE's FIRST CHAIN AT THE FULL SIZE, BY LEAN's KERNEL: in front of a link's closing
just as many oracle messages have been told as in front of the next code switch. A law file; no
running text imports it.

Why. The condition in front of the code switch into group l + 1 asks the kept old messages' shapes
at the state in front of link l's closing (the cut 14 l + 12; at the head's link 350). The fold's
fact on the messages' shapes speaks of the messages that are there: so the kept numbers must lie
below the count at that cut. The count is what the sub-protocols in front tell; under «the chain's
blocks have the written cut» that is read off the written rows (toldBefore_cut,
Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean).

  told_closing_written   at the written cut: what is told in front of number 14 l + 12 is
                   n0At (l + 1), l = 0 … 23; in front of number 350 it is n0At 25. By the kernel.
  told_at_closing, told_at_head_closing   the same of any list of blocks with the written cut.
  olds_below_closing   so the kept old messages of the switch into group l + 1 lie below what is
                   told in front of number 14 l + 12 (by olds_below,
                   Johnson/Top/H0/K2Hears/PlaceNums.lean).
  neg_*            negative tests, by the kernel: at the cut in front of link 1's own switch the
                   count is not n0At 2; at the right cut it is not n0At 2 + 1.
Limits. Closed facts on written values. That a run's chain has the written cut, and that the state
holds what the blocks tell, are others'. The full size alone. Nothing on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.CutNums
import Johnson.Top.H0.K2Hears.PlaceNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutFirstFull toldBefore toldBefore_cut toldOfRow)
open VerifiableInference.Desc.First.K2 (n0At oldsAt olds_below)

/-- What the written rows tell in front of number k. -/
def toldW (k : ℕ) : ℕ := ((cutFirstFull.take k).map toldOfRow).sum

set_option maxRecDepth 1000000 in
/-- **At the written cut.** -/
theorem told_closing_written :
    (((List.range 24).all fun l => toldW (14 * l + 12) == n0At (l + 1)) &&
      (toldW 350 == n0At 25)) = true := by decide +kernel

section
variable {T Cl : Type} {bs : List (Block T Cl)}

theorem told_at_closing (h : PlanWritten.cutOf bs = cutFirstFull) {l : ℕ} (hl : l < 24) :
    toldBefore bs (14 * l + 12) = n0At (l + 1) := by
  rw [toldBefore_cut, h]
  have H := told_closing_written
  rw [Bool.and_eq_true] at H
  exact eq_of_beq ((List.all_eq_true.1 H.1) l (List.mem_range.2 hl))

theorem told_at_head_closing (h : PlanWritten.cutOf bs = cutFirstFull) :
    toldBefore bs 350 = n0At 25 := by
  rw [toldBefore_cut, h]
  have H := told_closing_written
  rw [Bool.and_eq_true] at H
  exact eq_of_beq H.2

/-- **The kept old messages lie below what is told in front of the closing.** -/
theorem olds_below_closing (h : PlanWritten.cutOf bs = cutFirstFull) {l : ℕ} (hl : l < 24) :
    ∀ o ∈ oldsAt (l + 1), o < toldBefore bs (14 * l + 12) := by
  intro o ho
  rw [told_at_closing h hl]
  have H := (List.all_eq_true.1 olds_below) (l + 1) (by rw [List.mem_range'_1]; omega)
  exact of_decide_eq_true ((List.all_eq_true.1 H) o ho)

end

set_option maxRecDepth 1000000 in
theorem neg_told_cut : (toldW (14 * 1 + 2) == n0At 2) = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_told_number : (toldW (14 * 1 + 12) == n0At 2 + 1) = false := by decide +kernel

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.told_closing_written
#print axioms VerifiableInference.Desc.First.K2Hands.olds_below_closing
#print axioms VerifiableInference.Desc.First.K2Hands.told_at_head_closing
