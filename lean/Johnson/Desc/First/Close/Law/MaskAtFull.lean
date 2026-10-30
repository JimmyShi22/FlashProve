-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/MaskAtFull.lean (kind K10): THE NUMBER OF THE FRESH MASK OF A LINK's CLOSING (`ReqFrame.mask`), OFF PUBLIC NUMBERS, IS THE PLAN's OWN NUMBER OF THAT MESSAGE's SEAT: AT THE WRITTEN VALUES OF THE FULL SIZE, AT ALL 25 LINKS. Definitions with code, closed facts by the kernel, statements.

Why. K10's hCar asks five things of «rows.fresh» behind the closing. By `closeFrame_reads`
(Johnson/Desc/First/Link/Law/CloseReads.lean) rows.fresh is the frame's mask in front. By three
statements (mask_named · mask_head_named · mask_zero_named: Johnson/IMR/MaskNamed.lean,
MaskHeadNamed.lean, MaskZeroNamed.lean: theorems there, in scope, at a fold that returns)
the frame's mask in front of K10's own
sub-protocol of link l is: the count of oracle messages in front of the link's first sub-protocol + (1 + the switch's kept messages) + the link's own messages of moment 0; at link 0: the last alone. THE CLOSED HALF, HERE: in the table's counts that number is the place, in the plan's list of seats, of the seat of
the plan's entry with seg = some (l, 0) and role = mask.

What is said.
  `maskPub N sh l`: **the number, off public numbers**: the three cases (link 0 · the links 1 … 23 · the head's, whose first sub-protocol stands at 339).
  `maskSeat ps l`: the seat of the plan's entry with seg = some (l, 0) and role = mask. `maskNo seats ps l`: its place in the list of seats.
  `maskThereB` [BY THE KERNEL]: at each l < 25 the written plan has such an entry, and its seat is in the written list of seats.
  `maskB_full` [BY THE KERNEL]: **at each l < 25: maskPub at the written tellings = maskNo at the written seats.** `maskB_off`: one link further the two differ at every l < 24.
  `maskPub_free`, `mask_full`, `mask_at_cut`, `mask_at_laid`: so at any numbers beneath; where the first chain's cut is the written one; where the value is laid.

Limits. CLOSED FACTS: nothing on a state. The tie to a state is mask_named, mask_head_named and
mask_zero_named (Johnson/IMR/MaskNamed.lean, MaskHeadNamed.lean, MaskZeroNamed.lean: in scope, the
files read, at OnBytes.secondHashFunction, at an opened seat and a fold that returns);
Johnson/P5J/MaskAtMgAll.lean joins it to this file under AtMg, which is a premise
there, and «reached»; nothing of it is called here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.HingeMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- **The number of the fresh mask of link l's closing, off public numbers.** -/
def maskPub (N : Numbers) (sh : Params.ReqShape) (l : ℕ) : ℕ :=
  if l = 0 then Meaning.K2.msgsAt sh 0 0
  else N.msgsAt IM.placesW[if l = 24 then 339 else 14 * l + 2]? +
    (1 + (K2.targetAt sh l).kept.size) + Meaning.K2.msgsAt sh l 0

/-- The plan's entry for that message. -/
def maskEntry (ps : List P5T.PSeat) (l : ℕ) : Option P5T.PSeat :=
  ps.find? fun p => p.seg == some (l, 0) && p.role == .mask

/-- Its seat. -/
def maskSeat (ps : List P5T.PSeat) (l : ℕ) : ℕ × ℕ := ((maskEntry ps l).map (·.seat)).getD (0, 0)

/-- **The plan's own number of that seat.** -/
def maskNo (seats : List (ℕ × ℕ)) (ps : List P5T.PSeat) (l : ℕ) : ℕ := seats.idxOf (maskSeat ps l)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(W) The entry is there, and its seat is listed.** -/
theorem maskThereB :
    ((List.range 25).all fun l => (maskEntry P5T.psFull l).isSome &&
      decide (maskSeat P5T.psFull l ∈ seatsPlanW)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(W) The two numbers are one, at all 25 links.** -/
theorem maskB_full :
    ((List.range 25).all fun l =>
      decide (maskPub (P5T.N0Full.withTold IM.placesW toldCut) shapeFull l =
        maskNo seatsPlanW P5T.psFull l)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(N)** Against the next link's seat they differ, at every l < 24. -/
theorem maskB_off :
    ((List.range 24).any fun l =>
      decide (maskPub (P5T.N0Full.withTold IM.placesW toldCut) shapeFull l =
        maskNo seatsPlanW P5T.psFull (l + 1))) = false := by decide +kernel

theorem maskPub_free (N₀ N₁ : Numbers) (ps : List Place) (told : List (List Oracle))
    (sh : Params.ReqShape) (l : ℕ) :
    maskPub (N₀.withTold ps told) sh l = maskPub (N₁.withTold ps told) sh l := rfl

theorem mask_full (N₀ : Numbers) (l : ℕ) (hl : l < 25) :
    maskPub (N₀.withTold IM.placesW toldCut) shapeFull l = maskNo seatsPlanW P5T.psFull l := by
  rw [maskPub_free N₀ P5T.N0Full]
  exact of_decide_eq_true (List.all_eq_true.1 maskB_full l (List.mem_range.2 hl))

theorem mask_at_cut {St Cl : Type} {bs : List (Block St Cl)}
    (hc : VerifiableInference.PlanWritten.cutOf bs = VerifiableInference.PlanWritten.cutFirstFull)
    (N₀ : Numbers) (l : ℕ) (hl : l < 25) :
    maskPub (N₀.withTold IM.placesW (toldOf bs)) shapeFull l = maskNo seatsPlanW P5T.psFull l := by
  rw [(told_at_written hc).2]
  exact mask_full N₀ l hl

theorem mask_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) (N₀ : Numbers) (l : ℕ) (hl : l < 25) :
    maskPub (N₀.withTold IM.placesW (toldOf cF.blocksInOrder)) shapeFull l =
      maskNo seatsPlanW P5T.psFull l :=
  mask_at_cut (hc_at_laid hZ L) N₀ l hl

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.maskThereB
#print axioms VerifiableInference.Desc.First.Close.maskB_full
#print axioms VerifiableInference.Desc.First.Close.maskB_off
#print axioms VerifiableInference.Desc.First.Close.mask_full
#print axioms VerifiableInference.Desc.First.Close.mask_at_laid
