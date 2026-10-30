-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/LastJoin3.lean: FOR THE CODE SWITCH's NAMED CONDITION AT THE CLOSED CONSTANT
    (`P5J.AtMgA.K2Cond`, Johnson/Goal/Skeleton/Kinds/K2Bridge.lean): SIX OF ITS FIELDS AT EVERY
    PLACE OF THE KIND: hoP, hoC, hoR, hins, hctx, hHands. One definition, six theorems. A law file:
    no sub-protocol imports it.

What is said.
  `outsB`, `outs_full`, `outs_can_fail`, `outs_at`: BY LEAN's KERNEL at the 25 numbers: the table's
      row at a place of the kind opens the pin of the new members and the two rows of the next
      segment (the fields hoP, hoC, hoR); a negative test.
  `mOf_lt25`: at a place of the kind mOf k is below 25.
  `ins_at`: the fields hins, hctx: `k2_row_full`
      (Johnson/Top/H0/K2Caller/TieFourPlacesFull.lean) with `k2Place_at`
      (Johnson/P1K2R/TiesOneFour.lean): its segment is mOf k.
  `hHands_at`: the field hHands at every place of the kind, at the head's chain's own sub-protocol:
      the three arms of Johnson/Top/H0/K2Ties/HandsConst.lean by the place's sort. ITS PREMISES: the
          head; the named tests `madePinnedAt`, the cut, `sendsAreB`, `linkPlanB`, `k5PlanB`,
          `headPlanB`; "the output head's lookup has heard nothing".

Limits. THE NAMED TESTS ARE NOT SHOWN TO ACCEPT TOGETHER: the theorem may be idle. The import lines
    are wider than these need: Johnson/P1K2R/LastLine.lean takes
    CarryAtConst.lean and PieceAtRow.lean through this file. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.LastJoin2
import Johnson.P1K2R.CarryAtConst
import Johnson.P1K2R.PieceAtRow
import Johnson.Top.H0.K2Ties.HandsConst
import Johnson.Top.H0.K2Caller.TieFourPlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Chain Claim FileDescription Strs Wit KindName smpHeld)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid snAt sendsAreB)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn sameMembers flatPlacesOf)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike SeedReads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes DecBlind Left saidBehindB decBlind_at
    switches)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt LeftDoor EndsUnmarked BookDoor mOf mOf_link mem_switches said_at hsam_at hidx_at
    k2No_mOf k2_written_at_row k2_unmarked_at k2_spots piece_base_trees_at flat_planOk linkPlanB
    k5PlanB headPlanB)
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB fxAt)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

variable {F : Frame}

/-- What the table's row at number k opens, for the segment m + 1. -/
def outsB (k m : ℕ) : Bool :=
  (rowQ linksFull (flatPlacesOf linksFull true) k).outs.contains (Item.pin (m + 1) 0) &&
    (rowQ linksFull (flatPlacesOf linksFull true) k).outs.contains (Item.row (m + 1) .carried) &&
    (rowQ linksFull (flatPlacesOf linksFull true) k).outs.contains (Item.row (m + 1) .position)

set_option maxRecDepth 1000000 in
theorem outs_full : (switches 24).all (fun x => outsB x.1 (x.2 - 1)) = true := by decide +kernel

/-- A negative test: the first switch's row does not open the second segment's. -/
theorem outs_can_fail : outsB 16 1 = false := by decide +kernel

theorem outs_at {k : ℕ} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl) (hk :
    pl.kind = KindName.K2) : Item.pin (mOf k + 1) 0 ∈ (rowQ P5J.fullLinks P5J.At.ps k).outs ∧
    Item.row (mOf k + 1) .carried ∈ (rowQ P5J.fullLinks P5J.At.ps k).outs ∧ Item.row (mOf k + 1)
    .position ∈ (rowQ P5J.fullLinks P5J.At.ps k).outs := by
  have h : outsB k (mOf k + 1 - 1) = true := List.all_eq_true.1 outs_full _ (mem_switches ha hk)
  rw [Nat.add_sub_cancel] at h
  unfold outsB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨List.contains_iff_mem.1 h.1.1, List.contains_iff_mem.1 h.1.2, List.contains_iff_mem.1 h.2⟩

theorem mOf_lt25 {k : ℕ} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl) (hk :
    pl.kind = KindName.K2) : mOf k < 25 := by
  rcases k2_spots k pl ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · rw [mOf_link l a1 a24]
    omega
  · decide
  · decide

theorem ins_at {k : ℕ} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl) (hk :
    pl.kind = KindName.K2) : (rowQ P5J.fullLinks P5J.At.ps k).ins = [.carry (mOf k), .pinKept (mOf
    k)] ∧ (rowQ P5J.fullLinks P5J.At.ps k).ctx = [] := by
  obtain ⟨m', -, e1, hi, hc, -⟩ := k2_row_full k pl ha hk
  have e2 := (k2Place_at (mOf_lt25 ha hk) (by rw [k2No_mOf ha hk]; exact ha)).2.2
  have e : m' = mOf k := Nat.succ.inj (e1.symm.trans e2)
  subst e
  exact ⟨hi, hc⟩

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF
                  : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The field hHands, at every place of the kind.** -/
theorem hHands_at (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) (hy : madePinnedAt Zp.p.X.P
                Zp.p.chains.made Zp.first Zp.made = true) (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder
                = cutFirstFull) (hSB : ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ → sendsAreB
                Zp.made.proof.1 358 (snAt Zp G₀ IM.placesW) = true) (hLP : ∀ m, m < 23 → linkPlanB Zp (dC
                Hd).pubD.nsOf (dC Hd).pubD.d3 (m + 1) = true) (hK1 : k5PlanB Zp (dC Hd).pubD.d5 Zp.first.layout
                1 = true) (hK5 : ∀ m, m < 23 → IM.subW (m + 1) = .attention → k5PlanB Zp (dC Hd).pubD.d5
                Zp.first.layout (m + 1) = true) (hHP : headPlanB Zp (dC Hd).pubD.nsOf (dC Hd).pubD.d3 = true)
    (hh : Zp.p.X.H.tl.heard = none) {k : ℕ} {pl : VerifiableInference.Desc.Place} (ha :
    P5J.At.ps[k]? = some pl) (hk : pl.kind = KindName.K2) {B : Block Rec Cl} (hB : cF.blocksInOrder[k]? =
    some B) (ft : ℕ) :
    ∀ z, HandsR (Meaning.K2.FkR Zp cF z) (dC Hd).N P5J.fullLinks P5J.At.ps (EQ (mgAll (dC Hd)
        mgBase) P5J.fullLinks P5J.At.ps z) ft k B := by
  rcases k2_spots k pl ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · have e : 14 * (l - 1 + 1) + 2 = 14 * l + 0 + 2 := by omega
    have H := Meaning.K2.hHands_link_const Hd.toAtMg Hd.𝔇 hy hcut hSB (m := l - 1) (by omega) (hLP _
        (by omega)) hK1 (hK5 _ (by omega)) (ft := ft)
    rw [e] at H
    exact H B hB
  · exact Meaning.K2.hHands_head_const Hd.toAtMg Hd.𝔇 hy hcut hSB hHP hh B hB
  · exact Meaning.K2.hHands_fin_const Hd.toAtMg Hd.𝔇 hy hcut hSB B hB

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.outs_full
#print axioms VerifiableInference.Desc.First.K2Caller.outs_can_fail
#print axioms VerifiableInference.Desc.First.K2Caller.outs_at
#print axioms VerifiableInference.Desc.First.K2Caller.mOf_lt25
#print axioms VerifiableInference.Desc.First.K2Caller.ins_at
#print axioms VerifiableInference.Desc.First.K2Caller.hHands_at
