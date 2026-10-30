-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/LastJoin4.lean: FOR THE CODE SWITCH's NAMED CONDITION AT THE CLOSED CONSTANT
    (`P5J.AtMgA.K2Cond`, Johnson/Goal/Skeleton/Kinds/K2Bridge.lean): THE LISTED PLACES ARE THE
    CONSTANT's TENANTS. One theorem. A law file: no sub-protocol imports it.

What is said. `places_at_const`: `P1Named.places_at` (Johnson/Top/H0/K2Caller/PlacesWritten.lean)
    under `AtWritten` and "the first chain's sendings are the written ones".

Limits. AN IMPLICATION: ITS PREMISES ARE SHOWN AT NO STATE HERE: the theorem may be idle. The import
    lines are wider than the theorem needs: Johnson/P1K2R/LastLine.lean takes
    OwesAtConst.lean, RowClosedConst.lean, DoorKeepsMade.lean, OffHead.lean and MembersShapeAt.lean
    through this file. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.LastJoin3
import Johnson.P1K2R.OwesAtConst
import Johnson.P1K2R.RowClosedConst
import Johnson.Top.H0.K2Caller.DoorKeepsMade
import Johnson.Top.H0.K2Ties.OffHead
import Johnson.Top.H0.K2Ties.MembersShapeAt

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
open VerifiableInference.Desc.K12.Door (Laid snAt sendsAreB laidAtCodes)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn sameMembers flatPlacesOf
    laysPads)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike SeedReads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes DecBlind Left HeadBears saidBehindB
    decBlind_at AtWritten AtTold at_written at_told sends_at offC_head codes_of_sends left_of_seat)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt LeftDoor EndsUnmarked BookDoor mOf said_at hsam_at hidx_at k2No_mOf
    k2_written_at_row k2_unmarked_at k2_spots piece_base_trees_at flat_planOk linkPlanB k5PlanB
    headPlanB)
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB fxAt)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF
                  : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem places_at_const (A : AtWritten Zp cF) (hs : Zp.made.proof.1 = Johnson.G.proofSends0) {L :
    Laid} (hl : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) : L.places = P5J.At.seats Zp :=
    by
  have hc : Zp.first.codes = Johnson.G.proofSends0.codes := by
    show P5J.At.cs Zp = _
    rw [A.cs, codes_of_sends]
  exact P1Named.places_at hc hs A.pseats hl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.places_at_const
