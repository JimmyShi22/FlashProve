-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/K2FromHead.lean: THE CODE SWITCH's SHARE OF THE FIRST CHAIN's LAWS AT THE COMPOSED
    MEANING's CLOSED CONSTANT (`P5J.AtMgA.Kind` at the kind K2) FROM THE HEAD (WITH THE FOURTEEN
    ENTRY TESTS). Two theorems. A law file: no sub-protocol imports it.

What is said.
  `k02_kind_of_head`: under the head, for every filling whose three lists are the description's own:
      `Hd.Kind L₀ KindName.K2`: the type of the field k2 of `VerifierAndGoals.AtTheName.KindsConds`
      (Johnson/Goal/Skeleton/KindsOfConds.lean). It is `P5J.k02_kind_all`
      (Johnson/Goal/Skeleton/Kinds/K2Bridge.lean: the named condition gives the kind's share) at
      `k2Cond_of_head` (Johnson/P1K2R/LastLineOfHead.lean: the head gives the named condition).
  `k02_kind_free`: the same at the value `P5J.AtMgA.free` (Johnson/P5J/FreeAll.lean),
      whose three lists are the description's own by that file's `free_q₁`, `free_q₂`, `free_q₃`: NO
      PREMISE BUT THE HEAD.

Limits. THE HEAD IS A LONG CONDITION OF ITS OWN: what it holds: LastLineOfHead.lean's limits. NO
    EXAMPLE OF THE HEAD IS SHOWN HERE: the theorems may be idle. The kind's share is one of the
    first chain's; no soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.LastLineOfHead
import Johnson.P5J.FreeAll

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


/-- **The kind's share, from the head (with the fourteen entry tests)**, general in the filling. -/
theorem k02_kind_of_head (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) (L₀ : P5J.Free numsFull
                Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np
                            cF).first.blocksInOrder = L₀.c₁ :: L₀.k₁) (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L₀.c₂ ::
                                     L₀.k₂) (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L₀.c₃ :: L₀.k₃) :
    Hd.Kind L₀ KindName.K2 :=
  P5J.k02_kind_all Hd L₀ q₁ q₂ q₃ (k2Cond_of_head Hd L₀ q₁ q₂ q₃)

/-- **The kind's share at the value, from the head (with the fourteen entry tests) alone.** -/
theorem k02_kind_free (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) :
    Hd.Kind Hd.free KindName.K2 :=
  k02_kind_of_head Hd Hd.free Hd.free_q₁ Hd.free_q₂ Hd.free_q₃

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02_kind_of_head
#print axioms VerifiableInference.Desc.First.K2Caller.k02_kind_free
