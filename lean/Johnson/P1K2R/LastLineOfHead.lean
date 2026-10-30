-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/LastLineOfHead.lean: THE CODE SWITCH's NAMED CONDITION AT THE COMPOSED MEANING's
    CLOSED CONSTANT (`P5J.AtMgA.K2Cond`, Johnson/Goal/Skeleton/Kinds/K2Bridge.lean) FROM THE HEAD
    (WITH THE FOURTEEN ENTRY TESTS) AND "L₀'s THREE LISTS ARE THE DESCRIPTION's OWN": NO NAMED TEST
    STAYS IN FRONT. One theorem. A law file: no sub-protocol imports it. Its statement is that of
    `k2Cond_tests` (Johnson/P1K2R/LastLineTests.lean), CUT BY PROGRAM.

What is said. `k2Cond_of_head`: IT ENDS IN `Hd.K2Cond L₀`. THE FOUR NAMED TESTS OF `k2Cond_tests`
    ARE CALLS: `tableWrittenB`: `K2Ties.tableWrittenB_head` (Johnson/Top/H0/K2Ties/AtHead3.lean:
    "the typed table's maker returns" is read off the head's field opts (the named test spotsB,
        Johnson/P5J/OptsOk.lean), which none of the fourteen entry tests (`LPFD.lawsAsk`,
        Johnson/Desc/Laid/ProofAsks.lean) names; its value is
    the written table by `table_in_scope`, Johnson/LPFE1R/TableClosed.lean) ·
    `linkPlanB` (at the 23), `headPlanB`: `hLP_head`, `hHP_head`
    (Johnson/P1K2R/PlanBoolsAtConst.lean) · `k5PlanB` (at attention's segments): `hK5_head`
    (Johnson/P1K2R/K5AtConst.lean).
  ITS PREMISES, WHOLE. The head Hd : `P5J.AtMgA` at the second hash function; q₁ q₂ q₃: L₀'s three
      lists are the description's own. Nothing else.

Limits. THE HEAD IS A LONG CONDITION OF ITS OWN. WHAT THE HEAD HOLDS (`P5J.AtMgA`,
    Johnson/P5J/MgAtAll.lean): in scope · the files are read · the value is laid (over the proof
    file's fourteen entry tests) · the public part is the planner's · AND ELEVEN FURTHER CONDITIONS:
        the seven tests of `P5J.At.PlanOk` · headAt · cols13 · opts · k3. Which of them the verifier
        asks is not said here.
    NO EXAMPLE OF THE HEAD IS SHOWN HERE: the theorem may be idle. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.LastLineTests
import Johnson.P1K2R.PlanBoolsAtConst
import Johnson.P1K2R.K5AtConst

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


set_option maxHeartbeats 8000000 in
/-- **The named condition, from the head (with the fourteen entry tests).** -/
theorem k2Cond_of_head (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) (L₀ : P5J.Free numsFull Dw
                (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
                            = L₀.c₁ :: L₀.k₁) (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L₀.c₂ :: L₀.k₂) (q₃ :
                                                 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L₀.c₃ :: L₀.k₃) :
    Hd.K2Cond L₀ :=
  k2Cond_tests Hd L₀ q₁ q₂ q₃ (K2Ties.tableWrittenB_head Hd) (hLP_head Hd) (hK5_head Hd) (hHP_head
      Hd)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k2Cond_of_head
