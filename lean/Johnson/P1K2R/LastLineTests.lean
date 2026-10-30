-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/LastLineTests.lean: THE CODE SWITCH's NAMED CONDITION AT THE CLOSED CONSTANT
    (`P5J.AtMgA.K2Cond`, Johnson/Goal/Skeleton/Kinds/K2Bridge.lean): THE TWO EQUATIONS ON PUBLIC
    DATA AMONG THE PREMISES OF `k2Cond_plan` (Johnson/P1K2R/LastLinePlan.lean) ARE CALLS: THE HEAD
        AND FOUR NAMED TESTS STAY. One theorem. A law file: no sub-protocol imports it. Its
        statement is
    `k2Cond_plan`'s, CUT BY PROGRAM.

What is said. `k2Cond_tests`: IT ENDS IN `Hd.K2Cond L₀`. THE TWO: "25 segments":
    `P1K2.links25_atAll` (Johnson/Top/H0/Opts/Links25AtHead.lean), under the head · "the output
    head's lookup has heard nothing":
        `Fo.ZPlan.public_heard` (Johnson/Desc/First/Look/HeardNone.lean: a law of the planner's
        text; of the head it spends "the public part is the planner's" alone).
  ITS PREMISES, WHOLE. (i) The head Hd (with the fourteen entry tests: see LastLineHead.lean's
      limits); L₀'s three lists are the description's own. (ii) FOUR NAMED TESTS ON PUBLIC DATA:
          `tableWrittenB` · `linkPlanB` (at the 23) · `k5PlanB` (at attention's segments) ·
              `headPlanB`. Of these `linkPlanB`, `k5PlanB`, `headPlanB` stand at the parameters `(dC
              Hd).pubD`, a noncomputable term that names the proof Hd.

Limits. THE PREMISES ARE NOT SHOWN TO HOLD TOGETHER: no example: the theorem may be idle. No
    soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.LastLinePlan
import Johnson.Top.H0.Opts.Links25AtHead
import Johnson.Desc.First.Look.HeardNone

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
/-- **The named condition, from the head (with the fourteen entry tests) and four named tests.** -/
theorem k2Cond_tests (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) (L₀ : P5J.Free numsFull Dw
                (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
                            = L₀.c₁ :: L₀.k₁) (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L₀.c₂ :: L₀.k₂) (q₃ :
                                                 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L₀.c₃ :: L₀.k₃) (hTW : tableWrittenB Z.pol Z.lay
                                                                      Z.KL = true) (hLP : ∀ m, m < 23 →
                                                                      linkPlanB Zp (dC Hd).pubD.nsOf (dC Hd).pubD.d3 (m + 1) = true) (hK5 : ∀ m, m < 23 → IM.subW (m +
                                                                      1) = .attention → k5PlanB Zp (dC Hd).pubD.d5 Zp.first.layout (m + 1) = true) (hHP : headPlanB Zp
                                                                      (dC Hd).pubD.nsOf (dC Hd).pubD.d3 = true) :
    Hd.K2Cond L₀ :=
  k2Cond_plan Hd L₀ q₁ q₂ q₃ hTW (P1K2.links25_atAll Hd) hLP hK5 hHP (Fo.ZPlan.public_heard
      Hd.toAtMg.pubOne).2.2

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k2Cond_tests
