-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/LastLineHead.lean: THE CODE SWITCH's NAMED CONDITION AT THE CLOSED CONSTANT
    (`P5J.AtMgA.K2Cond`, Johnson/Goal/Skeleton/Kinds/K2Bridge.lean): FOUR OF THE PREMISES OF
    `k2Cond_last` (Johnson/P1K2R/LastLine.lean) ARE CALLS, FROM THE HEAD (WITH THE FOURTEEN ENTRY
        TESTS). One theorem. A law file: no sub-protocol imports it. Its statement is
    `k2Cond_last`'s, CUT BY PROGRAM.

What is said. `k2Cond_head`: IT ENDS IN `Hd.K2Cond L₀`. THE FOUR: `madePinnedAt` and the cut:
    `P5J.pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean) · `sendsAreB`:
    `P5J.sendsB_of_madeRow` (Johnson/P5J/FoldJ3.lean) at `P5J.madeRow_at_head` ·
    the head with the facts on reached states: `P5J.atMgR_madeRow` (Johnson/P5J/FoldJ3Whole.lean) at
    `P5J.startB_at_head` (Johnson/P5J/StartAtHead.lean).
  ITS PREMISES, WHOLE. (i) The head Hd; L₀'s three lists are the description's own. (ii) FOUR NAMED
      TESTS ON PUBLIC DATA: `tableWrittenB` · `linkPlanB` (at the 23) · `k5PlanB` (at 1;
      at attention's segments) · `headPlanB`; and "25 segments", "the output head's lookup has heard
          nothing". Of these `linkPlanB`, `k5PlanB`, `headPlanB` stand at the parameters `(dC
          Hd).pubD`, a noncomputable term that names the proof Hd. (iii) THREE TIMES "THE TYPE HAS A
              MEMBER", as in LastLine.lean.

Limits. THE FOUR ARE READ OFF THE HEAD's FIELD "the value is laid": that field stands over the proof
    file's list of fourteen entry tests, of which two are the two pins. The verifier asks these
        fourteen.
    That they accept at any files is not shown here; whether a value is laid at any public part
        under fourteen rows is not shown. WHAT THE HEAD HOLDS (`P5J.AtMgA`,
        Johnson/P5J/MgAtAll.lean): in scope · the files are read · the value is laid (over the proof
        file's fourteen entry tests) · the public part is the planner's · AND ELEVEN FURTHER
            CONDITIONS: the seven tests of `P5J.At.PlanOk` · headAt · cols13 · opts · k3. Which of
            them the verifier asks is not said here. THE
    PREMISES ARE NOT SHOWN TO HOLD TOGETHER: no example: the theorem may be idle. No soundness is
    claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.LastLine
import Johnson.P5J.StartAtHead
import Johnson.Goal.Skeleton.PinsOfLaid

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
/-- **The named condition**: `k2Cond_last` with four of its premises as calls; what stays: this
    file's head names it whole. -/
theorem k2Cond_head (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) (L₀ : P5J.Free numsFull Dw
                (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
                            = L₀.c₁ :: L₀.k₁) (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L₀.c₂ :: L₀.k₂) (q₃ :
                                                 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L₀.c₃ :: L₀.k₃) (hTW : tableWrittenB Z.pol Z.lay
                                                                      Z.KL = true) (h25 :
                                                                      Zp.s₀.check.frame.shape.link.length = 25) (hLP : ∀ m, m < 23 → linkPlanB Zp (dC Hd).pubD.nsOf
                                                                      (dC Hd).pubD.d3 (m + 1) = true) (hK1 : k5PlanB Zp (dC Hd).pubD.d5 Zp.first.layout 1 = true) (hK5
                                                                      : ∀ m, m < 23 → IM.subW (m + 1) = .attention → k5PlanB Zp (dC Hd).pubD.d5 Zp.first.layout (m +
                                                                      1) = true) (hHP : headPlanB Zp (dC Hd).pubD.nsOf (dC Hd).pubD.d3 = true) (hh : Zp.p.X.H.tl.heard
                                                                      = none) (hY : Nonempty (frC Dw).E.Str) (hI : ∀ {r : SwRow}, r ∈ tableFullLit → ∀ (h : r.ok =
                                                                      true) (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r
                                                                      (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
                                                                      (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
                                                                      h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent), Nonempty
                                                                      (TB (Letters.plain r (r.ok_says h)) iJ iQ) ∧ Nonempty ((Cb.Pv.SendLoc.stage (selZ (Letters.plain
                                                                      r (r.ok_says h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
                                                                      iQ).sw).Ex.Str)) :
    Hd.K2Cond L₀ := by
  have hp := P5J.pins_of_laid Hd.toAtMg.scope Hd.toAtMg.laid
  have hm := P5J.madeRow_at_head Hd.toAtMg
  have hSB : ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ → sendsAreB Zp.made.proof.1 358 (snAt
                  Zp G₀ IM.placesW) = true := by
    intro G₀ hG
    have h0 := P5J.sendsB_of_madeRow Hd.toAtMg hm G₀ hG
    rw [← P5J.placesW_at] at h0
    exact h0
  exact k2Cond_last Hd L₀ q₁ q₂ q₃ hp.1 hp.2 hSB hTW h25 hLP hK1 hK5 hHP hh (fun _ hl =>
      P5J.atMgR_madeRow Hd.toAtMg Hd.rchU (fun _ _ u => u.1.1) hl (P5J.startB_at_head Hd.toAtMg) hm)
      hY hI

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k2Cond_head
